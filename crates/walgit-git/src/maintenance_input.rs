//! Attempt-owned maintenance repositories containing only captured committed inputs.
//!
//! Callers supply an owned reader pin covering the source files. It is moved into
//! the blocking task, so cancellation cannot release it while files are copied.
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::AtomicBool;

use walgit_proto::v1::{PackRef, RefSnapshot};

use crate::{GitError, LocalRepo, ObjectFormat, RepoId, ge};

pub struct MaintenanceInput {
    pub repo: LocalRepo,
    pub packs: Vec<PackRef>,
    pub refs: RefSnapshot,
    // Drop the repository handles before removing its attempt directory.
    attempt_dir: Option<tempfile::TempDir>,
    root: PathBuf,
    lock: std::fs::File,
}

impl Drop for MaintenanceInput {
    fn drop(&mut self) {
        // Explicit unlock also releases transient fork-inherited descriptors;
        // correctness must not wait for another thread's child to reach exec.
        let _ = self.lock.unlock();
    }
}

impl MaintenanceInput {
    /// Opt into reusable scratch. The caller owns cleanup; this is never durable
    /// repository state and may be deleted to restart from committed inputs.
    pub fn persist(&mut self) -> PathBuf {
        if let Some(attempt) = self.attempt_dir.take() {
            let _ = attempt.keep();
        }
        self.root.clone()
    }
    pub fn scratch_root(&self) -> &Path {
        &self.root
    }
}

/// Reopen disposable scratch only against caller-supplied captured authority.
/// Revalidates original pack bytes and rejects injected objects/alternates.
pub async fn reopen(
    root: PathBuf,
    packs: Vec<PackRef>,
    refs: RefSnapshot,
) -> Result<MaintenanceInput, GitError> {
    tokio::task::spawn_blocking(move || {
        let lock = lock_attempt(&root)?;
        walgit_proto::snapshot::validate(&refs)
            .map_err(|e| GitError::InvalidInput(e.to_string()))?;
        let repo = LocalRepo::open(&root, &RepoId::new("maintenance", "input")?)?
            .ok_or_else(|| GitError::InvalidInput("missing maintenance input".into()))?;
        if repo.object_format().as_str() != refs.object_format {
            return Err(GitError::InvalidInput(
                "scratch object format mismatch".into(),
            ));
        }
        let mut expected = HashSet::new();
        for pack in &packs {
            let oid = gix_hash::ObjectId::from_hex(pack.checksum.as_bytes()).map_err(ge)?;
            if oid.kind() != repo.object_format().kind() || oid.to_string() != pack.checksum {
                return Err(GitError::InvalidInput(
                    "invalid scratch pack checksum".into(),
                ));
            }
            for (ext, required) in [
                ("pack", true),
                ("idx", true),
                ("rev", pack.has_rev),
                ("bitmap", pack.has_bitmap),
                ("commit-graph", pack.has_commit_graph),
            ] {
                if required && !expected.insert(format!("pack-{}.{ext}", pack.checksum)) {
                    return Err(GitError::InvalidInput("duplicate scratch pack".into()));
                }
            }
            verify(&repo, pack, repo.object_format())?;
        }
        let objects = repo.path().join("objects");
        for entry in std::fs::read_dir(&objects)? {
            let entry = entry?;
            if entry.file_name() != "pack" && entry.file_name() != "info" {
                return Err(GitError::InvalidInput(
                    "unexpected loose scratch objects".into(),
                ));
            }
        }
        for entry in std::fs::read_dir(objects.join("pack"))? {
            let entry = entry?;
            if !entry.file_type()?.is_file()
                || !expected.remove(&entry.file_name().to_string_lossy().into_owned())
            {
                return Err(GitError::InvalidInput(
                    "unexpected scratch pack file".into(),
                ));
            }
        }
        if !expected.is_empty() || std::fs::read_dir(objects.join("info"))?.next().is_some() {
            return Err(GitError::InvalidInput(
                "incomplete scratch files or unexpected object info".into(),
            ));
        }
        repo.load_ref_snapshot(&refs)?;
        repo.refresh()?;
        Ok(MaintenanceInput {
            repo,
            packs,
            refs,
            root,
            attempt_dir: None,
            lock,
        })
    })
    .await
    .map_err(ge)?
}

fn lock_attempt(root: &Path) -> Result<std::fs::File, GitError> {
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(root.join(".lock"))?;
    file.try_lock()
        .map_err(|e| GitError::InvalidInput(format!("maintenance attempt is busy: {e}")))?;
    Ok(file)
}

/// Build and verify an isolated input ODB on a blocking worker. `source` is the
/// bare repository directory. No loose objects, alternates, MIDX, or uncommitted
/// packs from that directory enter the attempt. Scratch is disposable progress.
pub async fn prepare<P: Send + 'static>(
    source: PathBuf,
    scratch_parent: PathBuf,
    packs: Vec<PackRef>,
    refs: RefSnapshot,
    reader_pin: P,
) -> Result<MaintenanceInput, GitError> {
    tokio::task::spawn_blocking(move || {
        let _pin = reader_pin;
        prepare_blocking(&source, &scratch_parent, packs, refs)
    })
    .await
    .map_err(ge)?
}

fn prepare_blocking(
    source: &Path,
    scratch_parent: &Path,
    packs: Vec<PackRef>,
    refs: RefSnapshot,
) -> Result<MaintenanceInput, GitError> {
    walgit_proto::snapshot::validate(&refs).map_err(|e| GitError::InvalidInput(e.to_string()))?;
    let format = match refs.object_format.as_str() {
        "sha1" => ObjectFormat::Sha1,
        "sha256" => ObjectFormat::Sha256,
        _ => unreachable!("validated snapshot"),
    };
    let mut seen = HashSet::new();
    for pack in &packs {
        if pack.checksum.len() != format.kind().len_in_hex()
            || !pack
                .checksum
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || !seen.insert(&pack.checksum)
        {
            return Err(GitError::InvalidInput(
                "invalid or duplicate committed pack checksum".into(),
            ));
        }
    }
    std::fs::create_dir_all(scratch_parent)?;
    let attempt = tempfile::Builder::new()
        .prefix("maintenance-input-")
        .tempdir_in(scratch_parent)?;
    let lock = lock_attempt(attempt.path())?;
    let repo = LocalRepo::init(
        attempt.path(),
        &RepoId::new("maintenance", "input")?,
        format,
    )?;
    for descriptor in &packs {
        let name = format!("pack-{}", descriptor.checksum);
        for (ext, required) in [
            ("pack", true),
            ("idx", true),
            ("rev", descriptor.has_rev),
            ("bitmap", descriptor.has_bitmap),
            ("commit-graph", descriptor.has_commit_graph),
        ] {
            if !required {
                continue;
            }
            let from = source.join("objects/pack").join(format!("{name}.{ext}"));
            // Copy, rather than hard-link, so subsequent scratch tools cannot
            // mutate serving inodes, including side files.
            if !std::fs::metadata(&from)?.is_file() {
                return Err(GitError::InvalidInput(
                    "committed input is not a file".into(),
                ));
            }
            std::fs::copy(
                from,
                repo.path()
                    .join("objects/pack")
                    .join(format!("{name}.{ext}")),
            )?;
        }
        verify(&repo, descriptor, format)?;
    }
    repo.load_ref_snapshot(&refs)?;
    repo.refresh()?;
    Ok(MaintenanceInput {
        repo,
        packs,
        refs,
        root: attempt.path().to_path_buf(),
        attempt_dir: Some(attempt),
        lock,
    })
}

pub(crate) fn verify(
    repo: &LocalRepo,
    expected: &PackRef,
    format: ObjectFormat,
) -> Result<(), GitError> {
    let path = repo
        .path()
        .join("objects/pack")
        .join(format!("pack-{}.pack", expected.checksum));
    let idx_path = path.with_extension("idx");
    if std::fs::metadata(&path)?.len() != expected.pack_size
        || std::fs::metadata(&idx_path)?.len() != expected.idx_size
    {
        return Err(GitError::InvalidInput(
            "committed pack/index size mismatch".into(),
        ));
    }
    let index = gix_pack::index::File::at(&idx_path, format.kind()).map_err(ge)?;
    let pack = gix_pack::data::File::at(&path, format.kind()).map_err(ge)?;
    let stop = AtomicBool::new(false);
    let mut progress = gix_features::progress::Discard;
    index.verify_checksum(&mut progress, &stop).map_err(ge)?;
    let actual = pack.verify_checksum(&mut progress, &stop).map_err(ge)?;
    if actual.to_string() != expected.checksum
        || index.pack_checksum() != actual
        || u64::from(index.num_objects()) != expected.object_count
        || index.num_objects() != pack.num_objects()
    {
        return Err(GitError::InvalidInput(
            "committed pack/index inventory mismatch".into(),
        ));
    }
    // Git verifies every index entry against the decoded object, including CRCs
    // and delta dependencies. No verbose object inventory is collected in RAM.
    let output = Command::new("git")
        .arg("-C")
        .arg(repo.path())
        .args(["verify-pack"])
        .arg(&idx_path)
        .stdout(Stdio::null())
        .output()?;
    if !output.status.success() {
        return Err(GitError::Subprocess {
            cmd: "git verify-pack".into(),
            status: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn git(repo: &LocalRepo, args: &[&str], input: &str) -> String {
        let mut child = Command::new("git")
            .arg("-C")
            .arg(repo.path())
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(input.as_bytes())
            .unwrap();
        let out = child.wait_with_output().unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap().trim().to_owned()
    }

    fn add_pack(repo: &LocalRepo, text: &str) -> (PackRef, String) {
        let oid = git(repo, &["hash-object", "-w", "--stdin"], text);
        let prefix = repo.path().join("objects/pack/pack");
        let checksum = git(
            repo,
            &["pack-objects", prefix.to_str().unwrap()],
            &format!("{oid}\n"),
        );
        let path = prefix.with_file_name(format!("pack-{checksum}.pack"));
        (
            PackRef {
                checksum,
                pack_size: std::fs::metadata(&path).unwrap().len(),
                idx_size: std::fs::metadata(path.with_extension("idx")).unwrap().len(),
                object_count: 1,
                ..Default::default()
            },
            oid,
        )
    }

    #[tokio::test]
    async fn exact_inventory_conserves_unreachable_objects_and_excludes_uncommitted_inputs() {
        for format in [ObjectFormat::Sha1, ObjectFormat::Sha256] {
            let root = tempfile::tempdir().unwrap();
            let source =
                LocalRepo::init(root.path(), &RepoId::new("test", "source").unwrap(), format)
                    .unwrap();
            let (committed, oid) = add_pack(&source, "committed unreachable blob");
            let (extra, _) = add_pack(&source, "uncommitted blob");
            let snap = RefSnapshot {
                object_format: format.as_str().into(),
                head_target: "refs/heads/main".into(),
                ..Default::default()
            };
            let input = prepare(
                source.path().to_path_buf(),
                root.path().join("scratch"),
                vec![committed.clone()],
                snap.clone(),
                (),
            )
            .await
            .unwrap();
            assert_eq!(input.packs, vec![committed]);
            assert_eq!(input.refs, snap);
            assert_eq!(
                git(&input.repo, &["cat-file", "blob", &oid], ""),
                "committed unreachable blob"
            );
            let pack_dir = input.repo.path().join("objects/pack");
            assert_eq!(std::fs::read_dir(&pack_dir).unwrap().count(), 2);
            assert!(
                !pack_dir
                    .join(format!("pack-{}.pack", extra.checksum))
                    .exists()
            );
            assert!(!input.repo.path().join("objects/info/alternates").exists());
            let path = input.repo.path().to_path_buf();
            drop(input);
            assert!(!path.exists());
            assert!(source.path().exists());
        }
    }

    #[tokio::test]
    async fn missing_corrupt_or_mismatched_committed_inputs_fail_closed() {
        let root = tempfile::tempdir().unwrap();
        let source = LocalRepo::init(
            root.path(),
            &RepoId::new("test", "source").unwrap(),
            ObjectFormat::Sha1,
        )
        .unwrap();
        let (pack, _) = add_pack(&source, "committed blob");
        let snapshot = RefSnapshot {
            object_format: "sha1".into(),
            ..Default::default()
        };
        let mut cases = Vec::new();
        let mut bad = pack.clone();
        bad.checksum = "../escape".into();
        cases.push(bad);
        let mut bad = pack.clone();
        bad.object_count += 1;
        cases.push(bad);
        let mut bad = pack.clone();
        bad.has_bitmap = true;
        cases.push(bad);
        for bad in cases {
            assert!(
                prepare(
                    source.path().to_path_buf(),
                    root.path().join("scratch"),
                    vec![bad],
                    snapshot.clone(),
                    ()
                )
                .await
                .is_err()
            );
        }
        let path = source
            .path()
            .join("objects/pack")
            .join(format!("pack-{}.pack", pack.checksum));
        let mut bytes = std::fs::read(&path).unwrap();
        bytes[12] ^= 1;
        std::fs::remove_file(&path).unwrap();
        std::fs::write(path, bytes).unwrap();
        assert!(
            prepare(
                source.path().to_path_buf(),
                root.path().join("scratch"),
                vec![pack],
                snapshot,
                ()
            )
            .await
            .is_err()
        );
    }
}
