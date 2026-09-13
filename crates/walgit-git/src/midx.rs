//! Verified multi-pack bitmaps for a complete installed pack inventory.
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::{GitError, LocalRepo, ObjectId, ge};

#[derive(Debug)]
pub struct VerifiedMidx {
    pub checksum: ObjectId,
    pub bitmap_path: PathBuf,
}

fn checked(command: &mut Command, input: Option<&[u8]>) -> Result<(), GitError> {
    let description = format!("{command:?}");
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(input) = input {
        child
            .stdin
            .take()
            .ok_or_else(|| std::io::Error::other("missing git stdin"))?
            .write_all(input)?;
    } else {
        drop(child.stdin.take());
    }
    let output = child.wait_with_output()?;
    if !output.status.success() {
        return Err(GitError::Subprocess {
            cmd: description,
            status: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    Ok(())
}

fn file_digest(path: &Path, kind: gix_hash::Kind) -> Result<ObjectId, GitError> {
    let mut file = std::fs::File::open(path)?;
    let size = file.metadata()?.len();
    let hash_len = kind.len_in_bytes();
    let payload = size
        .checked_sub(hash_len as u64)
        .ok_or_else(|| GitError::InvalidInput("truncated index checksum".into()))?;
    let mut hashing = gix_hash::io::Write::new(std::io::sink(), kind);
    if std::io::copy(&mut (&mut file).take(payload), &mut hashing)? != payload {
        return Err(GitError::InvalidInput("truncated index contents".into()));
    }
    let digest = hashing.hash.try_finalize().map_err(ge)?;
    file.seek(SeekFrom::Start(payload))?;
    let mut trailer = vec![0; hash_len];
    file.read_exact(&mut trailer)?;
    if digest.as_bytes() != trailer {
        return Err(GitError::InvalidInput("index checksum mismatch".into()));
    }
    Ok(digest)
}

/// Check the exact MIDX and its named bitmap, including both file digests and
/// bitmap-to-MIDX linkage. Existence or a successful Git write is insufficient.
pub fn verify_files(repo: &LocalRepo) -> Result<VerifiedMidx, GitError> {
    let dir = repo.path().join("objects/pack");
    let kind = repo.object_format().kind();
    let index_path = dir.join("multi-pack-index");
    let checksum = file_digest(&index_path, kind)?;
    let mut index_header = [0; 8];
    std::fs::File::open(&index_path)?.read_exact(&mut index_header)?;
    let hash_id = match kind {
        gix_hash::Kind::Sha1 => 1,
        gix_hash::Kind::Sha256 => 2,
        _ => {
            return Err(GitError::InvalidInput(
                "unsupported bitmap object format".into(),
            ));
        }
    };
    if index_header.get(..4) != Some(b"MIDX".as_slice())
        || index_header.get(4) != Some(&1)
        || index_header.get(5) != Some(&hash_id)
    {
        return Err(GitError::InvalidInput(
            "unsupported MIDX header or object format".into(),
        ));
    }
    let bitmap_path = dir.join(format!("multi-pack-index-{checksum}.bitmap"));
    file_digest(&bitmap_path, kind)?;
    let mut file = std::fs::File::open(&bitmap_path)?;
    let mut header = [0; 12];
    file.read_exact(&mut header)?;
    if header.get(..6) != Some(b"BITM\0\x01".as_slice()) || header.get(8..12) == Some(&[0; 4]) {
        return Err(GitError::InvalidInput(
            "missing supported nonempty MIDX bitmap".into(),
        ));
    }
    let mut mapping = vec![0; kind.len_in_bytes()];
    file.read_exact(&mut mapping)?;
    if checksum.as_bytes() != mapping {
        return Err(GitError::InvalidInput(
            "bitmap belongs to another MIDX".into(),
        ));
    }
    Ok(VerifiedMidx {
        checksum,
        bitmap_path,
    })
}

impl LocalRepo {
    /// In-memory cache mode, restored from the manifest on every reconciliation.
    /// It prevents older derived-history maintenance from replacing a full MIDX.
    pub fn set_segmented_midx_mode(&self, enabled: bool) {
        self.inner
            .segmented_midx
            .store(enabled, std::sync::atomic::Ordering::Release);
    }

    /// Drop disposable indexes before removing an indexed pack or switching to
    /// remote-only data. Caller excludes readers and runs off the async runtime.
    pub fn invalidate_midx(&self) -> Result<(), GitError> {
        let dir = self.path().join("objects/pack");
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if name == "multi-pack-index"
                || (name.starts_with("multi-pack-index-")
                    && (name.ends_with(".bitmap") || name.ends_with(".rev")))
            {
                match std::fs::remove_file(entry.path()) {
                    Ok(()) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                    Err(e) => return Err(e.into()),
                }
            }
        }
        Ok(())
    }

    /// Build over exactly these installed packs, then check file hashes, Git's
    /// index verification, and a real bitmap graph walk at the captured commit.
    /// The owned pin moves into the worker so cancellation cannot unpin live
    /// files while Git still reads them. Isolated scratch callers can pass `()`.
    pub async fn write_verified_midx<P: Send + 'static>(
        &self,
        packs: &[ObjectId],
        commit: ObjectId,
        pin: P,
    ) -> Result<VerifiedMidx, GitError> {
        let repo = self.clone();
        let packs = packs.to_vec();
        tokio::task::spawn_blocking(move || {
            let _pin = pin;
            if packs.is_empty()
                || commit.kind() != repo.object_format().kind()
                || packs.iter().any(|p| p.kind() != commit.kind())
            {
                return Err(GitError::InvalidInput(
                    "invalid bitmap inventory or commit format".into(),
                ));
            }
            let mut names: Vec<_> = packs.iter().map(|id| format!("pack-{id}.idx")).collect();
            names.sort();
            names.dedup();
            for id in &packs {
                if !repo.pack_path(id).is_file()
                    || !repo.pack_path(id).with_extension("idx").is_file()
                {
                    return Err(GitError::InvalidInput(
                        "bitmap requires every selected pack locally readable".into(),
                    ));
                }
            }
            let input = format!("{}\n", names.join("\n"));
            checked(
                Command::new("git").arg("-C").arg(repo.path()).args([
                    "multi-pack-index",
                    "write",
                    "--bitmap",
                    "--stdin-packs",
                ]),
                Some(input.as_bytes()),
            )?;
            let verified = verify_files(&repo)?;
            checked(
                Command::new("git")
                    .arg("-C")
                    .arg(repo.path())
                    .args(["multi-pack-index", "verify"]),
                None,
            )?;
            checked(
                Command::new("git").arg("-C").arg(repo.path()).args([
                    "rev-list",
                    "--test-bitmap",
                    &commit.to_string(),
                ]),
                None,
            )?;
            checked(
                Command::new("git").arg("-C").arg(repo.path()).args([
                    "config",
                    "pack.allowPackReuse",
                    "multi",
                ]),
                None,
            )?;
            repo.refresh()?;
            Ok(verified)
        })
        .await
        .map_err(|e| GitError::Protocol(format!("bitmap task: {e}")))?
    }
}
