//! Validated immutable indexes. A cross-process lock protects names while they
//! are opened/replaced; returned mappings own their bytes across later unlinks.
use std::path::{Path, PathBuf};
use std::sync::Arc;

use walgit_proto::v1::PackRef;
use walgit_store::Prefixed;

use crate::{WalError, progress::Reporter};

struct CacheLock(std::fs::File);
impl Drop for CacheLock {
    fn drop(&mut self) {
        let _ = self.0.unlock();
    }
}

async fn lock(dir: &Path, reporter: &Reporter) -> Result<Arc<CacheLock>, WalError> {
    tokio::fs::create_dir_all(dir).await?;
    let file = tokio::fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(dir.join(".index-cache.lock"))
        .await?
        .into_std()
        .await;
    let start = tokio::time::Instant::now();
    let mut narrated = false;
    loop {
        match file.try_lock() {
            Ok(()) => return Ok(Arc::new(CacheLock(file))),
            Err(std::fs::TryLockError::WouldBlock) => {
                if !narrated {
                    reporter.notice("Waiting for another index-cache operation");
                    narrated = true;
                }
                if start.elapsed() >= std::time::Duration::from_secs(30) {
                    return Err(WalError::Io(std::io::Error::new(
                        std::io::ErrorKind::WouldBlock,
                        "index cache busy; retry",
                    )));
                }
                tokio::time::sleep(std::time::Duration::from_millis(25)).await;
            }
            Err(std::fs::TryLockError::Error(error)) => return Err(error.into()),
        }
    }
}

fn validate(
    path: &Path,
    pack: &PackRef,
    hash: gix_hash::Kind,
) -> Result<gix_pack::index::File, WalError> {
    walgit_git::object_links::verified_index(path, pack, hash).map_err(WalError::from)
}

async fn one(
    store: Prefixed,
    repo: PathBuf,
    pack: PackRef,
    hash: gix_hash::Kind,
    guard: Arc<CacheLock>,
) -> Result<(PackRef, gix_pack::index::File), WalError> {
    let dir = crate::remote::idx_dir(&repo);
    let dest = dir.join(format!("{}.idx", pack.checksum));
    let reuse = tokio::task::spawn_blocking({
        let guard = guard.clone();
        let pack = pack.clone();
        let dest = dest.clone();
        let dir = dir.clone();
        move || -> Result<Option<gix_pack::index::File>, WalError> {
            let _guard = guard;
            if let Ok(index) = validate(&dest, &pack, hash) {
                return Ok(Some(index));
            }
            let installed = repo
                .join("objects/pack")
                .join(format!("pack-{}.idx", pack.checksum));
            if validate(&installed, &pack, hash).is_ok() {
                let temp = tempfile::Builder::new()
                    .prefix(".index-")
                    .suffix(".tmp")
                    .tempfile_in(&dir)?
                    .into_temp_path();
                std::fs::remove_file(&temp)?;
                if std::fs::hard_link(&installed, &temp).is_err() {
                    std::fs::copy(&installed, &temp)?;
                }
                let index = validate(&temp, &pack, hash)?;
                std::fs::rename(&temp, &dest)?;
                return Ok(Some(index));
            }
            Ok(None)
        }
    })
    .await
    .map_err(|e| WalError::Corrupt(e.to_string()))??;
    if let Some(index) = reuse {
        return Ok((pack, index));
    }
    let temp = tokio::task::spawn_blocking({
        let dir = dir.clone();
        let guard = guard.clone();
        move || {
            let _guard = guard;
            tempfile::Builder::new()
                .prefix(".index-")
                .suffix(".tmp")
                .tempfile_in(dir)
                .map(tempfile::NamedTempFile::into_temp_path)
        }
    })
    .await
    .map_err(|e| WalError::Corrupt(e.to_string()))??;
    crate::sync::download_object(
        &store,
        &walgit_proto::keys::idx_key(&pack.checksum),
        &temp,
        (pack.idx_size != 0).then_some(pack.idx_size),
        None,
    )
    .await?;
    tokio::task::spawn_blocking(move || {
        let _guard = guard;
        let index = validate(&temp, &pack, hash)?;
        std::fs::rename(&temp, dest)?;
        Ok((pack, index))
    })
    .await
    .map_err(|e| WalError::Corrupt(e.to_string()))?
}

/// Cold downloads run four at a time; cancellation aborts siblings. Temp names
/// are attempt-owned, never shared truncation targets. The lock's kernel lifetime
/// permits a successor to reclaim crash residue without an age or PID guess.
pub(crate) async fn load(
    store: &Prefixed,
    repo: &Path,
    packs: &[PackRef],
    retained: &[PackRef],
    hash: gix_hash::Kind,
    reporter: &Reporter,
) -> Result<Vec<(PackRef, gix_pack::index::File)>, WalError> {
    let dir = crate::remote::idx_dir(repo);
    let guard = lock(&dir, reporter).await?;
    let mut names = tokio::fs::read_dir(&dir).await?;
    while let Some(entry) = names.next_entry().await? {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with(".index-") && name.ends_with(".tmp") {
            tokio::fs::remove_file(entry.path()).await?;
        }
    }
    let mut pending = packs.iter();
    let mut tasks = tokio::task::JoinSet::new();
    let mut loaded = Vec::with_capacity(packs.len());
    loop {
        while tasks.len() < 4 {
            let Some(pack) = pending.next() else {
                break;
            };
            tasks.spawn(one(
                store.clone(),
                repo.to_owned(),
                pack.clone(),
                hash,
                guard.clone(),
            ));
        }
        let Some(result) = tasks.join_next().await else {
            break;
        };
        loaded.push(result.map_err(|e| WalError::Corrupt(e.to_string()))??);
        reporter.bar(
            "Validating pack indexes",
            loaded.len() as u64,
            Some(packs.len() as u64),
            "indexes",
        );
    }
    // Every opener and cached-name borrower holds the same lock. Existing readers
    // own mmap snapshots; no active operation retains an unopened cache name.
    let live: std::collections::HashSet<_> = retained.iter().map(|p| p.checksum.as_str()).collect();
    let mut names = tokio::fs::read_dir(&dir).await?;
    while let Some(entry) = names.next_entry().await? {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if let Some(checksum) = name.strip_suffix(".idx")
            && !live.contains(checksum)
        {
            tokio::fs::remove_file(entry.path()).await?;
        }
    }
    Ok(loaded)
}

/// Borrow a cached name only while locked, validate it, and create the caller's
/// independent link before yielding. Used by mount-based pack installation.
pub(crate) async fn reuse(
    repo: &Path,
    pack: &PackRef,
    hash: gix_hash::Kind,
    dest: PathBuf,
    reporter: &Reporter,
) -> Result<bool, WalError> {
    let dir = crate::remote::idx_dir(repo);
    let guard = lock(&dir, reporter).await?;
    let pack = pack.clone();
    tokio::task::spawn_blocking(move || {
        let _guard = guard;
        let source = dir.join(format!("{}.idx", pack.checksum));
        if validate(&source, &pack, hash).is_err() {
            return Ok(false);
        }
        if std::fs::hard_link(&source, &dest).is_err() {
            std::fs::copy(&source, &dest)?;
        }
        Ok(true)
    })
    .await
    .map_err(|e| WalError::Corrupt(e.to_string()))?
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};
    use walgit_store::{ObjectStoreExt, PutMode, memory::MemoryStore};

    fn git(dir: &Path, args: &[&str], input: &str) -> anyhow::Result<String> {
        let mut child = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        child
            .stdin
            .take()
            .ok_or_else(|| anyhow::anyhow!("missing stdin"))?
            .write_all(input.as_bytes())?;
        let output = child.wait_with_output()?;
        anyhow::ensure!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        Ok(String::from_utf8(output.stdout)?.trim().to_owned())
    }

    #[tokio::test]
    async fn repairs_corrupt_and_wrong_identity_indexes_and_pins_old_readers() -> anyhow::Result<()>
    {
        for format in ["sha1", "sha256"] {
            let root = tempfile::tempdir()?;
            git(
                root.path(),
                &["init", "--bare", &format!("--object-format={format}")],
                "",
            )?;
            let hash = if format == "sha1" {
                gix_hash::Kind::Sha1
            } else {
                gix_hash::Kind::Sha256
            };
            let mut fixtures = Vec::new();
            for content in ["first", "second"] {
                let oid = git(root.path(), &["hash-object", "-w", "--stdin"], content)?;
                let checksum = git(
                    root.path(),
                    &["pack-objects", "objects/pack/pack"],
                    &format!("{oid}\n"),
                )?;
                let installed = root
                    .path()
                    .join(format!("objects/pack/pack-{checksum}.idx"));
                let bytes = std::fs::read(&installed)?;
                fixtures.push((
                    PackRef {
                        checksum,
                        idx_size: bytes.len() as u64,
                        object_count: 1,
                        ..Default::default()
                    },
                    bytes,
                    installed,
                    oid,
                ));
            }
            let store = MemoryStore::shared();
            let prefixed = Prefixed::new(store.clone(), "p/");
            for (pack, bytes, _, _) in &fixtures {
                store
                    .put_bytes(
                        &format!("p/{}", walgit_proto::keys::idx_key(&pack.checksum)),
                        bytes.clone(),
                        PutMode::Create,
                    )
                    .await?;
            }
            let (pack, bytes, installed, oid) = &fixtures[0];
            let dir = crate::remote::idx_dir(root.path());
            std::fs::create_dir_all(&dir)?;
            let cached = dir.join(format!("{}.idx", pack.checksum));
            std::fs::hard_link(installed, &cached)?;
            // Both names point at a damaged inode. Repair must replace it, not
            // trust the installed alias or rewrite a mapping another reader owns.
            std::fs::set_permissions(
                installed,
                std::os::unix::fs::PermissionsExt::from_mode(0o600),
            )?;
            std::fs::write(installed, b"truncated")?;
            std::fs::write(dir.join(".index-abandoned.tmp"), b"crash residue")?;
            let reporter = Reporter::none();
            let loaded = load(
                &prefixed,
                root.path(),
                std::slice::from_ref(pack),
                std::slice::from_ref(pack),
                hash,
                &reporter,
            )
            .await?;
            let object = gix_hash::ObjectId::from_hex(oid.as_bytes())?;
            assert!(loaded[0].1.lookup(object).is_some());
            assert_eq!(std::fs::read(&cached)?, *bytes);
            assert_eq!(std::fs::read(installed)?, b"truncated");
            assert!(!dir.join(".index-abandoned.tmp").exists());
            // A structurally valid index for another pack is not evidence.
            std::fs::remove_file(&cached)?;
            std::fs::write(&cached, &fixtures[1].1)?;
            let repaired = load(
                &prefixed,
                root.path(),
                std::slice::from_ref(pack),
                std::slice::from_ref(pack),
                hash,
                &reporter,
            )
            .await?;
            assert!(repaired[0].1.lookup(object).is_some());
            load(&prefixed, root.path(), &[], &[], hash, &reporter).await?;
            assert!(!cached.exists());
            assert!(loaded[0].1.lookup(object).is_some());
            assert!(repaired[0].1.lookup(object).is_some());
        }
        Ok(())
    }

    // Invoked only in a disposable child process by the crash regression.
    #[test]
    fn child_index_cache_owner() -> anyhow::Result<()> {
        let Some(dir) = std::env::var_os("WALGIT_TEST_INDEX_LOCK_ROOT") else {
            return Ok(());
        };
        let dir = PathBuf::from(dir);
        let file = std::fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(dir.join(".index-cache.lock"))?;
        file.try_lock()?;
        std::fs::write(dir.join(".index-child.tmp"), b"in progress")?;
        std::fs::write(dir.join("child-ready"), b"ready")?;
        loop {
            std::thread::park();
        }
    }

    #[tokio::test]
    async fn killed_process_releases_ownership_before_residue_reclaim() -> anyhow::Result<()> {
        struct ChildOwner(std::process::Child);
        impl Drop for ChildOwner {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        let root = tempfile::tempdir()?;
        let dir = crate::remote::idx_dir(root.path());
        std::fs::create_dir_all(&dir)?;
        let mut child = ChildOwner(
            Command::new(std::env::current_exe()?)
                .args([
                    "--exact",
                    "index_cache::tests::child_index_cache_owner",
                    "--nocapture",
                ])
                .env("WALGIT_TEST_INDEX_LOCK_ROOT", &dir)
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()?,
        );
        tokio::time::timeout(std::time::Duration::from_secs(5), async {
            while !dir.join("child-ready").exists() {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            }
        })
        .await?;
        let contender = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(dir.join(".index-cache.lock"))?;
        assert!(matches!(
            contender.try_lock(),
            Err(std::fs::TryLockError::WouldBlock)
        ));
        assert!(dir.join(".index-child.tmp").exists());
        child.0.kill()?;
        child.0.wait()?;
        let store = Prefixed::new(MemoryStore::shared(), "p/");
        load(
            &store,
            root.path(),
            &[],
            &[],
            gix_hash::Kind::Sha1,
            &Reporter::none(),
        )
        .await?;
        assert!(!dir.join(".index-child.tmp").exists());
        Ok(())
    }

    #[tokio::test]
    async fn blocking_owner_keeps_lock_after_request_cancellation() -> anyhow::Result<()> {
        let dir = tempfile::tempdir()?;
        let guard = lock(dir.path(), &Reporter::none()).await?;
        let worker_guard = guard.clone();
        let (started_tx, started_rx) = tokio::sync::oneshot::channel();
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let worker = tokio::task::spawn_blocking(move || {
            let _guard = worker_guard;
            let _ = started_tx.send(());
            release_rx.recv()
        });
        started_rx.await?;
        drop(guard);
        worker.abort();
        let contender = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(dir.path().join(".index-cache.lock"))?;
        assert!(matches!(
            contender.try_lock(),
            Err(std::fs::TryLockError::WouldBlock)
        ));
        release_tx.send(())?;
        worker.await??;
        contender.try_lock()?;
        contender.unlock()?;
        Ok(())
    }
}
