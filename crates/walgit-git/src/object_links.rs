//! Raw Git links, independent of reachability accelerators and warm-cache state.
use std::collections::HashMap;

use gix_hash::ObjectId;
use gix_object::Kind;
use walgit_proto::v1::{PackRef, RefSnapshot};

use crate::{GitError, LocalRepo, ge};

/// Visit direct references without inflating blob payloads. Gitlinks name a
/// different repository and are deliberately excluded. Oversized metadata
/// refuses bounded maintenance before allocating its full decoded buffer.
pub fn visit_references(
    repo: &gix::Repository,
    id: ObjectId,
    max_object_bytes: u64,
    mut visit: impl FnMut(ObjectId, Kind) -> Result<(), GitError>,
) -> Result<(), GitError> {
    let header = repo.find_header(id).map_err(ge)?;
    if header.kind() == Kind::Blob {
        return Ok(());
    }
    if header.size() > max_object_bytes {
        return Err(GitError::InvalidInput(format!(
            "metadata object {id} exceeds the {max_object_bytes}-byte validation budget"
        )));
    }
    let object = repo.find_object(id).map_err(ge)?;
    match object.kind {
        Kind::Commit => {
            let commit =
                gix_object::CommitRef::from_bytes(&object.data, repo.object_hash()).map_err(ge)?;
            visit(commit.tree(), Kind::Tree)?;
            for parent in commit.parents() {
                visit(parent, Kind::Commit)?;
            }
        }
        Kind::Tree => {
            for entry in gix_object::TreeRefIter::from_bytes(&object.data, repo.object_hash()) {
                let entry = entry.map_err(ge)?;
                if !entry.mode.is_commit() {
                    visit(
                        entry.oid.to_owned(),
                        if entry.mode.is_tree() {
                            Kind::Tree
                        } else {
                            Kind::Blob
                        },
                    )?;
                }
            }
        }
        Kind::Tag => {
            let tag =
                gix_object::TagRef::from_bytes(&object.data, repo.object_hash()).map_err(ge)?;
            visit(tag.target(), tag.target_kind)?;
        }
        Kind::Blob => {}
    }
    Ok(())
}

/// Validate every indexed object, including unreachable commits/trees/tags.
/// The caller must supply an isolated ODB containing exactly captured committed
/// packs. Checking all direct edges there proves closure without a global walk
/// or an unbounded in-memory object set. Run on a blocking worker.
pub fn verify_indexed_links(
    local: &LocalRepo,
    packs: &[PackRef],
    refs: &RefSnapshot,
    max_object_bytes: u64,
) -> Result<(), GitError> {
    let mut repo = local.gix();
    repo.object_cache_size(
        usize::try_from((max_object_bytes / 4).min(64 * 1024 * 1024)).map_err(ge)?,
    );
    let mut kinds = HashMap::new();
    for pack in packs {
        let checksum = ObjectId::from_hex(pack.checksum.as_bytes()).map_err(ge)?;
        let index = gix_pack::index::File::at(
            local.pack_path(&checksum).with_extension("idx"),
            local.object_format().kind(),
        )
        .map_err(ge)?;
        for entry in index.iter() {
            visit_references(&repo, entry.oid, max_object_bytes, |target, expected| {
                let actual = if let Some(kind) = kinds.get(&target) {
                    *kind
                } else {
                    let kind = repo
                        .find_header(target)
                        .map_err(|error| {
                            GitError::InvalidInput(format!(
                                "indexed object {} references unavailable object {target}: {error}",
                                entry.oid
                            ))
                        })?
                        .kind();
                    if kinds.len() >= 4096 {
                        kinds.clear();
                    }
                    kinds.insert(target, kind);
                    kind
                };
                if actual != expected {
                    return Err(GitError::InvalidInput(format!(
                        "indexed object {} references {target} as {expected:?}, but found {actual:?}",
                        entry.oid
                    )));
                }
                Ok(())
            })?;
        }
    }
    for reference in &refs.refs {
        let id = ObjectId::from_hex(reference.oid.as_bytes()).map_err(ge)?;
        repo.find_header(id).map_err(ge)?;
    }
    Ok(())
}

/// Parse and verify the exact index identity before admitting it as membership evidence.
pub fn verified_index(
    path: &std::path::Path,
    pack: &PackRef,
    hash: gix_hash::Kind,
) -> Result<gix_pack::index::File, GitError> {
    let size = std::fs::metadata(path)?.len();
    if pack.idx_size != 0 && size != pack.idx_size {
        return Err(GitError::InvalidInput("pack index size mismatch".into()));
    }
    let index = gix_pack::index::File::at(path, hash).map_err(ge)?;
    index
        .verify_checksum(
            &mut gix_features::progress::Discard,
            &std::sync::atomic::AtomicBool::new(false),
        )
        .map_err(ge)?;
    if index.pack_checksum().to_string() != pack.checksum
        || (pack.object_count != 0 && u64::from(index.num_objects()) != pack.object_count)
    {
        return Err(GitError::InvalidInput(
            "pack index identity mismatch".into(),
        ));
    }
    Ok(index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};

    fn git(repo: &LocalRepo, args: &[&str], input: &str) -> anyhow::Result<String> {
        let mut child = Command::new("git")
            .arg("-C")
            .arg(repo.path())
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

    #[test]
    fn unreachable_indexed_links_cannot_hide_behind_empty_refs() -> anyhow::Result<()> {
        for format in [crate::ObjectFormat::Sha1, crate::ObjectFormat::Sha256] {
            let root = tempfile::tempdir()?;
            let repo = LocalRepo::init(root.path(), &crate::RepoId::new("o", "raw")?, format)?;
            let missing = "1".repeat(format.kind().len_in_hex());
            let commit = git(
                &repo,
                &[
                    "hash-object",
                    "--literally",
                    "-w",
                    "-t",
                    "commit",
                    "--stdin",
                ],
                &format!(
                    "tree {missing}\nauthor Test <test@example.invalid> 0 +0000\ncommitter Test <test@example.invalid> 0 +0000\n\nunreachable\n"
                ),
            )?;
            let prefix = repo.path().join("objects/pack/pack");
            let checksum = git(
                &repo,
                &["pack-objects", prefix.to_str().unwrap()],
                &format!("{commit}\n"),
            )?;
            repo.refresh()?;
            let result = verify_indexed_links(
                &repo,
                &[PackRef {
                    checksum,
                    ..Default::default()
                }],
                &RefSnapshot::default(),
                1024 * 1024,
            );
            assert!(
                result.is_err(),
                "unreachable broken input must not be conserved into a new cut"
            );
        }
        Ok(())
    }

    #[test]
    fn metadata_budget_is_checked_before_decode_and_blobs_have_no_links() -> anyhow::Result<()> {
        let root = tempfile::tempdir()?;
        let local = LocalRepo::init(
            root.path(),
            &crate::RepoId::new("o", "budget")?,
            crate::ObjectFormat::Sha1,
        )?;
        let blob = git(&local, &["hash-object", "-w", "--stdin"], &"x".repeat(4096))?;
        let tree = git(&local, &["mktree"], &format!("100644 blob {blob}\tfile\n"))?;
        local.refresh()?;
        let repo = local.gix();
        let blob = ObjectId::from_hex(blob.as_bytes())?;
        visit_references(&repo, blob, 1, |_, _| panic!("blob reference"))?;
        let tree = ObjectId::from_hex(tree.as_bytes())?;
        assert!(visit_references(&repo, tree, 1, |_, _| Ok(())).is_err());
        let mut edges = Vec::new();
        visit_references(&repo, tree, 1024, |oid, kind| {
            edges.push((oid, kind));
            Ok(())
        })?;
        assert_eq!(edges, vec![(blob, Kind::Blob)]);
        Ok(())
    }
}
