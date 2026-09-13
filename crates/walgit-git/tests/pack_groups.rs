#![allow(clippy::unwrap_used, clippy::indexing_slicing)]
#[path = "common/mod.rs"]
mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::process::{Command, Stdio};
use walgit_config::{PackGroupConfig, PackGroupKind, RefsConfig};
use walgit_git::{Ref, RefSnapshotData, pack_groups::resolve_groups};

#[test]
fn dependency_packs_reconstruct_captured_tags_without_metadata() {
    let source = common::SourceRepo::new();
    let a = source.head();
    let b = source.commit_file("nested/file", "second", "second");
    let c = source.commit_file("nested/file", "third", "third");
    let tag = source.annotated_tag("release", &c);
    let meta = source.commit_file("metadata-only", "not code", "metadata");
    let snapshot = RefSnapshotData {
        refs: [
            ("refs/heads/base", a),
            ("refs/heads/middle", b),
            ("refs/tags/release", tag.clone()),
            ("refs/meta/state", meta.clone()),
        ]
        .into_iter()
        .map(|(name, oid)| Ref {
            name: name.into(),
            oid,
            peeled: String::new(),
        })
        .collect(),
        head_target: "refs/heads/base".into(),
    };
    let group = |include: &str, subtract: &[&str]| PackGroupConfig {
        kind: PackGroupKind::Code,
        include: vec![include.into()],
        subtract: subtract.iter().map(|s| (*s).into()).collect(),
    };
    let mut config = RefsConfig {
        advertise: vec![],
        packfiles: BTreeMap::from([
            ("base".into(), group("HEAD", &[])),
            ("middle".into(), group("refs/heads/middle", &["base"])),
            ("release".into(), group("refs/tags/*", &["middle"])),
        ]),
    };
    let groups = resolve_groups(&config, &snapshot).unwrap();
    assert_eq!(groups["release"].dependencies, ["base", "middle"]);
    config.advertise = vec!["refs/meta/*".into()];
    assert_eq!(groups, resolve_groups(&config, &snapshot).unwrap());
    let target = common::fresh_bare();
    for name in ["base", "middle", "release"] {
        let roots = &groups[name];
        let bytes = source.pack(
            &roots.include.iter().map(String::as_str).collect::<Vec<_>>(),
            &roots.exclude.iter().map(String::as_str).collect::<Vec<_>>(),
            false,
        );
        let mut child = Command::new("git")
            .current_dir(target.path())
            .args(["index-pack", "--stdin"])
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(&bytes).unwrap();
        assert!(child.wait().unwrap().success());
    }
    common::run_git(target.path(), &["update-ref", "refs/tags/release", &tag]);
    common::run_git(target.path(), &["fsck", "--strict"]);
    let inventory = |dir: &std::path::Path, rev: &str| -> BTreeSet<String> {
        common::run_git(dir, &["rev-list", "--objects", rev])
            .lines()
            .map(|line| line.split_whitespace().next().unwrap().to_owned())
            .collect()
    };
    assert_eq!(inventory(target.path(), &tag), inventory(&source.dir, &tag));
    assert!(
        !Command::new("git")
            .current_dir(target.path())
            .args(["cat-file", "-e", &meta])
            .stderr(Stdio::null())
            .status()
            .unwrap()
            .success()
    );
}
