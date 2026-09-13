//! Coverage producers must never broaden a saved policy after a host config change.
use std::sync::Arc;

use walgit_config::{Config, PackGroupConfig, PackGroupKind};
use walgit_git::{ObjectFormat, RepoId};
use walgit_wal::Registry;

#[tokio::test]
async fn invalid_saved_dependency_cannot_fall_back_to_broader_host_policy() {
    let store = walgit_store::memory::MemoryStore::shared();
    let old_cache = tempfile::tempdir().unwrap();
    let new_cache = tempfile::tempdir().unwrap();
    let mut old_config = Config::default();
    old_config.cache.dir = old_cache.path().to_path_buf();
    old_config.refs.packfiles.insert(
        "base".into(),
        PackGroupConfig {
            kind: PackGroupKind::Code,
            include: vec!["refs/heads/main".into()],
            subtract: vec![],
        },
    );
    old_config.validate().unwrap();
    let id = RepoId::new("test", "policy-transition").unwrap();
    let old = Registry::new(store.clone(), Arc::new(old_config));
    let handle = old.create(&id, ObjectFormat::Sha1).await.unwrap();
    let settings = "[refs]\nadvertise = [\"refs/heads/release\"]\n[refs.packfiles.code]\ninclude = [\"refs/heads/release\"]\nsubtract = [\"base\"]\n";
    handle
        .publish_settings(settings, "operator", "limit scope")
        .await
        .unwrap();
    let original = handle.publication_view().await.unwrap();
    assert_eq!(original.config.refs.advertise, ["refs/heads/release"]);
    assert_eq!(
        original.config.refs.packfiles["code"].include,
        ["refs/heads/release"]
    );

    // The next host removes the group that the saved policy still subtracts.
    // Its broad default code group must not become a replacement coverage basis.
    let mut new_config = Config::default();
    new_config.cache.dir = new_cache.path().to_path_buf();
    new_config.validate().unwrap();
    assert!(new_config.with_settings(settings).is_err());
    let new = Registry::new(store, Arc::new(new_config));
    let reopened = new.open(&id).await.unwrap();
    assert!(reopened.publication_view().await.is_err());
    assert_eq!(reopened.settings().unwrap().toml, settings);
    assert_eq!(reopened.settings().unwrap().revision, 1);
}
