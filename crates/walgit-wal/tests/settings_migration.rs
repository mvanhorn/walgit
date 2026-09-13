//! Durable settings migrations never change the original audit document.
use prost::Message;
use std::sync::Arc;
use walgit_config::Config;
use walgit_git::{ObjectFormat, RepoId};
use walgit_store::{ObjectStoreExt, PutMode};
use walgit_wal::Registry;

#[tokio::test]
async fn obsolete_byte_policy_disables_maintenance_and_conflicts_fail_closed() {
    let cases = [
        (
            "[compaction]\nfactor=3\ntrigger_packs=4\ntrigger_bytes='1MiB'\nengine='git'\n[upstream]\ngit='https://example.invalid/repository.git'\nfollow=['refs/heads/release']\n",
            true,
        ),
        ("[compaction]\nretention_superseded='7d'\n", true),
        (
            "[compaction]\nfactor=3\n[packs]\ngeometric_factor=4\n",
            false,
        ),
        ("[compaction]\ntrigger_packs=1\n", false),
    ];
    for (index, (saved, valid)) in cases.into_iter().enumerate() {
        let store = walgit_store::memory::MemoryStore::shared();
        let cache = tempfile::tempdir().unwrap();
        let mut cfg = Config::default();
        cfg.cache.dir = cache.path().to_owned();
        assert!(
            cfg.with_settings(saved).is_err(),
            "new writes must reject obsolete sections"
        );
        let registry = Registry::new(store.clone(), Arc::new(cfg.clone()));
        let id = RepoId::new("test", format!("migration-{index}")).unwrap();
        let handle = registry.create(&id, ObjectFormat::Sha1).await.unwrap();
        handle
            .publish_settings("[packs]\nenabled=true\n", "operator", "seed")
            .await
            .unwrap();
        let mut manifest = (*handle.manifest()).clone();
        manifest.settings.as_mut().unwrap().toml = saved.into();
        let key = format!("{}{}", id.store_prefix(), walgit_proto::keys::MANIFEST);
        store
            .put_bytes(&key, manifest.encode_to_vec(), PutMode::Overwrite)
            .await
            .unwrap();
        let cold = tempfile::tempdir().unwrap();
        cfg.cache.dir = cold.path().to_owned();
        let reader = Registry::new(store, Arc::new(cfg));
        let reopened = reader.open(&id).await.unwrap();
        let effective = reopened.validated_effective_config();
        assert_eq!(effective.is_ok(), valid, "{saved}: {effective:?}");
        if let Ok(config) = effective {
            assert!(!config.packs.enabled);
            if index == 0 {
                assert_eq!(config.packs.geometric_factor, 3);
                assert_eq!(config.upstream.follow, ["refs/heads/release"]);
            }
        }
        assert_eq!(reopened.settings().unwrap().toml, saved);
        assert_eq!(reopened.settings().unwrap().revision, 1);
    }
}
