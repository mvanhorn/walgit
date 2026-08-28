//! `lfs.serve_via = "signed_url"` uploads: the batch's `upload` action becomes a
//! presigned, checksummed PUT straight to the store, `verify` stays on walgit.
//!
//! The in-memory store signs nothing (like every backend that cannot bind a
//! sha256 on a PUT), so it carries a test switch — `fake_signed_puts` — that
//! answers the way a signing backend does. What is asserted here is walgit's half
//! of the contract: which href a client is given, that the store's signed headers
//! reach it verbatim, that `verify` is unchanged and still authenticated, and that
//! anything short of a bound PUT keeps the bytes coming through walgit.

mod harness;

use std::sync::atomic::Ordering;

use anyhow::Result;
use base64::Engine as _;
use harness::Server;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use walgit_store::memory::{FAKE_SIGNED_PUT_CHECKSUM_HEADER, MemoryStore};

const TOKEN: &str = "writer-token";

fn tokens(cfg: &mut walgit_config::Config) {
    cfg.server.auth.mode = walgit_config::AuthMode::Token;
    cfg.server.auth.anonymous_read = false;
    cfg.server.auth.tokens = vec![walgit_config::StaticToken {
        principal: "writer@example.com".into(),
        token: TOKEN.into(),
        token_env: None,
        write: true,
        admin: false,
    }];
}

/// `Server::put_repo` sends no credential, and these servers require one.
async fn create_repo(server: &Server) -> Result<()> {
    let resp = reqwest::Client::new()
        .put(format!("{}/o/r", server.base_url))
        .bearer_auth(TOKEN)
        .send()
        .await?;
    assert!(resp.status().is_success(), "create repo: {}", resp.status());
    Ok(())
}

fn batch_upload(oid: &str, size: usize) -> Value {
    json!({
        "operation": "upload",
        "transfers": ["basic"],
        "objects": [{"oid": oid, "size": size}],
    })
}

async fn upload_batch(server: &Server, oid: &str, size: usize) -> Result<Value> {
    let resp = reqwest::Client::new()
        .post(format!(
            "{}/o/r.git/info/lfs/objects/batch",
            server.base_url
        ))
        .bearer_auth(TOKEN)
        .json(&batch_upload(oid, size))
        .send()
        .await?;
    assert_eq!(resp.status(), reqwest::StatusCode::OK);
    assert_eq!(
        resp.headers()
            .get("cache-control")
            .and_then(|v| v.to_str().ok()),
        Some("no-store"),
        "a batch answer carries signed URLs and a credential"
    );
    Ok(resp.json().await?)
}

/// A store that signs checksummed PUTs: the client uploads to it directly, with
/// the store's headers, and comes back to walgit only for `verify`.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn signed_url_uploads_go_to_the_store_with_the_oid_bound_to_the_put() -> Result<()> {
    let body = b"lfs bytes that never touch walgit".to_vec();
    let oid = hex::encode(Sha256::digest(&body));
    let store = MemoryStore::shared();
    store.fake_signed_puts.store(true, Ordering::Relaxed);
    let server = Server::start_with_store_and_tweak(store, |c| {
        tokens(c);
        c.lfs.serve_via = walgit_config::BundleServe::SignedUrl;
        c.lfs.signed_url_ttl = std::time::Duration::from_secs(900);
    })
    .await?;
    create_repo(&server).await?;

    let r = upload_batch(&server, &oid, body.len()).await?;
    let obj = &r["objects"][0];
    let upload = &obj["actions"]["upload"];
    assert_eq!(
        upload["href"].as_str(),
        Some(
            format!("https://storage.example.test/test-bucket/repos/o/r/lfs/objects/{}/{}/{oid}?X-Test-Signature=1",
                &oid[..2], &oid[2..4])
            .as_str()
        ),
        "the upload href is the store's signed URL: {obj}"
    );
    // The checksum the store signed is the oid itself, so the PUT can only land
    // the bytes the client said it was uploading.
    assert_eq!(
        upload["header"][FAKE_SIGNED_PUT_CHECKSUM_HEADER].as_str(),
        Some(
            base64::engine::general_purpose::STANDARD
                .encode(Sha256::digest(&body))
                .as_str()
        ),
        "signed headers must reach the client verbatim: {obj}"
    );
    assert_eq!(upload["expires_in"].as_u64(), Some(900));

    // `verify` is walgit's, unchanged, and still authenticated: `authenticated`
    // stops git-lfs adding walgit's credential to the store's URL, so the one it
    // needs for `verify` travels on that action.
    assert_eq!(obj["authenticated"], true);
    assert_eq!(
        obj["actions"]["verify"]["href"].as_str(),
        Some(format!("{}/o/r/info/lfs/verify", server.base_url).as_str()),
        "{obj}"
    );
    assert_eq!(
        obj["actions"]["verify"]["header"]["authorization"].as_str(),
        Some(format!("Bearer {TOKEN}").as_str()),
        "{obj}"
    );

    // Nothing was written by handing out the URL: the object is still missing, so
    // a second batch offers the same upload rather than reporting it present.
    let again = upload_batch(&server, &oid, body.len()).await?;
    assert!(again["objects"][0]["actions"]["upload"].is_object());
    Ok(())
}

/// The default. `verify` gets no credential of its own because git-lfs
/// authenticates the walgit href itself, and the PUT's sha256 gate still runs.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn proxy_is_the_default_and_still_checks_the_sha256_itself() -> Result<()> {
    let body = b"lfs bytes through walgit".to_vec();
    let oid = hex::encode(Sha256::digest(&body));
    let server = Server::start_with_tweak(tokens).await?;
    create_repo(&server).await?;

    let r = upload_batch(&server, &oid, body.len()).await?;
    let obj = &r["objects"][0];
    let href = obj["actions"]["upload"]["href"]
        .as_str()
        .expect("upload href")
        .to_string();
    assert_eq!(
        href,
        format!("{}/o/r/info/lfs/objects/{oid}", server.base_url)
    );
    assert!(obj["actions"]["upload"]["header"].is_null(), "{obj}");
    assert!(obj["actions"]["verify"]["header"].is_null(), "{obj}");
    assert!(
        obj["authenticated"].is_null(),
        "git-lfs must authenticate our own href: {obj}"
    );

    let client = reqwest::Client::new();
    // Bytes that do not hash to the oid are refused before the store write.
    let bad = client
        .put(&href)
        .bearer_auth(TOKEN)
        .body(b"other bytes".to_vec())
        .send()
        .await?;
    assert_eq!(bad.status(), reqwest::StatusCode::BAD_REQUEST);
    // The real ones land, and `verify` confirms them.
    let ok = client
        .put(&href)
        .bearer_auth(TOKEN)
        .body(body.clone())
        .send()
        .await?;
    assert_eq!(ok.status(), reqwest::StatusCode::OK);
    let verified = client
        .post(format!("{}/o/r/info/lfs/verify", server.base_url))
        .bearer_auth(TOKEN)
        .json(&json!({"oid": oid, "size": body.len()}))
        .send()
        .await?;
    assert_eq!(verified.status(), reqwest::StatusCode::OK);
    Ok(())
}

/// Fail closed. A store that signs nothing, and a store whose signing is denied,
/// both leave the upload on walgit — never a signed PUT that is not bound to the
/// oid, and never a failed push.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_store_that_cannot_bind_the_checksum_keeps_the_upload_on_walgit() -> Result<()> {
    let oid = hex::encode(Sha256::digest(b"unsignable"));
    for signing_fails in [false, true] {
        let mut store = MemoryStore::new();
        store.signing_fails = signing_fails;
        let server = Server::start_with_store_and_tweak(std::sync::Arc::new(store), |c| {
            tokens(c);
            c.lfs.serve_via = walgit_config::BundleServe::SignedUrl;
        })
        .await?;
        create_repo(&server).await?;

        let r = upload_batch(&server, &oid, 10).await?;
        let obj = &r["objects"][0];
        assert_eq!(
            obj["actions"]["upload"]["href"].as_str(),
            Some(format!("{}/o/r/info/lfs/objects/{oid}", server.base_url).as_str()),
            "signing_fails={signing_fails}: {obj}"
        );
        assert!(obj["actions"]["upload"]["header"].is_null(), "{obj}");
        assert!(obj["authenticated"].is_null(), "{obj}");
    }
    Ok(())
}

/// `lfs.max_object_bytes` can only be enforced where the bytes pass through, so
/// an object over the cap is not signed: it goes to the proxy href, which rejects
/// it (413) instead of the store accepting it behind walgit's back.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_object_over_the_cap_is_never_signed() -> Result<()> {
    let body = vec![b'x'; 4096];
    let oid = hex::encode(Sha256::digest(&body));
    let store = MemoryStore::shared();
    store.fake_signed_puts.store(true, Ordering::Relaxed);
    let server = Server::start_with_store_and_tweak(store, |c| {
        tokens(c);
        c.lfs.serve_via = walgit_config::BundleServe::SignedUrl;
        c.lfs.max_object_bytes = bytesize::ByteSize::b(1024);
    })
    .await?;
    create_repo(&server).await?;

    let r = upload_batch(&server, &oid, body.len()).await?;
    let obj = &r["objects"][0];
    let href = obj["actions"]["upload"]["href"]
        .as_str()
        .expect("upload href")
        .to_string();
    assert_eq!(
        href,
        format!("{}/o/r/info/lfs/objects/{oid}", server.base_url),
        "{obj}"
    );
    let too_big = reqwest::Client::new()
        .put(&href)
        .bearer_auth(TOKEN)
        .body(body)
        .send()
        .await?;
    assert_eq!(too_big.status(), reqwest::StatusCode::PAYLOAD_TOO_LARGE);

    // Under the cap the same repo signs again.
    let small = b"small".to_vec();
    let small_oid = hex::encode(Sha256::digest(&small));
    let r = upload_batch(&server, &small_oid, small.len()).await?;
    assert!(
        r["objects"][0]["actions"]["upload"]["href"]
            .as_str()
            .is_some_and(|h| h.starts_with("https://storage.example.test/")),
        "{r}"
    );
    Ok(())
}
