//! Canonical ref snapshots. Exact content keys are authority only after publication.
use anyhow::{Result, ensure};
use prost::Message;
use sha2::{Digest, Sha256};

use crate::v1::RefSnapshot;

#[expect(
    clippy::case_sensitive_file_extension_comparisons,
    reason = "Git refname rules reject the case-sensitive .lock suffix"
)]
fn valid_ref(name: &str) -> bool {
    name.starts_with("refs/")
        && !name.ends_with('/')
        && !name.ends_with('.')
        && !name.contains("..")
        && !name.contains("@{")
        && !name
            .bytes()
            .any(|b| b <= b' ' || b == 127 || b"~^:?*[\\".contains(&b))
        && name
            .split('/')
            .all(|p| !p.is_empty() && !p.starts_with('.') && !p.ends_with(".lock"))
}

fn valid_oid(oid: &str, len: usize) -> bool {
    oid.len() == len
        && oid
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        && oid.bytes().any(|b| b != b'0')
}

/// Validate object format, ref names/OIDs, unique names and symbolic HEAD syntax.
/// An unborn symbolic HEAD may name a ref absent from the snapshot.
pub fn validate(snapshot: &RefSnapshot) -> Result<()> {
    let oid_len = match snapshot.object_format.as_str() {
        "sha1" => 40,
        "sha256" => 64,
        other => anyhow::bail!("unsupported snapshot object format {other:?}"),
    };
    ensure!(
        snapshot.head_target.is_empty() || valid_ref(&snapshot.head_target),
        "invalid snapshot symbolic HEAD"
    );
    let mut names = std::collections::BTreeSet::new();
    for r in &snapshot.refs {
        ensure!(valid_ref(&r.name), "invalid snapshot ref name {:?}", r.name);
        ensure!(names.insert(&r.name), "duplicate snapshot ref {:?}", r.name);
        ensure!(
            valid_oid(&r.oid, oid_len),
            "invalid snapshot OID for {}",
            r.name
        );
        ensure!(
            r.peeled.is_empty()
                || (r.name.starts_with("refs/tags/") && valid_oid(&r.peeled, oid_len)),
            "invalid snapshot peeled target for {}",
            r.name
        );
    }
    Ok(())
}

/// Sort refs and omit incidental creation time. Duplicate/conflicting refs are errors.
pub fn canonicalize(snapshot: &RefSnapshot) -> Result<RefSnapshot> {
    validate(snapshot)?;
    let mut canonical = snapshot.clone();
    canonical.refs.sort_by(|a, b| a.name.cmp(&b.name));
    canonical.created_at = None;
    Ok(canonical)
}

pub fn encode(snapshot: &RefSnapshot) -> Result<Vec<u8>> {
    Ok(canonicalize(snapshot)?.encode_to_vec())
}

pub fn key(bytes: &[u8]) -> String {
    format!("checkpoints/refs/{}.pb", hex::encode(Sha256::digest(bytes)))
}

/// Verify exact canonical encoding as well as the content-addressed key.
pub fn decode_verified(expected_key: &str, bytes: &[u8]) -> Result<RefSnapshot> {
    ensure!(key(bytes) == expected_key, "snapshot content key mismatch");
    let snapshot = RefSnapshot::decode(bytes)?;
    ensure!(
        encode(&snapshot)? == bytes,
        "snapshot encoding is not canonical"
    );
    Ok(snapshot)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v1::Ref;
    fn fixture(format: &str) -> RefSnapshot {
        let len = if format == "sha1" { 40 } else { 64 };
        RefSnapshot {
            seq: 7,
            object_format: format.into(),
            head_target: "refs/heads/main".into(),
            created_at: Some(crate::time::now()),
            refs: vec![
                Ref {
                    name: "refs/tags/v1".into(),
                    oid: "b".repeat(len),
                    peeled: "a".repeat(len),
                },
                Ref {
                    name: "refs/heads/main".into(),
                    oid: "a".repeat(len),
                    peeled: String::new(),
                },
            ],
        }
    }
    #[test]
    fn sha1_and_sha256_canonicalize_independently_of_time_and_order() {
        for format in ["sha1", "sha256"] {
            let mut s = fixture(format);
            let bytes = encode(&s).unwrap();
            s.refs.reverse();
            s.created_at = None;
            assert_eq!(bytes, encode(&s).unwrap());
            assert_eq!(
                decode_verified(&key(&bytes), &bytes).unwrap(),
                canonicalize(&s).unwrap()
            );
            let mut conflict = s.clone();
            conflict.refs[0].oid = "c".repeat(conflict.refs[0].oid.len());
            assert_ne!(key(&bytes), key(&encode(&conflict).unwrap()));
            assert!(decode_verified(&key(&bytes), &encode(&conflict).unwrap()).is_err());
        }
    }
    #[test]
    fn malformed_duplicate_and_noncanonical_snapshots_fail() {
        let mut s = fixture("sha1");
        s.refs.push(s.refs[0].clone());
        assert!(encode(&s).is_err());
        let mut s = fixture("sha1");
        s.refs[0].oid = "0".repeat(40);
        assert!(encode(&s).is_err());
        let mut s = fixture("sha1");
        s.refs[0].name = "refs/../x".into();
        assert!(encode(&s).is_err());
        let mut s = fixture("sha1");
        s.head_target = "main".into();
        assert!(encode(&s).is_err());
        let s = fixture("sha1");
        let noncanonical = s.encode_to_vec();
        assert!(decode_verified(&key(&noncanonical), &noncanonical).is_err());
        assert!(decode_verified("checkpoints/refs/not-a-digest.pb", &encode(&s).unwrap()).is_err());
    }
}
