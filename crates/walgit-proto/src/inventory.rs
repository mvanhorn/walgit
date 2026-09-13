//! Exact membership helpers. Retired inventory is download history, never live proof.
use std::collections::BTreeSet;

use crate::v1::{Manifest, RetiredPack};

impl Manifest {
    pub fn serves_pack(&self, checksum: &str) -> bool {
        self.packs.iter().any(|p| p.checksum == checksum)
            || self.retired_packs.iter().any(|p| p.checksum == checksum)
    }

    /// Record currently live members before removing them. Never expires or truncates history.
    pub fn retire_packs(&mut self, checksums: &[String], seq: u64) {
        self.retire_packs_at(checksums, seq, crate::time::now());
    }

    pub fn retire_packs_at(&mut self, checksums: &[String], seq: u64, at: prost_types::Timestamp) {
        let requested: BTreeSet<_> = checksums.iter().collect();
        let mut recorded: BTreeSet<_> = self
            .retired_packs
            .iter()
            .map(|p| p.checksum.clone())
            .collect();
        for pack in &self.packs {
            if requested.contains(&pack.checksum) && recorded.insert(pack.checksum.clone()) {
                self.retired_packs.push(RetiredPack {
                    checksum: pack.checksum.clone(),
                    retired_seq: seq,
                    retired_at: Some(at),
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Message,
        v1::{Manifest, PackRef},
    };
    #[test]
    fn retirement_is_exact_deduplicated_and_survives_reencoding() {
        let mut m = Manifest {
            packs: vec![PackRef {
                checksum: "a".repeat(40),
                ..Default::default()
            }],
            ..Default::default()
        };
        m.retire_packs(&["a".repeat(40), "b".repeat(40)], 7);
        m.retire_packs(&["a".repeat(40)], 9);
        m.packs.clear();
        let m = Manifest::decode(m.encode_to_vec().as_slice()).unwrap();
        assert_eq!(m.retired_packs.len(), 1);
        assert_eq!(m.retired_packs[0].retired_seq, 7);
        assert!(m.serves_pack(&"a".repeat(40)));
        assert!(!m.serves_pack(&"b".repeat(40)));
    }
    #[test]
    fn old_wire_messages_keep_new_fields_empty() {
        // Synthetic pre-extension wire bytes: format_version=1, object_format=sha1/sha256.
        for format in ["sha1", "sha256"] {
            let mut bytes = vec![8, 1, 26, u8::try_from(format.len()).unwrap()];
            bytes.extend_from_slice(format.as_bytes());
            let m = Manifest::decode(bytes.as_slice()).unwrap();
            assert_eq!(m.object_format, format);
            assert!(m.retired_packs.is_empty());
            assert_eq!(m.encode_to_vec(), bytes);
        }
        let p = PackRef::decode(&[56, 7, 64, 2][..]).unwrap();
        assert_eq!(p.seq, 7);
        assert_eq!(p.tier, 2);
        assert!(p.group_coverages.is_empty());
        assert_eq!(p.audience, 0);
    }
}
