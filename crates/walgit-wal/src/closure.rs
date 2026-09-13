//! Exact indexed inventory checks. Local readability and retired membership are
//! not publication evidence. Callers bind these mappings to their CAS snapshot.
use std::cmp::Reverse;
use std::collections::BinaryHeap;

use gix_hash::ObjectId;
use walgit_proto::v1::{Manifest, PackRef, RefSnapshot};

use crate::{RepoHandle, WalError, progress::Reporter};

/// Merge sorted index OIDs with one cursor per pack, never a set per object.
struct IndexUnion<'a> {
    indexes: Vec<&'a gix_pack::index::File>,
    cursors: BinaryHeap<Reverse<(ObjectId, usize, u32)>>,
    previous: Option<ObjectId>,
}
impl<'a> IndexUnion<'a> {
    fn new(indexes: Vec<&'a gix_pack::index::File>) -> Self {
        let cursors = indexes
            .iter()
            .enumerate()
            .filter(|(_, index)| index.num_objects() > 0)
            .map(|(i, index)| Reverse((index.oid_at_index(0).to_owned(), i, 0)))
            .collect();
        Self {
            indexes,
            cursors,
            previous: None,
        }
    }
}
impl Iterator for IndexUnion<'_> {
    type Item = ObjectId;
    #[allow(
        clippy::indexing_slicing,
        reason = "Heap positions come only from enumeration of the immutable index vector"
    )]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(Reverse((oid, pack, position))) = self.cursors.pop() {
            let index = self.indexes[pack];
            if position + 1 < index.num_objects() {
                self.cursors.push(Reverse((
                    index.oid_at_index(position + 1).to_owned(),
                    pack,
                    position + 1,
                )));
            }
            if self.previous != Some(oid) {
                self.previous = Some(oid);
                return Some(oid);
            }
        }
        None
    }
}

pub(crate) async fn verify_replacement_inventory(
    handle: &RepoHandle,
    current: &Manifest,
    result: &Manifest,
    refs: &RefSnapshot,
    inputs: &[String],
    outputs: &[PackRef],
) -> Result<(), WalError> {
    let reporter = Reporter::for_repo(handle.progress.clone());
    reporter.notice("Verifying replacement object conservation and current tips");
    let indexes = crate::index_cache::load(
        &handle.store,
        handle.local.path(),
        &current.packs,
        &current.packs,
        handle.local.object_format().kind(),
        &reporter,
    )
    .await?;
    let inputs = inputs.to_vec();
    let outputs: Vec<_> = outputs.iter().map(|p| p.checksum.clone()).collect();
    let retained: Vec<_> = result.packs.iter().map(|p| p.checksum.clone()).collect();
    let refs = refs.clone();
    tokio::task::spawn_blocking(move || {
        let input_indexes = indexes
            .iter()
            .filter(|(p, _)| inputs.contains(&p.checksum))
            .map(|(_, i)| i)
            .collect();
        let output_indexes = indexes
            .iter()
            .filter(|(p, _)| outputs.contains(&p.checksum))
            .map(|(_, i)| i)
            .collect();
        let mut output_objects = IndexUnion::new(output_indexes).peekable();
        let mut checked = 0u64;
        for oid in IndexUnion::new(input_indexes) {
            checked += 1;
            if checked.is_multiple_of(262_144) {
                reporter.bar(
                    "Verifying replacement conservation",
                    checked,
                    None,
                    "objects",
                );
            }
            while output_objects.peek().is_some_and(|next| *next < oid) {
                output_objects.next();
            }
            if output_objects.peek() != Some(&oid) {
                return Err(WalError::Invalid(format!(
                    "replacement loses indexed object {oid}"
                )));
            }
        }
        reporter.bar(
            "Verifying replacement conservation",
            checked,
            Some(checked),
            "objects",
        );
        for reference in refs.refs {
            let oid = ObjectId::from_hex(reference.oid.as_bytes())
                .map_err(|e| WalError::Corrupt(e.to_string()))?;
            if !indexes
                .iter()
                .any(|(p, i)| retained.contains(&p.checksum) && i.lookup(oid).is_some())
            {
                return Err(WalError::Invalid(format!(
                    "replacement does not cover current tip {} ({oid})",
                    reference.name
                )));
            }
        }
        Ok(())
    })
    .await
    .map_err(|e| WalError::Corrupt(e.to_string()))?
}
