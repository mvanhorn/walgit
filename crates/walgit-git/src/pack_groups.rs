//! Resolve packaging roots from a captured ref view, independently of discovery.
//!
//! This describes graph walks, not evidence that any pack contains their results.
use std::collections::{BTreeMap, BTreeSet};

use walgit_config::refs::{PackGroupKind, RefsConfig};

use crate::{GitError, RefSnapshotData, validate_ref_name};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupRoots {
    pub kind: PackGroupKind,
    /// Positive revision roots; annotated tags remain roots themselves.
    pub include: Vec<String>,
    /// Logical roots of subtraction dependencies, before their own subtraction.
    pub exclude: Vec<String>,
    /// Complete transitive dependency names needed when delivering this group.
    pub dependencies: Vec<String>,
}

/// Resolve deterministic Git revision inputs using only the supplied snapshot.
/// Unmatched objects must be conserved separately by the packing caller.
pub fn resolve_groups(
    config: &RefsConfig,
    snapshot: &RefSnapshotData,
) -> Result<BTreeMap<String, GroupRoots>, GitError> {
    config
        .validate()
        .map_err(|e| GitError::InvalidInput(e.to_string()))?;
    let mut names = BTreeSet::new();
    for reference in &snapshot.refs {
        validate_ref_name(&reference.name)?;
        if reference.name == "HEAD" || !names.insert(&reference.name) {
            return Err(GitError::InvalidInput(
                "duplicate or symbolic ref in snapshot".into(),
            ));
        }
        // Revision input is an object id, never a ref name or an option.
        let oid = gix_hash::ObjectId::from_hex(reference.oid.as_bytes())
            .map_err(|e| GitError::InvalidInput(e.to_string()))?;
        if oid.is_null() {
            return Err(GitError::InvalidInput("null ref target in snapshot".into()));
        }
    }
    let roots: BTreeMap<_, BTreeSet<_>> = config
        .packfiles
        .iter()
        .map(|(name, group)| {
            let roots = snapshot
                .refs
                .iter()
                .filter(|reference| group.matches_ref(&reference.name, &snapshot.head_target))
                .map(|reference| reference.oid.clone())
                .collect();
            (name.clone(), roots)
        })
        .collect();
    let mut result = BTreeMap::new();
    for (name, group) in &config.packfiles {
        let mut dependencies = BTreeSet::new();
        let mut pending = group.subtract.clone();
        while let Some(dependency) = pending.pop() {
            if dependencies.insert(dependency.clone()) {
                let target = config
                    .packfiles
                    .get(&dependency)
                    .ok_or_else(|| GitError::InvalidInput(format!("missing group {dependency}")))?;
                pending.extend(target.subtract.iter().cloned());
            }
        }
        // Only direct dependencies define this physical set. Recursing here
        // would remove objects outside the dependency's logical closure.
        let exclude: BTreeSet<_> = group
            .subtract
            .iter()
            .filter_map(|dependency| roots.get(dependency))
            .flat_map(|roots| roots.iter().cloned())
            .collect();
        result.insert(
            name.clone(),
            GroupRoots {
                kind: group.kind,
                include: roots.get(name).into_iter().flatten().cloned().collect(),
                exclude: exclude.into_iter().collect(),
                dependencies: dependencies.into_iter().collect(),
            },
        );
    }
    Ok(result)
}
