//! Maintenance choices from committed pack inventory. Layout thresholds are
//! independent of graph certificates: a missing proof never requests a full cut.
use std::collections::BTreeMap;
use std::time::{Duration, SystemTime};

use walgit_config::{Config, packs::FoldInventory};
use walgit_proto::v1::{Manifest, PackKind, PackRef};

/// One bounded maintenance decision. The worker captures and rechecks inputs
/// again under its lease; these checksums are never publication authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Work {
    Classify(Vec<String>),
    Fold(Vec<String>),
    Freeze(String),
    FirstFreeze,
    Resegment,
    RepairCoverage,
}

#[cfg(test)]
mod planner_tests {
    use super::*;

    #[test]
    fn count_trigger_does_not_rewrite_a_disproportionately_large_buffer() {
        let cfg = Config::default();
        let policy = cfg.refs.policy_identity();
        let mut manifest = Manifest::default();
        for n in 0..16 {
            manifest.packs.push(PackRef {
                checksum: format!("{n:040x}"),
                pack_size: 100,
                pack_groups: vec!["code".into()],
                ref_policy: policy.clone(),
                ..Default::default()
            });
        }
        for (n, bytes) in [(16, 2000), (17, 1_000_000)] {
            manifest.packs.push(PackRef {
                checksum: format!("{n:040x}"),
                pack_size: bytes,
                tier: 1,
                pack_groups: vec!["code".into()],
                ref_policy: policy.clone(),
                ..Default::default()
            });
        }
        let Some(Work::Fold(selected)) = plan(&manifest, &cfg, SystemTime::now()) else {
            panic!("fresh count should trigger a fold");
        };
        assert_eq!(selected.len(), 17);
        assert!(selected.contains(&format!("{:040x}", 16)));
        assert!(!selected.contains(&format!("{:040x}", 17)));
    }
}

fn age(pack: &PackRef, manifest: &Manifest, now: SystemTime) -> Duration {
    // Old descriptors have no publication timestamp. The last committed
    // manifest mutation is a conservative lower bound on their age.
    pack.published_at
        .or(manifest.updated_at)
        .as_ref()
        .map(walgit_proto::time::to_system)
        .and_then(|at| now.duration_since(at).ok())
        .unwrap_or_default()
}

fn redundant_history(pack: &PackRef) -> bool {
    pack.kind == PackKind::History as i32
        && pack.pack_groups.is_empty()
        && !pack.derived_from.is_empty()
}

/// Select one unit, with separate families for each group/type/audience tuple.
/// Frozen packs never enter a fold, and an idle repository is not recut by age.
pub fn plan(manifest: &Manifest, cfg: &Config, now: SystemTime) -> Option<Work> {
    if !cfg.packs.enabled || manifest.packs.is_empty() {
        return None;
    }
    let policy = cfg.refs.policy_identity();
    let unclassified: Vec<_> = manifest
        .packs
        .iter()
        .filter(|p| !redundant_history(p))
        .filter(|p| {
            p.pack_groups.is_empty() || (p.pack_groups != ["_retained"] && p.ref_policy != policy)
        })
        .take(128)
        .map(|p| p.checksum.clone())
        .collect();
    if !unclassified.is_empty() {
        return Some(Work::Classify(unclassified));
    }

    let live_bytes = manifest
        .packs
        .iter()
        .filter(|p| !redundant_history(p))
        .map(|p| p.pack_size)
        .sum();
    let floor = cfg.packfile_uri.uri_min_bytes.as_u64();
    let mut families: BTreeMap<(Vec<String>, i32, i32), Vec<&PackRef>> = BTreeMap::new();
    for pack in manifest
        .packs
        .iter()
        .filter(|p| p.tier < 2 && !redundant_history(p))
    {
        families
            .entry((pack.pack_groups.clone(), pack.kind, pack.audience))
            .or_default()
            .push(pack);
    }
    for packs in families.values() {
        let fresh: Vec<_> = packs.iter().filter(|p| p.tier == 0).collect();
        let inventory = FoldInventory {
            live_bytes,
            fresh_bytes: fresh.iter().map(|p| p.pack_size).sum(),
            fresh_packs: fresh.len(),
            oldest_fresh_age: fresh
                .iter()
                .map(|p| age(p, manifest, now))
                .max()
                .unwrap_or_default(),
        };
        if cfg.packs.fold_reason(&inventory, floor).is_some() {
            let mut selected: Vec<_> = fresh.iter().map(|p| p.checksum.clone()).collect();
            let mut size: u64 = fresh.iter().map(|p| p.pack_size).sum();
            let mut buffers: Vec<_> = packs.iter().filter(|p| p.tier == 1).collect();
            buffers.sort_by_key(|p| p.pack_size);
            for buffer in buffers {
                if buffer.pack_size > size.saturating_mul(u64::from(cfg.packs.geometric_factor)) {
                    break;
                }
                size = size.saturating_add(buffer.pack_size);
                selected.push(buffer.checksum.clone());
            }
            return Some(Work::Fold(selected));
        }
    }
    for pack in manifest.packs.iter().filter(|p| p.tier == 1) {
        if cfg
            .packs
            .freeze_reason(pack.pack_size, age(pack, manifest, now), floor)
            .is_some()
        {
            return Some(Work::Freeze(pack.checksum.clone()));
        }
    }
    let frozen: Vec<_> = manifest
        .packs
        .iter()
        .filter(|p| p.tier == 2 && !redundant_history(p))
        .collect();
    let frozen_bytes = frozen.iter().map(|p| p.pack_size).sum();
    if cfg.packs.first_freeze_due(live_bytes, frozen_bytes, floor) {
        return Some(Work::FirstFreeze);
    }
    let global_bytes = frozen
        .iter()
        .filter(|p| p.derived_from.is_empty())
        .map(|p| p.pack_size)
        .sum();
    let fold_bytes = frozen
        .iter()
        .filter(|p| !p.derived_from.is_empty())
        .map(|p| p.pack_size)
        .sum();
    if cfg.packs.resegment_due(global_bytes, fold_bytes) {
        return Some(Work::Resegment);
    }

    // Proof repair is its own metadata unit. Full graph validation belongs to
    // that unit; this cheap hint does not claim readiness or pick a URI set.
    let missing_proof = cfg.refs.packfiles.iter().any(|(name, group)| {
        !group.include.is_empty()
            && manifest.packs.iter().any(|p| p.pack_groups.contains(name))
            && !manifest
                .packs
                .iter()
                .flat_map(|p| &p.group_coverages)
                .any(|c| c.group == *name && c.ref_policy == policy)
    });
    missing_proof.then_some(Work::RepairCoverage)
}

use crate::ops::Log;
use anyhow::{Context, bail, ensure};
use prost::Message;
use std::path::{Path, PathBuf};
use walgit_git::{maintenance_input, pack_segments};
use walgit_proto::v1::{PackAudience, PackGroupCoverage};
use walgit_wal::{PackClassification, PublicationView, RepoHandle};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Prepared,
    Step,
    Sealed,
}
pub static TEST_ABORT_AFTER: parking_lot::Mutex<Option<(String, Phase)>> =
    parking_lot::Mutex::new(None);
fn abort_after(handle: &RepoHandle, phase: Phase) -> anyhow::Result<()> {
    if TEST_ABORT_AFTER
        .lock()
        .as_ref()
        .is_some_and(|(repo, p)| *repo == handle.id().to_string() && *p == phase)
    {
        bail!("pack lifecycle aborted by test hook after {phase:?}");
    }
    Ok(())
}

pub struct Outcome {
    pub packs: Vec<String>,
    pub superseded: usize,
    pub tier: u32,
    pub resumed: bool,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct Receipt {
    group: String,
    kind: i32,
    outputs: Vec<OutputReceipt>,
}
#[derive(serde::Serialize, serde::Deserialize)]
struct OutputReceipt {
    descriptor: Vec<u8>,
    path: PathBuf,
    exceeds_target: bool,
}
#[derive(serde::Serialize, serde::Deserialize)]
struct Journal {
    root: PathBuf,
    manifest: Vec<u8>,
    refs: Vec<u8>,
    policy: String,
    tuning: String,
    selected: Vec<String>,
    tier: u32,
    global: bool,
    metadata: bool,
    receipts: Vec<Receipt>,
}
fn journal_path(handle: &RepoHandle, cfg: &Config) -> PathBuf {
    cfg.cache
        .dir
        .join("_pack-lifecycle")
        .join(handle.id().owner())
        .join(format!("{}.json", handle.id().name()))
}
async fn save_journal(path: &Path, journal: &Journal) -> anyhow::Result<()> {
    tokio::fs::create_dir_all(path.parent().context("journal parent")?).await?;
    let tmp = path.with_extension("json.tmp");
    tokio::fs::write(&tmp, serde_json::to_vec(journal)?).await?;
    tokio::fs::rename(tmp, path).await?;
    Ok(())
}
fn compatible(
    journal: &Journal,
    current: &PublicationView,
    tuning: &str,
) -> anyhow::Result<PublicationView> {
    ensure!(
        journal.policy == current.config.refs.policy_identity() && journal.tuning == tuning,
        "scratch policy/tuning changed"
    );
    let manifest = Manifest::decode(journal.manifest.as_slice())?;
    walgit_wal::validate_manifest(&manifest)?;
    ensure!(
        manifest.repo == current.manifest.repo,
        "scratch repository changed"
    );
    let refs = walgit_proto::v1::RefSnapshot::decode(journal.refs.as_slice())?;
    walgit_proto::snapshot::validate(&refs)?;
    ensure!(
        refs.refs == current.refs.refs
            && refs.head_target == current.refs.head_target
            && refs.object_format == current.refs.object_format
            && refs.seq <= current.refs.seq,
        "scratch refs changed"
    );
    // Every original input remains exact and committed. Additive outputs from
    // this attempt are harmless; other new inputs require a fresh capture.
    let output_ids = journal
        .receipts
        .iter()
        .flat_map(|r| &r.outputs)
        .map(|r| PackRef::decode(r.descriptor.as_slice()).map(|p| p.checksum))
        .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
    for pack in &manifest.packs {
        ensure!(
            current.manifest.packs.iter().any(|p| p == pack),
            "scratch input changed or retired"
        );
    }
    ensure!(
        current.manifest.packs.iter().all(|p| manifest
            .packs
            .iter()
            .any(|old| old.checksum == p.checksum)
            || output_ids.contains(&p.checksum)),
        "new committed inputs require replanning"
    );
    Ok(PublicationView {
        manifest: std::sync::Arc::new(manifest),
        version: current.version.clone(),
        refs,
        config: current.config.clone(),
    })
}
fn receipts(journal: &Journal, cfg: &Config) -> anyhow::Result<Vec<pack_segments::StepReceipt>> {
    journal
        .receipts
        .iter()
        .map(|r| {
            let audience = cfg.refs.packfiles.get(&r.group).map(|g| g.kind);
            Ok(pack_segments::StepReceipt {
                group: r.group.clone(),
                kind: PackKind::try_from(r.kind)?,
                outputs: r
                    .outputs
                    .iter()
                    .map(|o| {
                        Ok(pack_segments::SegmentOutput {
                            group: r.group.clone(),
                            audience,
                            dependencies: Vec::new(),
                            pack: PackRef::decode(o.descriptor.as_slice())?,
                            path: o.path.clone(),
                            exceeds_target: o.exceeds_target,
                        })
                    })
                    .collect::<anyhow::Result<_>>()?,
            })
        })
        .collect()
}

/// One isolated, conserving unit. The lease heartbeat is managed by the caller;
/// every publication also renews synchronously so a lost lease aborts the seal.
pub async fn run(
    handle: &RepoHandle,
    cfg: &Config,
    force: bool,
    forced_full: bool,
    log: Log<'_>,
    lease: &tokio::sync::Mutex<walgit_store::coord::LeaseGuard>,
) -> anyhow::Result<Option<Outcome>> {
    drop(handle.sync_refs().await?);
    let initial = handle.publication_view().await?;
    let mut work = if forced_full {
        Some(Work::Resegment)
    } else {
        plan(&initial.manifest, &initial.config, SystemTime::now())
    };
    if work.is_none() && force {
        let mut families: BTreeMap<_, Vec<String>> = BTreeMap::new();
        for p in initial
            .manifest
            .packs
            .iter()
            .filter(|p| p.tier < 2 && !redundant_history(p))
        {
            families
                .entry((p.pack_groups.clone(), p.kind, p.audience))
                .or_default()
                .push(p.checksum.clone());
        }
        work = families
            .into_values()
            .find(|p| p.len() >= 2)
            .map(Work::Fold);
    }
    let Some(work) = work else {
        return Ok(None);
    };
    let bytes: u64 = initial
        .manifest
        .packs
        .iter()
        .map(|p| p.pack_size.saturating_add(p.idx_size))
        .sum();
    // Serving copy + isolated inputs + outputs coexist until the seal. This is
    // conservative even when the filesystem supports reflinks.
    let budget = cfg.cache_budget_bytes();
    ensure!(
        budget == 0 || bytes.saturating_mul(3) < budget,
        "pack lifecycle needs isolated input/output headroom: {} bytes, budget {}",
        bytes.saturating_mul(3),
        budget
    );
    log(format!(
        "pack lifecycle {work:?}: capturing {bytes} committed bytes in isolated scratch"
    ));
    drop(handle.sync_full().await?);
    let current = handle.publication_view().await?;
    let cpu = std::thread::available_parallelism().map_or(1, usize::from);
    let memory = if budget == 0 {
        cfg.packs.segment_delta_window_memory.as_u64()
    } else {
        budget.saturating_sub(bytes.saturating_mul(3)).max(1)
    };
    let delta = cfg.packs.delta_budget(cpu, memory)?;
    let resources = pack_segments::Resources {
        sort_memory_bytes: memory.clamp(1, 64 * 1024 * 1024),
        delta_memory_bytes: delta
            .window_memory_per_thread
            .saturating_mul(delta.threads as u64),
        threads: delta.threads,
    };
    let tuning = format!(
        "{}\n{}:{}:{}",
        toml::to_string(&cfg.packs)?,
        resources.sort_memory_bytes,
        resources.delta_memory_bytes,
        resources.threads
    );
    let path = journal_path(handle, cfg);
    let root = cfg.cache.dir.join("_pack-lifecycle").join("attempts");
    tokio::fs::create_dir_all(&root).await?;
    let old = tokio::fs::read(&path)
        .await
        .ok()
        .and_then(|b| serde_json::from_slice::<Journal>(&b).ok());
    let mut resumed = false;
    let mut restored = None;
    if let Some(journal) = old {
        let attempt = async {
            ensure!(
                journal
                    .root
                    .canonicalize()?
                    .starts_with(root.canonicalize()?),
                "scratch root outside lifecycle directory"
            );
            let captured = compatible(&journal, &current, &tuning)?;
            let input = maintenance_input::reopen(
                journal.root.clone(),
                captured.manifest.packs.clone(),
                captured.refs.clone(),
            )
            .await?;
            let selected = if journal.metadata {
                captured
                    .manifest
                    .packs
                    .iter()
                    .map(|p| p.checksum.clone())
                    .collect()
            } else {
                journal.selected.clone()
            };
            let plan = pack_segments::resume(
                input,
                selected,
                cfg.refs.clone(),
                resources,
                receipts(&journal, cfg)?,
            )
            .await?;
            Ok::<_, anyhow::Error>((journal, captured, plan))
        }
        .await;
        match attempt {
            Ok(value) => {
                restored = Some(value);
                resumed = true;
            }
            Err(error) if error.to_string().contains("maintenance attempt is busy") => {
                return Err(error);
            }
            Err(error) => log(format!(
                "scratch cannot resume ({error:#}); starting a fresh isolated attempt"
            )),
        }
    }
    let (mut journal, captured, mut physical) = if let Some(value) = restored {
        value
    } else {
        let selected = match &work {
            Work::Fold(ids) | Work::Classify(ids) => ids.clone(),
            Work::Freeze(id) => vec![id.clone()],
            _ => current
                .manifest
                .packs
                .iter()
                .map(|p| p.checksum.clone())
                .collect(),
        };
        let tier = match work {
            Work::Fold(_) => 1,
            Work::Classify(_) | Work::RepairCoverage => 0,
            _ => 2,
        };
        let global = matches!(work, Work::FirstFreeze | Work::Resegment);
        let pin = handle.pin_local_objects().await;
        let mut input = maintenance_input::prepare(
            handle.local().path().to_path_buf(),
            root,
            current.manifest.packs.clone(),
            current.refs.clone(),
            pin,
        )
        .await?;
        let scratch = input.persist();
        // Classification uses the whole captured inventory; rewrite selection
        // is narrowed only after every object has an exact family assignment.
        let planning_ids = if matches!(work, Work::Classify(_) | Work::RepairCoverage) {
            current
                .manifest
                .packs
                .iter()
                .map(|p| p.checksum.clone())
                .collect()
        } else {
            selected.clone()
        };
        let physical =
            pack_segments::plan(input, planning_ids, cfg.refs.clone(), resources).await?;
        let journal = Journal {
            root: scratch,
            manifest: current.manifest.encode_to_vec(),
            refs: current.refs.encode_to_vec(),
            policy: cfg.refs.policy_identity(),
            tuning,
            selected,
            tier,
            global,
            metadata: matches!(work, Work::Classify(_) | Work::RepairCoverage),
            receipts: Vec::new(),
        };
        save_journal(&path, &journal).await?;
        abort_after(handle, Phase::Prepared)?;
        (journal, current, physical)
    };
    if journal.metadata {
        let (returned, classification) = pack_segments::classify(physical).await?;
        physical = returned;
        if let Some(mixed) = classification
            .packs
            .iter()
            .find(|p| p.mixed && journal.selected.contains(&p.checksum))
        {
            journal.selected = vec![mixed.checksum.clone()];
            journal.metadata = false;
            physical = pack_segments::plan(
                physical.input,
                journal.selected.clone(),
                cfg.refs.clone(),
                resources,
            )
            .await?;
            save_journal(&path, &journal).await?;
        } else {
            let outcome =
                repair_metadata(handle, &captured, classification, lease, cfg, log).await?;
            drop(physical);
            let _ = tokio::fs::remove_file(&path).await;
            // Failed/cancelled blocking workers own their scratch; only the
            // completed plan above permits successful-path cleanup here.
            let _ = tokio::fs::remove_dir_all(&journal.root).await;
            return Ok(Some(outcome));
        }
    }
    for family in 0..physical.families.len() {
        if physical.families[family].completed {
            continue;
        }
        let group = physical.families[family].group.clone();
        let kind = physical.families[family].kind;
        log(format!(
            "packing family {group} {kind:?} ({}/{})",
            family + 1,
            physical.families.len()
        ));
        physical = pack_segments::step(physical, family, cfg.packs.clone()).await?;
        let outputs = physical
            .outputs
            .iter()
            .filter(|o| o.group == group && o.pack.kind == kind as i32)
            .map(|o| OutputReceipt {
                descriptor: o.pack.encode_to_vec(),
                path: o.path.clone(),
                exceeds_target: o.exceeds_target,
            })
            .collect();
        journal.receipts.push(Receipt {
            group,
            kind: kind as i32,
            outputs,
        });
        save_journal(&path, &journal).await?;
        abort_after(handle, Phase::Step)?;
    }
    let finished = pack_segments::finish(physical).await?;
    let mut outputs: BTreeMap<String, (PackRef, PathBuf)> = BTreeMap::new();
    for output in &finished.outputs {
        ensure!(
            !output.exceeds_target || output.pack.object_count > 0,
            "empty oversized output"
        );
        if output.exceeds_target {
            log(format!(
                "pack {} exceeds size target; Git may retain an indivisible oversized object",
                output.pack.checksum
            ));
        }
        let audience = match output.audience {
            Some(walgit_config::PackGroupKind::Code) => PackAudience::Code,
            Some(walgit_config::PackGroupKind::Meta) => PackAudience::Meta,
            None => PackAudience::Retained,
        };
        let entry = outputs
            .entry(output.pack.checksum.clone())
            .or_insert_with(|| {
                let mut pack = output.pack.clone();
                pack.tier = journal.tier;
                pack.audience = audience as i32;
                pack.ref_policy.clone_from(&journal.policy);
                pack.pack_groups.clear();
                pack.group_coverages.clear();
                pack.derived_from = if journal.global {
                    String::new()
                } else {
                    journal.selected.first().cloned().unwrap_or_default()
                };
                (pack, output.path.clone())
            });
        if audience == PackAudience::Code {
            entry.0.audience = PackAudience::Code as i32;
        }
        if !entry.0.pack_groups.contains(&output.group) {
            entry.0.pack_groups.push(output.group.clone());
            entry.0.pack_groups.sort();
        }
    }
    if journal.global
        && cfg.git.commit_graph
        && let Some((pack, source)) = outputs
            .values_mut()
            .find(|(p, _)| p.kind == PackKind::History as i32)
    {
        let oid = gix_hash::ObjectId::from_hex(pack.checksum.as_bytes())?;
        finished
            .input
            .repo
            .write_pack_commit_graph(&oid, cfg.git.commit_graph_changed_paths)
            .await?;
        let generated = finished
            .input
            .repo
            .pack_path(&oid)
            .with_extension("commit-graph");
        tokio::fs::copy(&generated, source.with_extension("commit-graph")).await?;
        pack.has_commit_graph = true;
        tokio::fs::remove_file(generated).await?;
        let info = finished
            .input
            .repo
            .path()
            .join("objects/info/commit-graphs");
        if info.exists() {
            tokio::fs::remove_dir_all(info).await?;
        }
    }
    let mut classes = Vec::new();
    for (pack, source) in outputs.values() {
        lease.lock().await.heartbeat(cfg.packs.lease_ttl).await?;
        let class = PackClassification::from_pack(pack);
        if !handle
            .manifest()
            .packs
            .iter()
            .any(|p| p.checksum == pack.checksum)
        {
            handle
                .publish_prepared_pack(source, pack, class.clone())
                .await?;
            log(format!("committed additive pack {}", pack.checksum));
        }
        classes.push(pack.clone());
    }
    let final_ids = captured
        .manifest
        .packs
        .iter()
        .filter(|p| !journal.selected.contains(&p.checksum))
        .map(|p| p.checksum.clone())
        .chain(outputs.keys().cloned())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .map(|id| gix_hash::ObjectId::from_hex(id.as_bytes()))
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(commit) = captured
        .refs
        .refs
        .iter()
        .find(|r| r.name.starts_with("refs/heads/"))
    {
        let oid = gix_hash::ObjectId::from_hex(commit.oid.as_bytes())?;
        handle.local().set_segmented_midx_mode(true);
        let pin = handle.pin_local_objects().await;
        handle
            .local()
            .write_verified_midx(&final_ids, oid, pin)
            .await?;
    }
    lease.lock().await.heartbeat(cfg.packs.lease_ttl).await?;
    handle
        .seal_pack_replacement(&captured, &journal.selected, &classes, &[], lease)
        .await?;
    abort_after(handle, Phase::Sealed)?;
    let outcome = Outcome {
        packs: outputs.into_keys().collect(),
        superseded: journal.selected.len(),
        tier: journal.tier,
        resumed,
    };
    drop(finished);
    let _ = tokio::fs::remove_file(path).await;
    let _ = tokio::fs::remove_dir_all(journal.root).await;
    Ok(Some(outcome))
}

async fn repair_metadata(
    handle: &RepoHandle,
    captured: &PublicationView,
    classification: pack_segments::Classification,
    lease: &tokio::sync::Mutex<walgit_store::coord::LeaseGuard>,
    cfg: &Config,
    log: Log<'_>,
) -> anyhow::Result<Outcome> {
    let snapshot = handle.prepare_coverage_snapshot(captured).await?;
    let policy = cfg.refs.policy_identity();
    let mut updates = Vec::new();
    for member in &classification.packs {
        if member.mixed {
            continue;
        }
        let audience = match member.audience {
            Some(walgit_config::PackGroupKind::Code) => PackAudience::Code,
            Some(walgit_config::PackGroupKind::Meta) => PackAudience::Meta,
            None => PackAudience::Retained,
        };
        updates.push(PackClassification {
            checksum: member.checksum.clone(),
            kind: member.kind as i32,
            audience: audience as i32,
            ref_policy: policy.clone(),
            pack_groups: member.groups.clone(),
            covers_seq: captured.refs.seq,
            coverage_refs_key: snapshot.key().to_string(),
            group_coverages: Vec::new(),
        });
    }
    // Metadata refresh can exceed one CAS batch. No partial batch carries a
    // proof; the final carrier update checks all same-generation members live.
    for batch in updates.chunks(128) {
        lease.lock().await.heartbeat(cfg.packs.lease_ttl).await?;
        handle.reclassify_packs(batch, &[]).await?;
    }
    let roots = walgit_git::pack_groups::resolve_groups(
        &cfg.refs,
        &walgit_git::RefSnapshotData::from(captured.refs.clone()),
    )?;
    let members: BTreeMap<String, Vec<String>> = cfg
        .refs
        .packfiles
        .keys()
        .map(|group| {
            (
                group.clone(),
                updates
                    .iter()
                    .filter(|p| p.pack_groups.contains(group))
                    .map(|p| p.checksum.clone())
                    .collect(),
            )
        })
        .collect();
    let complete = |group: &str| {
        classification.group_complete.get(group) == Some(&true)
            && members.get(group).is_some_and(|p| !p.is_empty())
    };
    let mut carriers: BTreeMap<String, PackClassification> = BTreeMap::new();
    for (group, root) in roots {
        if !complete(&group) || !root.dependencies.iter().all(|d| complete(d)) {
            continue;
        }
        let ids = members.get(&group).context("missing group members")?;
        let carrier = updates
            .iter()
            .find(|p| p.checksum == ids[0])
            .context("missing coverage carrier")?;
        carriers
            .entry(carrier.checksum.clone())
            .or_insert_with(|| carrier.clone())
            .group_coverages
            .push(PackGroupCoverage {
                group,
                ref_policy: policy.clone(),
                covers_seq: captured.refs.seq,
                packs: ids.clone(),
                refs_key: snapshot.key().to_string(),
            });
    }
    // Dependency sets must commit together. Bounded policy cardinality keeps
    // this one batch; exceeding it leaves metadata classified but uncertified.
    ensure!(
        carriers.len() <= 128,
        "coverage has more than 128 carriers; reduce group count"
    );
    if !carriers.is_empty() {
        lease.lock().await.heartbeat(cfg.packs.lease_ttl).await?;
        handle
            .reclassify_packs(&carriers.into_values().collect::<Vec<_>>(), &[snapshot])
            .await?;
    }
    log(format!(
        "classified {} packs and repaired provable group coverage without rewriting pack bytes",
        updates.len()
    ));
    Ok(Outcome {
        packs: updates.into_iter().map(|p| p.checksum).collect(),
        superseded: 0,
        tier: 0,
        resumed: false,
    })
}
