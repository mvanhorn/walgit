//! Pack lifecycle policy. These decisions schedule work; they never certify graph
//! coverage, authorize URI delivery, or permit retiring an input before a seal.
use std::time::Duration;

use anyhow::{Result, ensure};
use serde::{Deserialize, Serialize};

use crate::ByteSize;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields, default)]
pub struct PacksConfig {
    pub enabled: bool,
    pub geometric_factor: u32,
    pub fold_when_fresh_packs_reach: usize,
    #[serde(with = "humantime_serde")]
    pub fold_when_max_age: Duration,
    pub fold_needs_at_least_packs: usize,
    /// Target passed to Git's max-pack-size, not an absolute oversized-object cap.
    pub segment_max_bytes: ByteSize,
    /// Zero derives the planning target from `segment_max_bytes`.
    pub segment_target_bytes: ByteSize,
    pub segment_delta_window: u32,
    pub segment_delta_depth: u32,
    /// Whole operation delta-search budget, divided across resolved threads.
    /// This does not bound the process's full RSS.
    pub segment_delta_window_memory: ByteSize,
    pub segment_reuse_objects: bool,
    /// Zero resolves available CPUs. Explicit values remain bounded by that availability.
    pub segment_threads: usize,
    #[serde(with = "humantime_serde")]
    pub freeze_when_settled: Duration,
    /// Desired frozen share, 0 disables the first-freeze coverage trigger.
    pub frozen_coverage_target: f64,
    /// Re-segment when frozen-fold bytes exceed this multiple of the last global cut.
    pub resegment_when_frozen_folds_exceed: f64,
    #[serde(with = "humantime_serde")]
    pub lease_ttl: Duration,
}

impl Default for PacksConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            geometric_factor: 2,
            fold_when_fresh_packs_reach: 16,
            fold_when_max_age: Duration::from_hours(24),
            fold_needs_at_least_packs: 2,
            segment_max_bytes: ByteSize::gib(2),
            segment_target_bytes: ByteSize::b(0),
            segment_delta_window: 250,
            segment_delta_depth: 50,
            segment_delta_window_memory: ByteSize::gib(2),
            segment_reuse_objects: true,
            segment_threads: 0,
            freeze_when_settled: Duration::from_hours(14 * 24),
            frozen_coverage_target: 0.75,
            resegment_when_frozen_folds_exceed: 0.5,
            lease_ttl: Duration::from_mins(10),
        }
    }
}

/// Counts for one compatible family. Frozen and other-family packs are excluded
/// from fresh bytes/count; `live_bytes` is the repository's complete live inventory.
#[derive(Debug, Clone, Default)]
pub struct FoldInventory {
    pub live_bytes: u64,
    pub fresh_bytes: u64,
    pub fresh_packs: usize,
    pub oldest_fresh_age: Duration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldReason {
    Count,
    Bytes,
    Age,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FreezeReason {
    Size,
    Settled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeltaBudget {
    pub threads: usize,
    pub window_memory_per_thread: u64,
}

impl PacksConfig {
    pub fn validate(&self) -> Result<()> {
        ensure!(
            self.geometric_factor >= 2,
            "packs.geometric_factor must be >= 2"
        );
        ensure!(
            self.fold_needs_at_least_packs >= 2,
            "packs.fold_needs_at_least_packs must be >= 2"
        );
        ensure!(
            self.fold_when_fresh_packs_reach >= self.fold_needs_at_least_packs,
            "packs.fold_when_fresh_packs_reach must reach the minimum useful count"
        );
        ensure!(
            !self.enabled || self.segment_max_bytes.as_u64() >= ByteSize::mib(1).as_u64(),
            "packs.segment_max_bytes must be >= 1 MiB when enabled"
        );
        let target = self.segment_target_bytes.as_u64();
        ensure!(
            target == 0
                || (target >= ByteSize::mib(1).as_u64()
                    && target <= self.segment_max_bytes.as_u64()),
            "packs.segment_target_bytes must be zero or 1 MiB..=segment_max_bytes"
        );
        ensure!(
            self.segment_delta_window > 0,
            "packs.segment_delta_window must be positive"
        );
        ensure!(
            self.segment_delta_depth > 0,
            "packs.segment_delta_depth must be positive"
        );
        ensure!(
            self.segment_delta_window_memory.as_u64() > 0,
            "packs.segment_delta_window_memory must be positive (zero would be unbounded)"
        );
        ensure!(
            self.frozen_coverage_target.is_finite()
                && (0.0..=1.0).contains(&self.frozen_coverage_target),
            "packs.frozen_coverage_target must be finite and within 0..=1"
        );
        ensure!(
            self.resegment_when_frozen_folds_exceed.is_finite()
                && self.resegment_when_frozen_folds_exceed > 0.0,
            "packs.resegment_when_frozen_folds_exceed must be finite and positive"
        );
        ensure!(
            !self.lease_ttl.is_zero(),
            "packs.lease_ttl must be positive"
        );
        Ok(())
    }

    pub fn target_bytes(&self) -> u64 {
        let target = self.segment_target_bytes.as_u64();
        if target == 0 {
            self.segment_max_bytes.as_u64()
        } else {
            target
        }
    }

    /// A proportional byte trigger, floored by the useful URI threshold.
    pub fn fold_byte_threshold(&self, live_bytes: u64, uri_min_bytes: u64) -> u64 {
        let factor = u64::from(self.geometric_factor.max(2));
        (live_bytes / (factor * factor)).max(uri_min_bytes)
    }

    pub fn fold_reason(&self, inventory: &FoldInventory, uri_min_bytes: u64) -> Option<FoldReason> {
        if !self.enabled || inventory.fresh_packs < self.fold_needs_at_least_packs.max(2) {
            return None;
        }
        if inventory.fresh_packs >= self.fold_when_fresh_packs_reach {
            return Some(FoldReason::Count);
        }
        if inventory.fresh_bytes
            >= self
                .fold_byte_threshold(inventory.live_bytes, uri_min_bytes)
                .max(1)
        {
            return Some(FoldReason::Bytes);
        }
        if !self.fold_when_max_age.is_zero() && inventory.oldest_fresh_age >= self.fold_when_max_age
        {
            return Some(FoldReason::Age);
        }
        None
    }

    /// A zero settlement duration disables the age arm; size remains independent.
    pub fn freeze_reason(
        &self,
        fold_bytes: u64,
        settled_for: Duration,
        uri_min_bytes: u64,
    ) -> Option<FreezeReason> {
        if !self.enabled || fold_bytes == 0 {
            return None;
        }
        if self.segment_max_bytes.as_u64() > 0 && fold_bytes >= self.segment_max_bytes.as_u64() {
            return Some(FreezeReason::Size);
        }
        if fold_bytes >= uri_min_bytes.max(1)
            && !self.freeze_when_settled.is_zero()
            && settled_for >= self.freeze_when_settled
        {
            return Some(FreezeReason::Settled);
        }
        None
    }

    /// Resource planning only: approximate ratios never constitute a coverage proof.
    #[expect(
        clippy::cast_precision_loss,
        reason = "Byte ratios schedule maintenance, not graph correctness"
    )]
    pub fn first_freeze_due(&self, live_bytes: u64, frozen_bytes: u64, uri_min_bytes: u64) -> bool {
        self.enabled
            && uri_min_bytes > 0
            && live_bytes / 4 >= uri_min_bytes
            && self.frozen_coverage_target > 0.0
            && (frozen_bytes as f64) < self.frozen_coverage_target * live_bytes as f64
    }

    /// A missing global baseline belongs to first-freeze planning, not a zero denominator.
    #[expect(
        clippy::cast_precision_loss,
        reason = "Byte ratios schedule maintenance, not graph correctness"
    )]
    pub fn resegment_due(&self, global_cut_bytes: u64, frozen_fold_bytes: u64) -> bool {
        self.enabled
            && global_cut_bytes > 0
            && (frozen_fold_bytes as f64)
                > self.resegment_when_frozen_folds_exceed * global_cut_bytes as f64
    }

    /// Resolve the whole-operation memory limit against host headroom and divide
    /// across an explicit CPU-bounded thread count. Neither argument may be zero.
    pub fn delta_budget(
        &self,
        available_threads: usize,
        host_memory_limit: u64,
    ) -> Result<DeltaBudget> {
        ensure!(
            available_threads > 0 && host_memory_limit > 0,
            "pack delta search needs CPU and memory headroom"
        );
        let memory = self
            .segment_delta_window_memory
            .as_u64()
            .min(host_memory_limit);
        ensure!(
            memory > 0,
            "pack delta-search memory budget must be positive"
        );
        let threads = if self.segment_threads == 0 {
            available_threads
        } else {
            self.segment_threads.min(available_threads)
        };
        let threads = threads.min(usize::try_from(memory).unwrap_or(usize::MAX));
        let divisor = u64::try_from(threads)?;
        Ok(DeltaBudget {
            threads,
            window_memory_per_thread: memory / divisor,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn defaults_validate_and_reject_obsolete_keys() {
        let config = PacksConfig::default();
        config.validate().unwrap();
        assert_eq!(config.target_bytes(), 2_147_483_648);
        for text in [
            "factor = 2",
            "trigger_bytes = \"1GiB\"",
            "retention_superseded = \"7d\"",
        ] {
            assert!(toml::from_str::<PacksConfig>(text).is_err());
        }
        for text in [
            "geometric_factor = 1",
            "fold_needs_at_least_packs = 1",
            "segment_max_bytes = \"100B\"",
            "segment_delta_window_memory = \"0B\"",
            "frozen_coverage_target = nan",
            "frozen_coverage_target = 1.1",
            "resegment_when_frozen_folds_exceed = inf",
            "lease_ttl = \"0s\"",
        ] {
            assert!(
                toml::from_str::<PacksConfig>(text)
                    .unwrap()
                    .validate()
                    .is_err(),
                "{text}"
            );
        }
    }
    #[test]
    fn folds_need_two_inputs_and_have_independent_size_count_age_arms() {
        let config = PacksConfig::default();
        let floor = 32 * 1024 * 1024;
        let mut inventory = FoldInventory {
            live_bytes: floor * 16,
            fresh_bytes: floor * 8,
            fresh_packs: 1,
            oldest_fresh_age: Duration::from_hours(48),
        };
        assert_eq!(config.fold_reason(&inventory, floor), None);
        inventory.fresh_packs = 2;
        assert_eq!(
            config.fold_reason(&inventory, floor),
            Some(FoldReason::Bytes)
        );
        inventory.fresh_bytes = 1;
        assert_eq!(config.fold_reason(&inventory, floor), Some(FoldReason::Age));
        inventory.oldest_fresh_age = Duration::ZERO;
        assert_eq!(config.fold_reason(&inventory, floor), None);
        inventory.fresh_packs = 16;
        assert_eq!(
            config.fold_reason(&inventory, floor),
            Some(FoldReason::Count)
        );
        assert_eq!(config.fold_byte_threshold(floor, floor), floor);
    }
    #[test]
    fn freeze_and_resegment_use_distinct_stability_triggers() {
        let config = PacksConfig::default();
        let floor = 32 * 1024 * 1024;
        assert_eq!(
            config.freeze_reason(floor - 1, Duration::from_hours(1000), floor),
            None
        );
        assert_eq!(
            config.freeze_reason(floor, Duration::from_hours(14 * 24), floor),
            Some(FreezeReason::Settled)
        );
        assert_eq!(
            config.freeze_reason(config.target_bytes(), Duration::ZERO, floor),
            Some(FreezeReason::Size)
        );
        assert!(!config.first_freeze_due(floor * 3, 0, floor));
        assert!(config.first_freeze_due(floor * 4, floor * 2, floor));
        assert!(!config.first_freeze_due(floor * 4, floor * 3, floor));
        assert!(!config.resegment_due(0, floor));
        assert!(!config.resegment_due(floor * 2, floor));
        assert!(config.resegment_due(floor * 2, floor + 1));
    }
    #[test]
    fn thread_memory_budget_is_whole_operation_and_never_zero() {
        let config = PacksConfig {
            segment_threads: 128,
            ..Default::default()
        };
        let budget = config.delta_budget(8, 1024).unwrap();
        assert_eq!(
            budget,
            DeltaBudget {
                threads: 8,
                window_memory_per_thread: 128
            }
        );
        let budget = config.delta_budget(8, 3).unwrap();
        assert_eq!(
            budget,
            DeltaBudget {
                threads: 3,
                window_memory_per_thread: 1
            }
        );
        assert!(config.delta_budget(0, 1024).is_err());
        assert!(config.delta_budget(8, 0).is_err());
    }
}
