//! Which machine answered: kind (a serverless host vs the SSD host vs dev), its name,
//! revision and build. Shown in the UI footer and on `/readyz` so a user (or
//! an agent reading logs) can always tell *where* a response came from — the
//! hybrid topology (D20) makes that a first-class question.

use serde::Serialize;

#[derive(Serialize, Clone, Debug)]
pub struct InstanceInfo {
    /// `serverless` | `ssd` | `dev` (lower-case, stable; the UI colours by it).
    pub kind: &'static str,
    /// Human name: a serverless host service (`front`), ssd-host host (`ssd-1`), or hostname.
    pub name: String,
    /// serverless revision (`front-00061-abc`) or empty.
    pub revision: String,
    /// Short instance id (configured id or pid) to distinguish concurrent processes.
    pub instance: String,
    /// Build: crate version + git sha baked at build time when available.
    pub version: String,
    /// Roles this instance runs (`serve`, `maintain`, …).
    pub roles: Vec<String>,
    /// Maintainer disk class from config (`tmpfs` | `ssd`) — the practical ssd-host/a serverless host tell.
    pub disk: &'static str,
    /// Machine shape, human: a serverless host `8 vCPU · 32 GiB` (from the cgroup limits the
    /// container sees), the SSD host = the GCE machine type (`c3-standard-176-lssd`), dev = host cpus/mem.
    pub shape: String,
    pub cpus: usize,
    pub memory_bytes: u64,
}

fn cgroup_memory_max() -> Option<u64> {
    for p in [
        "/sys/fs/cgroup/memory.max",
        "/sys/fs/cgroup/memory/memory.limit_in_bytes",
    ] {
        if let Ok(s) = std::fs::read_to_string(p) {
            let s = s.trim();
            if s == "max" {
                continue;
            }
            if let Ok(v) = s.parse::<u64>() {
                // cgroup v1 reports a huge number when unlimited.
                if v < (1u64 << 60) {
                    return Some(v);
                }
            }
        }
    }
    None
}
fn meminfo_total() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/meminfo").ok()?;
    let line = s.lines().find(|l| l.starts_with("MemTotal:"))?;
    let kb: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kb * 1024)
}
fn cgroup_cpus() -> Option<usize> {
    // cgroup v2: "quota period"; v1: cpu.cfs_quota_us / cpu.cfs_period_us.
    if let Ok(s) = std::fs::read_to_string("/sys/fs/cgroup/cpu.max") {
        let mut it = s.split_whitespace();
        if let (Some(q), Some(p)) = (it.next(), it.next())
            && q != "max"
            && let (Ok(q), Ok(p)) = (q.parse::<f64>(), p.parse::<f64>())
            && p > 0.0
        {
            return Some((q / p).round().max(1.0) as usize);
        }
    }
    None
}
/// Machine type as resolved once by [`init_machine_type`]; unset until then, and
/// on every host that never probes (dev, tests, off GCP), which reads as `None`.
static MACHINE_TYPE: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();

const MACHINE_TYPE_URL: &str =
    "http://metadata.google.internal/computeMetadata/v1/instance/machine-type";

/// Resolve the GCE machine type once, at startup, off the request path
/// (principle VI: `info()` runs on tokio workers under every health probe).
///
/// Only the SSD host ever shows a machine type (`info()` puts it in the shape
/// line), so only the SSD host probes, as before; every other host sends
/// nothing. The whole probe is capped at 300 ms, so an SSD host that is not on
/// GCE waits at most that, once, before it starts serving.
pub async fn init_machine_type(cfg: &walgit_config::Config) {
    if !is_ssd_host(cfg) {
        return;
    }
    let _ = MACHINE_TYPE.set(fetch_machine_type().await);
}

/// The same reading of `WALGIT_INSTANCE_KIND` and `maintenance.disk` that
/// [`info`] uses to call a host `ssd`.
fn is_ssd_host(cfg: &walgit_config::Config) -> bool {
    match std::env::var("WALGIT_INSTANCE_KIND")
        .ok()
        .filter(|v| !v.is_empty())
        .as_deref()
    {
        Some("ssd") => true,
        Some("serverless" | "dev") => false,
        _ => cfg.maintenance.disk == walgit_config::MaintainerDisk::Ssd,
    }
}

/// One GET at the metadata server, 300 ms for the whole thing. The value comes
/// back as a path (`projects/1234/machineTypes/c3-standard-176-lssd`); the last
/// segment is the machine type, and an empty answer is no answer.
async fn fetch_machine_type() -> Option<String> {
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_millis(300))
        .build()
        .ok()?;
    let resp = client
        .get(MACHINE_TYPE_URL)
        .header("Metadata-Flavor", "Google")
        .send()
        .await
        .ok()?;
    if !resp.status().is_success() {
        return None;
    }
    let body = resp.text().await.ok()?;
    body.trim()
        .rsplit('/')
        .next()
        .map(std::string::ToString::to_string)
        .filter(|m| !m.is_empty())
}

/// The resolved machine type. A read of the cell and nothing else: handlers
/// never probe.
fn gce_machine_type() -> Option<String> {
    MACHINE_TYPE.get().cloned().flatten()
}
fn gib(b: u64) -> String {
    let g = b as f64 / (1u64 << 30) as f64;
    if g >= 10.0 {
        format!("{g:.0} GiB")
    } else {
        format!("{g:.1} GiB")
    }
}

pub fn info(cfg: &walgit_config::Config) -> InstanceInfo {
    let env = |k: &str| std::env::var(k).ok().filter(|v| !v.is_empty());
    let disk = match cfg.maintenance.disk {
        walgit_config::MaintainerDisk::Ssd => "ssd",
        walgit_config::MaintainerDisk::Tmpfs => "tmpfs",
    };
    // Explicit host description first, then infer only the storage class.
    let kind: &'static str = match env("WALGIT_INSTANCE_KIND").as_deref() {
        Some("ssd") => "ssd",
        Some("serverless") => "serverless",
        Some("dev") => "dev",
        _ if disk == "ssd" => "ssd",
        _ => "dev",
    };
    let name = env("WALGIT_INSTANCE_NAME")
        .or_else(|| cfg.maintenance.host.clone())
        .or_else(|| env("HOSTNAME"))
        .unwrap_or_else(|| "walgit".into());
    let revision = env("WALGIT_REVISION").unwrap_or_default();
    let instance = env("WALGIT_INSTANCE_ID").map_or_else(
        || std::process::id().to_string(),
        |i| {
            i.chars()
                .rev()
                .take(6)
                .collect::<String>()
                .chars()
                .rev()
                .collect()
        },
    );
    let version = match option_env!("WALGIT_BUILD_SHA") {
        Some(sha) if !sha.is_empty() => format!(
            "{}+{}",
            env!("CARGO_PKG_VERSION"),
            &sha[..sha.len().min(12)]
        ),
        _ => env!("CARGO_PKG_VERSION").to_string(),
    };
    let roles = if cfg.server.roles.is_empty() {
        vec!["all".to_string()]
    } else {
        cfg.server
            .roles
            .iter()
            .map(|r| format!("{r:?}").to_lowercase())
            .collect()
    };
    let cpus = cgroup_cpus()
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, std::num::NonZero::get));
    let memory_bytes = cgroup_memory_max().or_else(meminfo_total).unwrap_or(0);
    let shape = match kind {
        "ssd" => gce_machine_type().map_or_else(
            || format!("{cpus} vCPU · {}", gib(memory_bytes)),
            |m| format!("{m} · {cpus} vCPU · {}", gib(memory_bytes)),
        ),
        "serverless" => format!("a serverless host · {cpus} vCPU · {}", gib(memory_bytes)),
        _ => format!("{cpus} cpus · {}", gib(memory_bytes)),
    };
    InstanceInfo {
        kind,
        name,
        revision,
        instance,
        version,
        roles,
        disk,
        shape,
        cpus,
        memory_bytes,
    }
}

/// Value of the `Server` response header: who answered, at a glance —
/// `walgit/<version> (serverless; front-00061-abc/1f2e3d)` or
/// `walgit/<version> (ssd; ssd-1)` or `(dev; host)`. Computed once.
pub fn server_header(cfg: &walgit_config::Config) -> &'static str {
    static V: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    V.get_or_init(|| {
        let i = info(cfg);
        let who = if i.kind == "serverless" && !i.revision.is_empty() {
            format!("{}/{}", i.revision, i.instance)
        } else {
            i.name.clone()
        };
        // ASCII only (header value); strip anything odd.
        let clean: String = format!("walgit/{} ({}; {})", i.version, i.kind, who)
            .chars()
            .filter(|c| c.is_ascii() && !c.is_ascii_control())
            .collect();
        clean
    })
    .as_str()
}

#[cfg(test)]
mod tests {
    use super::{gce_machine_type, init_machine_type, is_ssd_host};

    /// A host that is not the SSD host never probes: no name to resolve, no
    /// network, nothing cached, so `info()` keeps the plain cpu/memory shape.
    #[tokio::test]
    async fn init_machine_type_probes_only_on_the_ssd_host() {
        if std::env::var("WALGIT_INSTANCE_KIND").as_deref() == Ok("ssd") {
            return; // This runner calls itself the SSD host: the probe is meant to run.
        }
        let cfg = walgit_config::Config::default(); // maintenance.disk = tmpfs
        assert!(!is_ssd_host(&cfg));
        let started = std::time::Instant::now();
        init_machine_type(&cfg).await;
        let took = started.elapsed();
        assert!(
            took < std::time::Duration::from_millis(100),
            "the metadata server was contacted from a non-SSD host (took {took:?})"
        );
        assert!(
            gce_machine_type().is_none(),
            "nothing should be cached when the probe never ran"
        );
    }
}
