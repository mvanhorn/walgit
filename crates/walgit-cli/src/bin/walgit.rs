//! `walgit` — the full CLI (serve | compact | repo | wal | synth | import | mirror | config).
fn main() -> anyhow::Result<()> {
    walgit_cli::main()
}
