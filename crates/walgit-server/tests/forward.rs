//! A buffered push is replayable only when the broker never received it.
mod harness;
use harness::{Server, TestRepo, git_in};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn ambiguous_delivery_and_gateway_responses_never_publish_locally() -> anyhow::Result<()> {
    let writer = Server::start().await?;
    writer.put_repo("o", "forward").await?;
    let source = TestRepo::synthetic(1, 1)?;
    git_in(
        &source,
        &["push", "-q", &writer.repo_url("o", "forward"), "main"],
    )?;
    let tip = git_in(&source, &["rev-parse", "HEAD"])?;
    let initial_log = writer.read_log("o", "forward").await?;
    for (name, reply, expected) in [
        ("lost", "", 502),
        (
            "gateway",
            "HTTP/1.1 503 Service Unavailable\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",
            503,
        ),
        (
            "redirect",
            "HTTP/1.1 307 Temporary Redirect\r\nLocation: http://127.0.0.1:1/\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",
            307,
        ),
    ] {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let broker = tokio::spawn(async move {
            let (mut stream, _) = listener.accept().await?;
            let mut received = Vec::new();
            loop {
                received.push(stream.read_u8().await?);
                // The forwarding stream uses HTTP/1 chunked transfer. Wait for
                // the entire body before dropping or rejecting the response.
                if received.ends_with(b"\r\n0\r\n\r\n") {
                    break;
                }
                anyhow::ensure!(received.len() < 16384, "unexpected forwarding body");
            }
            stream.write_all(reply.as_bytes()).await?;
            stream.shutdown().await?;
            Ok::<_, anyhow::Error>(received)
        });
        let front = writer
            .start_sibling_with(|cfg| {
                cfg.wal.push_broker_url = Some(format!("http://{address}"));
            })
            .await?;
        let command = format!(
            "{} {} refs/heads/{name}\0report-status\n",
            "0".repeat(40),
            tip.trim()
        );
        let body = format!("{:04x}{command}0000", command.len() + 4);
        let response = tokio::time::timeout(
            std::time::Duration::from_secs(10),
            reqwest::Client::new()
                .post(format!(
                    "{}/git-receive-pack",
                    front.repo_url("o", "forward")
                ))
                .header("content-type", "application/x-git-receive-pack-request")
                .body(body)
                .send(),
        )
        .await??;
        assert_eq!(response.status().as_u16(), expected);
        let received = broker.await??;
        assert!(String::from_utf8_lossy(&received).contains(&format!("refs/heads/{name}")));
        assert_eq!(writer.read_log("o", "forward").await?, initial_log);
        assert!(
            !writer
                .ls_remote("o", "forward")
                .await?
                .contains(&format!("refs/heads/{name}"))
        );
    }
    Ok(())
}
