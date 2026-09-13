//! Native v2 response framing. Coverage authority belongs to the caller; this
//! module makes subtraction and URL emission one operation on the native engine.
use std::collections::HashSet;
use tokio::io::{AsyncRead, AsyncWrite, AsyncWriteExt};

use crate::{GitError, LocalRepo, ObjectId, UploadPackRequest, pkt};

#[derive(Debug, Clone)]
pub struct PackfileUri {
    pub checksum: ObjectId,
    pub url: String,
    pub index: Option<IndexUri>,
}

#[derive(Debug, Clone)]
pub struct IndexUri {
    pub checksum: ObjectId,
    pub url: String,
}

/// Every root must have exact captured coverage in the complete offered pack set.
/// This transport type does not prove that graph obligation or authorize a URL.
#[derive(Debug, Clone)]
pub struct Selection {
    pub packs: Vec<PackfileUri>,
    pub roots: Vec<ObjectId>,
}

impl LocalRepo {
    /// Use only after native-engine dispatch and exact group/dependency selection.
    /// Have-only negotiation, shallow requests and unsupported filters stay dynamic.
    pub async fn upload_pack_with_uris<W: AsyncWrite + Unpin + Send>(
        &self,
        mut request: UploadPackRequest,
        selection: &Selection,
        mut writer: W,
    ) -> Result<(), GitError> {
        if selection.packs.is_empty()
            || selection.roots.is_empty()
            || request.wants.is_empty()
            || !request.done
            || !request.shallow.is_empty()
            || request.deepen.is_some()
            || request.deepen_since.is_some()
            || !request.deepen_not.is_empty()
            || request.filter.as_deref().is_some_and(|f| f != "blob:none")
        {
            return Err(GitError::InvalidInput(
                "URI selection requires a complete supported fetch".into(),
            ));
        }
        for pack in &selection.packs {
            let protocol = pack.url.split_once("://").map(|(p, _)| p);
            if pack.checksum.kind() != self.object_format().kind()
                || !matches!(protocol, Some("http" | "https"))
                || !request
                    .packfile_uris_protocols
                    .iter()
                    .any(|p| Some(p.as_str()) == protocol)
                || pack
                    .url
                    .bytes()
                    .any(|b| b.is_ascii_control() || b.is_ascii_whitespace())
                || pack.url.len() + pack.checksum.kind().len_in_hex() + 3 > pkt::MAX_PKT_DATA
            {
                return Err(GitError::InvalidInput(
                    "invalid or unnegotiated packfile URI".into(),
                ));
            }
            if let Some(index) = &pack.index
                && (!request.packfile_indexes
                    || index.checksum.kind() != pack.checksum.kind()
                    || !index
                        .url
                        .starts_with(&format!("{}://", protocol.unwrap_or_default()))
                    || index
                        .url
                        .bytes()
                        .any(|b| b.is_ascii_control() || b.is_ascii_whitespace())
                    || index.url.len() + 2 * pack.checksum.kind().len_in_hex() + 4
                        > pkt::MAX_PKT_DATA)
            {
                return Err(GitError::InvalidInput(
                    "invalid or unnegotiated index URI".into(),
                ));
            }
        }
        if selection
            .roots
            .iter()
            .any(|id| id.kind() != self.object_format().kind())
        {
            return Err(GitError::InvalidInput(
                "URI root object format mismatch".into(),
            ));
        }
        let real: HashSet<_> = request.haves.iter().copied().collect();
        let synthetic: HashSet<_> = selection
            .roots
            .iter()
            .filter(|id| !real.contains(*id))
            .map(ToString::to_string)
            .collect();
        for root in &selection.roots {
            if !request.haves.contains(root) {
                request.haves.push(*root);
            }
        }
        // Static packs are not installed yet when the client indexes this stream.
        request.thin_pack = false;
        // Upstream must not independently select packs outside our proof.
        request.packfile_uris_protocols.clear();
        request.packfile_indexes = false;
        let body = crate::build_v2_fetch_request(&request);
        let (mut source, sink) = tokio::io::duplex(64 * 1024);
        let native = self.upload_pack_raw(pkt::Protocol::V2, &body[..], sink);
        let splice = splice(
            &mut source,
            &mut writer,
            &selection.packs,
            &synthetic,
            request.sideband_all,
        );
        tokio::try_join!(native, splice)?;
        Ok(())
    }
}

async fn line<W: AsyncWrite + Unpin>(
    writer: &mut W,
    data: &[u8],
    sideband: bool,
) -> Result<(), GitError> {
    if sideband {
        let mut payload = Vec::with_capacity(data.len() + 1);
        payload.push(1);
        payload.extend_from_slice(data);
        pkt::write_pkt_line(writer, &payload).await
    } else {
        pkt::write_pkt_line(writer, data).await
    }
}

async fn splice<R: AsyncRead + Unpin, W: AsyncWrite + Unpin>(
    source: &mut R,
    writer: &mut W,
    packs: &[PackfileUri],
    synthetic: &HashSet<String>,
    sideband: bool,
) -> Result<(), GitError> {
    while let Some(packet) = pkt::read_pkt_line(source).await? {
        match packet {
            pkt::PktLine::Data(data) => {
                let payload = if sideband {
                    match data.split_first() {
                        Some((1, rest)) => rest,
                        Some((2 | 3, _)) => {
                            pkt::write_pkt_line(writer, &data).await?;
                            continue;
                        }
                        _ => return Err(GitError::Protocol("invalid response sideband".into())),
                    }
                } else {
                    &data[..]
                };
                if let Some(ack) = payload.strip_prefix(b"ACK ")
                    && std::str::from_utf8(ack).is_ok_and(|oid| synthetic.contains(oid.trim_end()))
                {
                    continue;
                }
                if payload == b"packfile\n" {
                    line(writer, b"packfile-uris\n", sideband).await?;
                    for pack in packs {
                        line(
                            writer,
                            format!("{} {}\n", pack.checksum, pack.url).as_bytes(),
                            sideband,
                        )
                        .await?;
                    }
                    pkt::write_delim(writer).await?;
                    if packs.iter().any(|p| p.index.is_some()) {
                        line(writer, b"packfile-indexes\n", sideband).await?;
                        for pack in packs {
                            if let Some(index) = &pack.index {
                                line(
                                    writer,
                                    format!("{} {} {}\n", pack.checksum, index.checksum, index.url)
                                        .as_bytes(),
                                    sideband,
                                )
                                .await?;
                            }
                        }
                        pkt::write_delim(writer).await?;
                    }
                    pkt::write_pkt_line(writer, &data).await?;
                    // Pack bytes already have their native sideband framing.
                    tokio::io::copy(source, writer).await?;
                    writer.flush().await?;
                    return Ok(());
                }
                pkt::write_pkt_line(writer, &data).await?;
            }
            pkt::PktLine::Delim => pkt::write_delim(writer).await?,
            pkt::PktLine::Flush | pkt::PktLine::ResponseEnd => {
                return Err(GitError::Protocol(
                    "native response ended without selected URI delivery".into(),
                ));
            }
        }
    }
    Err(GitError::Protocol(
        "truncated native response before packfile".into(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn splice_preserves_native_bytes_and_only_removes_synthetic_acknowledgements() {
        for sideband in [false, true] {
            let oid = ObjectId::from_hex(b"1111111111111111111111111111111111111111").unwrap();
            let packs = [PackfileUri {
                checksum: oid,
                url: "https://example.invalid/repo/packfiles/one.pack".into(),
                index: None,
            }];
            let mut input = Vec::new();
            for data in [
                "acknowledgments\n",
                "ACK 1111111111111111111111111111111111111111\n",
                "ACK 2222222222222222222222222222222222222222\n",
                "ready\n",
            ] {
                line(&mut input, data.as_bytes(), sideband).await.unwrap();
            }
            pkt::encode_delim(&mut input);
            line(&mut input, b"packfile\n", sideband).await.unwrap();
            let mut pack_bytes = Vec::new();
            pkt::encode_data(&mut pack_bytes, b"\x01PACK\0\xff\n");
            pkt::encode_flush(&mut pack_bytes);
            input.extend_from_slice(&pack_bytes);
            let mut output = Vec::new();
            splice(
                &mut &input[..],
                &mut output,
                &packs,
                &HashSet::from([oid.to_string()]),
                sideband,
            )
            .await
            .unwrap();
            assert!(output.ends_with(&pack_bytes));
            let text = String::from_utf8_lossy(&output);
            assert!(!text.contains("ACK 111111"));
            assert!(text.contains("ACK 222222"));
            assert!(text.find("packfile-uris\n").unwrap() < text.find("packfile\n").unwrap());
        }
    }

    #[tokio::test]
    async fn no_pack_or_truncated_response_cannot_satisfy_uri_delivery() {
        for data in [b"0000".as_slice(), b"0002", b"000", b""] {
            assert!(
                splice(&mut &data[..], &mut Vec::new(), &[], &HashSet::new(), false)
                    .await
                    .is_err()
            );
        }
    }

    #[tokio::test]
    async fn optional_indexes_are_delimited_between_uris_and_pack_data() {
        let checksum = ObjectId::from_hex(b"1111111111111111111111111111111111111111").unwrap();
        let index_hash = ObjectId::from_hex(b"2222222222222222222222222222222222222222").unwrap();
        let packs = [PackfileUri {
            checksum,
            url: "https://example.invalid/one.pack".into(),
            index: Some(IndexUri {
                checksum: index_hash,
                url: "https://example.invalid/one.idx".into(),
            }),
        }];
        let mut source = Vec::new();
        line(&mut source, b"packfile\n", true).await.unwrap();
        pkt::encode_data(&mut source, b"\x01PACK");
        pkt::encode_flush(&mut source);
        let mut output = Vec::new();
        splice(&mut &source[..], &mut output, &packs, &HashSet::new(), true)
            .await
            .unwrap();
        let mut expected = Vec::new();
        line(&mut expected, b"packfile-uris\n", true).await.unwrap();
        line(
            &mut expected,
            format!("{checksum} https://example.invalid/one.pack\n").as_bytes(),
            true,
        )
        .await
        .unwrap();
        pkt::encode_delim(&mut expected);
        line(&mut expected, b"packfile-indexes\n", true)
            .await
            .unwrap();
        line(
            &mut expected,
            format!("{checksum} {index_hash} https://example.invalid/one.idx\n").as_bytes(),
            true,
        )
        .await
        .unwrap();
        pkt::encode_delim(&mut expected);
        expected.extend_from_slice(&source);
        assert_eq!(output, expected);
    }
}
