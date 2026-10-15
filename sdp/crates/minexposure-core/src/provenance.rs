use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Artifact {
    pub source_repository: String,
    pub source_commit: String,
    pub source_path: String,
    pub imported_path: PathBuf,
    pub bytes: u64,
    pub sha256: String,
    pub dirty_at_source: bool,
    pub classification: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct AuditFinding {
    pub path: PathBuf,
    pub valid: bool,
    pub detail: String,
}

pub fn sha256_file(path: &Path) -> std::io::Result<(u64, String)> {
    let bytes = fs::read(path)?;
    Ok((bytes.len() as u64, format!("{:x}", Sha256::digest(&bytes))))
}

pub fn audit(root: &Path, artifacts: &[Artifact]) -> Vec<AuditFinding> {
    artifacts
        .iter()
        .map(|artifact| {
            let path = root.join(&artifact.imported_path);
            match sha256_file(&path) {
                Ok((bytes, hash)) if bytes == artifact.bytes && hash == artifact.sha256 => {
                    AuditFinding {
                        path: artifact.imported_path.clone(),
                        valid: true,
                        detail: "size and SHA-256 match".into(),
                    }
                }
                Ok((bytes, hash)) => AuditFinding {
                    path: artifact.imported_path.clone(),
                    valid: false,
                    detail: format!(
                        "expected {} bytes {} but found {bytes} bytes {hash}",
                        artifact.bytes, artifact.sha256
                    ),
                },
                Err(error) => AuditFinding {
                    path: artifact.imported_path.clone(),
                    valid: false,
                    detail: error.to_string(),
                },
            }
        })
        .collect()
}
