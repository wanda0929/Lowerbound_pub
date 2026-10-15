use crate::model::ModelId;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RigorStatus {
    Exploratory,
    LowerCertified,
    UpperCertified,
    LeanInstantiated,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SolverMetadata {
    pub name: String,
    pub version: String,
    pub settings: serde_json::Value,
    pub status: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ResultMetadata {
    pub schema: String,
    pub model: ModelId,
    pub formulation_hash: String,
    pub basis_hashes: Vec<String>,
    pub psd_blocks: Vec<u128>,
    pub solver: SolverMetadata,
    pub estimated_memory_bytes: u128,
    pub measured_peak_memory_bytes: Option<u128>,
    pub objective: Option<String>,
    pub residuals: serde_json::Value,
    pub provenance_manifest: String,
    pub rigor: RigorStatus,
}
