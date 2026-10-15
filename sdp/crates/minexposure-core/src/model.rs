use serde::{Deserialize, Serialize};
use std::fmt;
use std::str::FromStr;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ModelId {
    ScalarL1,
    FixedRayL2,
    IdealCzFixed,
    IdealCzFree,
    FiniteCzFixedKappa,
    NotionDense,
    NotionQuotient,
    StationaryTorus,
    StationaryTorusHausdorffLift,
    StationaryTorusHausdorffSplit,
    StationaryTorusStrengthened,
    StationaryTorusSharedControlLift,
}

impl ModelId {
    pub const ALL: [Self; 12] = [
        Self::ScalarL1,
        Self::FixedRayL2,
        Self::IdealCzFixed,
        Self::IdealCzFree,
        Self::FiniteCzFixedKappa,
        Self::NotionDense,
        Self::NotionQuotient,
        Self::StationaryTorus,
        Self::StationaryTorusHausdorffLift,
        Self::StationaryTorusHausdorffSplit,
        Self::StationaryTorusStrengthened,
        Self::StationaryTorusSharedControlLift,
    ];
}

impl fmt::Display for ModelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            serde_json::to_value(self).unwrap().as_str().unwrap()
        )
    }
}

impl FromStr for ModelId {
    type Err = String;
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::ALL
            .into_iter()
            .find(|id| id.to_string() == value)
            .ok_or_else(|| format!("unknown model `{value}`"))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Variable {
    pub name: &'static str,
    pub role: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct RelaxationOrder {
    pub order: u8,
    pub maximum_moment_degree: u8,
    pub moment_matrix_degree: u8,
    pub liouville_test_degree: u8,
    pub disk_localizer_degree: Option<u8>,
}

impl RelaxationOrder {
    pub fn standard(order: u8) -> Result<Self, String> {
        if order == 0 {
            return Err("relaxation order must be positive".into());
        }
        Ok(Self {
            order,
            maximum_moment_degree: 2 * order,
            moment_matrix_degree: order,
            liouville_test_degree: 2 * order - 1,
            disk_localizer_degree: Some(order - 1),
        })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Model {
    pub id: ModelId,
    pub title: &'static str,
    pub occupation_variables: u8,
    pub terminal_variables: u8,
    pub variables: Vec<Variable>,
    pub coefficient_field: &'static str,
    pub time_semantics: &'static str,
    pub control_set: &'static str,
    pub cost: &'static str,
    pub terminal_set: &'static str,
    pub quotient: &'static str,
    pub symmetry: &'static str,
    pub facial_reduction: &'static str,
    pub provenance_lane: &'static str,
}

fn variables(names: &'static [&'static str], state_count: usize) -> Vec<Variable> {
    names
        .iter()
        .enumerate()
        .map(|(index, name)| Variable {
            name,
            role: if index < state_count {
                "state"
            } else {
                "control"
            },
        })
        .collect()
}

pub fn model(id: ModelId) -> Model {
    let (title, occ, end, field, time, control, cost, terminal, quotient, symmetry, face, lane) =
        match id {
            ModelId::ScalarL1 => (
                "scalar L1 bounded-control transfer",
                3,
                0,
                "Q",
                "fixed horizon",
                "interval",
                "absolute-state exposure",
                "fixed endpoint",
                "none",
                "sign symmetry recorded but not block reduced",
                "none",
                "time_bound",
            ),
            ModelId::FixedRayL2 => (
                "fixed-ray bounded-drive L2",
                8,
                2,
                "Q(sqrt(2))",
                "fixed horizon",
                "unit disk",
                "quadratic exposure",
                "terminal phase circle",
                "none",
                "fixed-ray involution",
                "none",
                "time_bound",
            ),
            ModelId::IdealCzFixed => (
                "ideal-blockade common-control CZ, fixed time",
                10,
                8,
                "Q(sqrt(2))",
                "fixed horizon",
                "shared unit disk",
                "Rydberg exposure",
                "CZ polynomial variety",
                "sphere ideals optional",
                "sector exchange and phase actions",
                "none",
                "time_bound / SittingSDP",
            ),
            ModelId::IdealCzFree | ModelId::NotionDense => (
                "ideal-blockade common-control CZ, free time (dense)",
                10,
                8,
                "Q(sqrt(2))",
                "stationary free time; occupation mass is not capped",
                "shared unit disk",
                "Rydberg exposure",
                "CZ polynomial variety",
                "sphere ideals represented as equalities",
                "sector exchange and phase actions",
                "zero-cost waiting remains; additive residuals are invalid",
                "SittingSDP",
            ),
            ModelId::FiniteCzFixedKappa => (
                "finite-blockade CZ at fixed kappa",
                12,
                10,
                "Q(sqrt(2))",
                "fixed kappa parameter cell",
                "shared unit disk",
                "Rydberg exposure",
                "finite-blockade CZ variety",
                "sphere ideals optional",
                "exchange symmetry",
                "none",
                "time_bound / Finite_blockade_pulse",
            ),
            ModelId::NotionQuotient => (
                "SittingSDP degree-preserving sphere quotient",
                10,
                8,
                "Q(sqrt(2))",
                "stationary free time; occupation mass is not capped",
                "shared unit disk",
                "Rydberg exposure",
                "explicit CZ equations",
                "degree-preserving sphere normal forms",
                "not block diagonalized",
                "zero-cost waiting remains",
                "SittingSDP",
            ),
            ModelId::StationaryTorus => (
                "fully reduced stationary torus",
                10,
                0,
                "Q(sqrt(2))",
                "active-time normalization; waiting arcs removed",
                "phase circle |u|=1",
                "|r1|^2/2 + |r2|^2/4",
                "fixed quotient point (1,0,-1,0)",
                "three unit-circle normal forms",
                "U(1)xU(1) charges plus reflection",
                "exact kernel of restriction to r1=r2=0",
                "uncommitted thread T-01a04c92 aggregate evidence; canonical regeneration pending original basis recovery",
            ),
            ModelId::StationaryTorusHausdorffLift => (
                "stationary torus with normalized cumulative-cost Hausdorff lift",
                11,
                1,
                "Q(sqrt(2))",
                "active-time normalization with cumulative cost x=C/(2935887/1000000)",
                "phase circle |u|=1 and 0<=x<=1",
                "|r1|^2/2 + |r2|^2/4",
                "fixed CZ quotient point with a terminal measure on x",
                "three unit-circle normal forms plus Hausdorff x localizers",
                "U(1)xU(1) charges plus reflection",
                "zero-cost kernel for moment blocks; exact-zero full x(1-x) localizer faces",
                "Finite_blockade_pulse jan22-cost-lifted-hausdorff-handoff@10ed9ad",
            ),
            ModelId::StationaryTorusHausdorffSplit => (
                "stationary torus with piecewise normalized cumulative-cost Hausdorff lift",
                11,
                1,
                "Q(sqrt(2))",
                "active-time normalization with exact rational cumulative-cost cells",
                "phase circle |u|=1 and local 0<=xi<=1 in every cost cell",
                "|r1|^2/2 + |r2|^2/4",
                "fixed CZ quotient point with one terminal measure per cost cell",
                "three unit-circle normal forms plus cellwise Hausdorff localizers",
                "U(1)xU(1) charges plus reflection; state-only interface moments",
                "cellwise zero-cost kernel; nonnegative one-way interface crossing flux",
                "exploratory cumulative-cost domain split; thread T-01a05601-9ca5-72fc-81b8-a7bab8bdca1d",
            ),
            ModelId::StationaryTorusStrengthened => (
                "stationary torus with cost-weighted moment caps",
                10,
                0,
                "Q(sqrt(2))",
                "active-time normalization; waiting arcs removed",
                "phase circle |u|=1",
                "|r1|^2/2 + |r2|^2/4",
                "fixed quotient point (1,0,-1,0)",
                "same three unit-circle normal forms; no terminal-ideal occupation quotient",
                "U(1)xU(1) charges plus reflection",
                "exact zero-cost kernel plus valid cost-weighted moment caps from C* < 147/50",
                "relaxation-strengthening lane; source-parity lane remains unchanged",
            ),
            ModelId::StationaryTorusSharedControlLift => (
                "singular-safe shared-control invariant lift",
                8,
                0,
                "Q(sqrt(2))",
                "active-time projected occupation; unrestricted finite duration",
                "shared-control contractions retain unit-amplitude phase",
                "x/2 + y/4",
                "fixed invariant points C=1 to C=-1 with x=y=J=0",
                "division-free invariant syzygies and boundary closures",
                "reflection-realified projected moments",
                "x(1-x), y(1-y) localizers",
                "Finite_blockade_pulse shared-control lift at 1131fe5; exploratory",
            ),
        };
    let occ: u8 = occ;
    let end: u8 = end;
    let variable_names: &[&str] = match id {
        ModelId::ScalarL1 => &["state", "abs_state", "control"],
        ModelId::FixedRayL2 => &[
            "gg_re", "gg_im", "w_re", "w_im", "rr_re", "rr_im", "u_re", "u_im",
        ],
        ModelId::IdealCzFixed
        | ModelId::IdealCzFree
        | ModelId::NotionDense
        | ModelId::NotionQuotient
        | ModelId::StationaryTorus
        | ModelId::StationaryTorusStrengthened => &[
            "g1_re", "g1_im", "r1_re", "r1_im", "g2_re", "g2_im", "r2_re", "r2_im", "u_re", "u_im",
        ],
        ModelId::StationaryTorusHausdorffLift | ModelId::StationaryTorusHausdorffSplit => &[
            "g1_re",
            "g1_im",
            "r1_re",
            "r1_im",
            "g2_re",
            "g2_im",
            "r2_re",
            "r2_im",
            "normalized_cumulative_cost",
            "u_re",
            "u_im",
        ],
        ModelId::StationaryTorusSharedControlLift => &["x", "y", "C", "J", "p", "q", "m", "n"],
        ModelId::FiniteCzFixedKappa => &[
            "g1_re", "g1_im", "r1_re", "r1_im", "g2_re", "g2_im", "w_re", "w_im", "rr_re", "rr_im",
            "u_re", "u_im",
        ],
    };
    let state_count = match id {
        ModelId::ScalarL1 => 2,
        ModelId::StationaryTorusSharedControlLift => 4,
        _ => usize::from(occ.saturating_sub(2)),
    };
    Model {
        id,
        title,
        occupation_variables: occ,
        terminal_variables: end,
        variables: variables(variable_names, state_count),
        coefficient_field: field,
        time_semantics: time,
        control_set: control,
        cost,
        terminal_set: terminal,
        quotient,
        symmetry,
        facial_reduction: face,
        provenance_lane: lane,
    }
}
