use crate::SCHEMA_VERSION;
use crate::estimate::{Estimate, estimate};
use crate::model::{ModelId, RelaxationOrder};
use crate::monomial::{basis_hash, monomials};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssemblyKind {
    OccupationPrimal,
    HjbDual,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Assembly {
    pub schema: &'static str,
    pub kind: AssemblyKind,
    pub model: ModelId,
    pub order: RelaxationOrder,
    pub occupation_basis_hash: String,
    pub terminal_basis_hash: Option<String>,
    pub liouville_test_basis_hash: String,
    pub formulation_hash: String,
    pub estimate: Estimate,
    pub convention: &'static str,
}

pub fn assemble(model: ModelId, r: u8, kind: AssemblyKind) -> Result<Assembly, String> {
    if model == ModelId::StationaryTorusHausdorffSplit {
        return Err(
            "stationary_torus_hausdorff_split assembly requires an exact --knots grid".into(),
        );
    }
    let estimate = estimate(model, r)?;
    let order = estimate.order.clone();
    if matches!(
        model,
        ModelId::StationaryTorus | ModelId::StationaryTorusStrengthened
    ) {
        let exact = crate::stationary_torus::structure(r)?;
        let hash_input = if model == ModelId::StationaryTorusStrengthened {
            serde_json::json!({
                "schema": SCHEMA_VERSION,
                "kind": kind,
                "scientific_formulation_hash": exact.formulation_hash,
                "strengthening": "cost-weighted-moment-caps-147/50-v1",
            })
        } else {
            // Keep the source-parity lane's established assembly hash intact.
            serde_json::json!({
                "schema": SCHEMA_VERSION,
                "kind": kind,
                "scientific_formulation_hash": exact.formulation_hash,
            })
        };
        return Ok(Assembly {
            schema: SCHEMA_VERSION,
            kind,
            model,
            order,
            occupation_basis_hash: exact.basis_hash,
            terminal_basis_hash: None,
            liouville_test_basis_hash: exact.liouville_basis_hash,
            formulation_hash: format!(
                "sha256:{:x}",
                Sha256::digest(serde_json::to_vec(&hash_input).expect("assembly hash serializes"))
            ),
            estimate,
            convention: if model == ModelId::StationaryTorusStrengthened {
                "stationary complex mixed moments; source quotient and symmetry; zero-cost facial kernel; exact 147/50 cost-weighted moment caps"
            } else {
                "stationary complex mixed moments; degree=2r; U(1)xU(1) charge blocks; reflection realification; exact sphere/control quotient; zero-cost facial kernel"
            },
        });
    }
    if model == ModelId::StationaryTorusSharedControlLift {
        let exact = crate::shared_control_lift::assemble(r)?.structure;
        let basis_hash = format!(
            "sha256:{:x}",
            Sha256::digest(
                serde_json::to_vec(&exact).expect("shared-control structure serializes")
            )
        );
        let hash_input = serde_json::json!({
            "schema": SCHEMA_VERSION,
            "kind": kind,
            "model": model,
            "structure": exact,
        });
        return Ok(Assembly {
            schema: SCHEMA_VERSION,
            kind,
            model,
            order,
            occupation_basis_hash: basis_hash.clone(),
            terminal_basis_hash: None,
            liouville_test_basis_hash: basis_hash,
            formulation_hash: format!(
                "sha256:{:x}",
                Sha256::digest(serde_json::to_vec(&hash_input).expect("assembly hash serializes"))
            ),
            estimate,
            convention: "standalone reflection-realified shared-control invariant occupation lift; exploratory",
        });
    }
    if model == ModelId::StationaryTorusHausdorffLift {
        let exact = crate::stationary_hausdorff::structure(r)?;
        let hash_input = serde_json::json!({
            "schema": SCHEMA_VERSION,
            "kind": kind,
            "scientific_formulation_hash": exact.formulation_hash,
        });
        return Ok(Assembly {
            schema: SCHEMA_VERSION,
            kind,
            model,
            order,
            occupation_basis_hash: exact.occupation_basis_hash,
            terminal_basis_hash: Some(exact.terminal_basis_hash),
            liouville_test_basis_hash: exact.liouville_basis_hash,
            formulation_hash: format!(
                "sha256:{:x}",
                Sha256::digest(serde_json::to_vec(&hash_input).expect("assembly hash serializes"))
            ),
            estimate,
            convention: "stationary complex mixed state-cost moments; x=C/(2935887/1000000); degree=2r; terminal x moments; occupation and terminal M_r plus x(1-x) M_(r-1); exact-zero full-localizer faces plus diagonal certificate blocks",
        });
    }
    let model_spec = crate::model::model(model);
    let occupation_basis = monomials(
        usize::from(model_spec.occupation_variables),
        order.maximum_moment_degree.into(),
    );
    let terminal_basis_hash = (model_spec.terminal_variables > 0).then(|| {
        basis_hash(&monomials(
            usize::from(model_spec.terminal_variables),
            order.maximum_moment_degree.into(),
        ))
    });
    let occupation_basis_hash = basis_hash(&occupation_basis);
    let liouville_test_basis_hash = basis_hash(&monomials(
        usize::from(model_spec.occupation_variables),
        order.liouville_test_degree.into(),
    ));
    let hash_input = serde_json::json!({
        "schema": SCHEMA_VERSION,
        "kind": kind,
        "model": model_spec,
        "order": order,
        "occupation_basis_hash": occupation_basis_hash,
        "terminal_basis_hash": terminal_basis_hash,
        "liouville_test_basis_hash": liouville_test_basis_hash,
        "normalization": "graded_total_degree_then_ascending_lex",
    });
    let formulation_hash = format!(
        "sha256:{:x}",
        Sha256::digest(serde_json::to_vec(&hash_input).expect("assembly hash serializes"))
    );
    Ok(Assembly {
        schema: SCHEMA_VERSION,
        kind,
        model,
        order,
        occupation_basis_hash,
        terminal_basis_hash,
        liouville_test_basis_hash,
        formulation_hash,
        estimate,
        convention: "moment degree=2r; Gram degree=r; Liouville/value degree=2r-1; disk localizer degree=r-1",
    })
}

impl PartialEq for Assembly {
    fn eq(&self, other: &Self) -> bool {
        self.formulation_hash == other.formulation_hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primal_and_dual_share_bases_but_not_formulation_hash() {
        let p = assemble(ModelId::FixedRayL2, 2, AssemblyKind::OccupationPrimal).unwrap();
        let d = assemble(ModelId::FixedRayL2, 2, AssemblyKind::HjbDual).unwrap();
        assert_eq!(p.occupation_basis_hash, d.occupation_basis_hash);
        assert_ne!(p.formulation_hash, d.formulation_hash);
        assert_eq!(
            p,
            assemble(ModelId::FixedRayL2, 2, AssemblyKind::OccupationPrimal).unwrap()
        );
    }

    #[test]
    fn strengthened_torus_has_a_separate_hash_without_changing_the_source_hash() {
        let source = assemble(ModelId::StationaryTorus, 2, AssemblyKind::OccupationPrimal).unwrap();
        let strengthened = assemble(
            ModelId::StationaryTorusStrengthened,
            2,
            AssemblyKind::OccupationPrimal,
        )
        .unwrap();
        assert_eq!(
            source.occupation_basis_hash,
            strengthened.occupation_basis_hash
        );
        assert_ne!(source.formulation_hash, strengthened.formulation_hash);
    }
}
