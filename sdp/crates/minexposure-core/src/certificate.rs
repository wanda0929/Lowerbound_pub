use crate::{Qsqrt2, Rational};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const FLOATING_GRAM_ENCODING: &str = "upper_triangle_column_major_unscaled";

/// Backend-neutral floating solution surface consumed by exactification lanes.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FloatingPsdBlock {
    pub side: usize,
    pub upper_triangle: Vec<f64>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FloatingPsdGrams {
    pub matrix_count: usize,
    pub encoding: String,
    pub blocks: Vec<FloatingPsdBlock>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FloatingDualSolution {
    /// Exact-model Liouville order; excludes any normalization constraint.
    pub dual_equality_multipliers: Vec<f64>,
    /// Some lifted lanes have a distinct terminal-mass normalization row.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dual_normalization_multiplier: Option<f64>,
    pub dual_psd_grams: FloatingPsdGrams,
}

impl FloatingDualSolution {
    pub fn validate(&self) -> Result<(), String> {
        if self.dual_psd_grams.encoding != FLOATING_GRAM_ENCODING {
            return Err(format!(
                "unsupported floating Gram encoding {:?}",
                self.dual_psd_grams.encoding
            ));
        }
        if self.dual_psd_grams.matrix_count != self.dual_psd_grams.blocks.len() {
            return Err("floating Gram matrix_count does not match blocks".into());
        }
        if self
            .dual_equality_multipliers
            .iter()
            .chain(self.dual_normalization_multiplier.iter())
            .any(|value| !value.is_finite())
        {
            return Err("floating dual multipliers must be finite".into());
        }
        for block in &self.dual_psd_grams.blocks {
            if block.upper_triangle.len() != block.side * (block.side + 1) / 2 {
                return Err("floating Gram triangle has the wrong length".into());
            }
            if block.upper_triangle.iter().any(|value| !value.is_finite()) {
                return Err("floating Gram entries must be finite".into());
            }
        }
        Ok(())
    }

    #[allow(clippy::needless_range_loop)]
    pub fn full_gram_matrices(&self) -> Result<Vec<Vec<Vec<f64>>>, String> {
        self.validate()?;
        Ok(self
            .dual_psd_grams
            .blocks
            .iter()
            .map(|block| {
                let mut matrix = vec![vec![0.0; block.side]; block.side];
                let mut position = 0;
                for column in 0..block.side {
                    for row in 0..=column {
                        let value = block.upper_triangle[position];
                        matrix[row][column] = value;
                        matrix[column][row] = value;
                        position += 1;
                    }
                }
                matrix
            })
            .collect())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ResidualPolicy {
    ExactZero,
    CostRelative,
    AdditiveFixedHorizon,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExactTransport {
    pub schema: String,
    pub formulation_hash: String,
    pub coefficient_field: String,
    pub claimed_bound: Rational,
    pub residual_policy: ResidualPolicy,
    pub residual_coefficients: BTreeMap<Vec<u16>, Qsqrt2>,
    pub residual_upper: Rational,
    pub gram_factor_hashes: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CheckReport {
    pub valid: bool,
    pub exact_identity: bool,
    pub residual_policy: ResidualPolicy,
    pub message: String,
}

pub fn check_transport(certificate: &ExactTransport, free_time: bool) -> CheckReport {
    let exact_identity = certificate
        .residual_coefficients
        .values()
        .all(|coefficient| *coefficient == Qsqrt2::ZERO);
    let valid_policy = !free_time
        || matches!(
            certificate.residual_policy,
            ResidualPolicy::ExactZero | ResidualPolicy::CostRelative
        );
    let residual_valid = match certificate.residual_policy {
        ResidualPolicy::ExactZero => exact_identity && certificate.residual_upper == Rational::ZERO,
        ResidualPolicy::CostRelative | ResidualPolicy::AdditiveFixedHorizon => {
            certificate.residual_upper.numerator >= 0
        }
    };
    let valid = valid_policy && residual_valid && !certificate.gram_factor_hashes.is_empty();
    let message = if !valid_policy {
        "additive residual is unsound for uncapped free time because zero-cost waiting permits unbounded occupation mass"
    } else if !residual_valid {
        "residual data do not satisfy the declared policy"
    } else if certificate.gram_factor_hashes.is_empty() {
        "no exact Gram-factor payload hashes are present"
    } else {
        "transport contract is internally valid; payload hashes must also pass provenance audit"
    };
    CheckReport {
        valid,
        exact_identity,
        residual_policy: certificate.residual_policy,
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_and_expands_shared_floating_dual_encoding() {
        let solution = FloatingDualSolution {
            dual_equality_multipliers: vec![1.0, -2.0],
            dual_normalization_multiplier: Some(3.0),
            dual_psd_grams: FloatingPsdGrams {
                matrix_count: 1,
                encoding: FLOATING_GRAM_ENCODING.into(),
                blocks: vec![FloatingPsdBlock {
                    side: 2,
                    upper_triangle: vec![1.0, 2.0, 3.0],
                }],
            },
        };
        assert_eq!(
            solution.full_gram_matrices().unwrap(),
            vec![vec![vec![1.0, 2.0], vec![2.0, 3.0]]]
        );
    }

    #[test]
    fn rejects_additive_free_time_residual() {
        let c = ExactTransport {
            schema: "minexposure/certificate-v1".into(),
            formulation_hash: "sha256:x".into(),
            coefficient_field: "Q".into(),
            claimed_bound: Rational::ONE,
            residual_policy: ResidualPolicy::AdditiveFixedHorizon,
            residual_coefficients: BTreeMap::new(),
            residual_upper: Rational::new(1, 1_000_000),
            gram_factor_hashes: vec!["sha256:x".into()],
        };
        assert!(!check_transport(&c, true).valid);
        assert!(check_transport(&c, false).valid);
    }
}
