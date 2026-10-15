use super::split::semidefinite_ldl_minimum;
use super::{
    BigQsqrt2, ExactAuditError, ExactDualCertificate, ParsedGram, ScalarParser, add_assign,
    parse_matrix, sub_assign,
};
use crate::stationary_hausdorff::{
    EXPOSURE_UPPER, ExactCertificateModel, ExactGramShiftMetadata, HausdorffBasisBound,
    HausdorffGramFamily, HausdorffLocalizer, exact_certificate_model, structure,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const SHIFTED_HAUSDORFF_SCHEMA_V1: &str =
    "minexposure/jan22-cost-lifted-shifted-exact-dual-q-v1";
pub const SHIFTED_SALVAGE_FAILURE_SCHEMA_V1: &str =
    "minexposure/jan22-cost-lifted-shifted-salvage-failure-v1";
const ORIGINAL_HAUSDORFF_SCHEMA_V1: &str = "jan22-cost-lifted-exact-dual-q-v1";
const TRANSFORM_ORIENTATION_V1: &str =
    "gram_coordinate_i=sum_j(transform_rows[i][j].coefficient*basis_monomial_j)";
const EXACT_SHIFT_BISECTION_STEPS: usize = 15;

type EncodedMatrix = Vec<Vec<String>>;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ShiftedBoundKind {
    OccupationCostRelative,
    TerminalAdditive,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ShiftedTransformEntry {
    pub basis_index: usize,
    pub coefficient: i64,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ShiftedBlockDerivation {
    pub block_index: usize,
    pub family: HausdorffGramFamily,
    pub gram_side: usize,
    pub basis_size: usize,
    pub basis_bound: HausdorffBasisBound,
    pub transform_orientation: String,
    pub transform_rows: Vec<Vec<ShiftedTransformEntry>>,
    pub localizer: HausdorffLocalizer,
    pub localizer_supremum: String,
    /// Per basis monomial: `|z_j|^2 <= value*c` for occupation, or
    /// `|z_j|^2 <= value` for terminal. `None` marks a nonzero zero-cost face.
    pub basis_squared_bounds: Vec<Option<String>>,
    pub coordinate_bounds: Vec<Option<String>>,
    pub bound_kind: ShiftedBoundKind,
    /// `None` is mandatory when any occupation coordinate has no finite bound.
    pub block_bound: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ShiftedGramBlock {
    pub derivation: ShiftedBlockDerivation,
    /// Exactly zero for an originally PSD block; exactly positive for a failing block.
    pub delta: String,
}

/// Sound shift-and-discount wrapper around the pinned monolithic Hausdorff certificate.
/// The embedded exact identity is reconstructed before any shift is considered.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ShiftedExactDualCertificate {
    pub schema: String,
    pub formulation_hash: String,
    pub original: ExactDualCertificate,
    pub blocks: Vec<ShiftedGramBlock>,
    pub total_occupation_multiplier: String,
    pub total_terminal_discount: String,
    pub discounted_bound: String,
    pub bound_target: String,
    #[serde(default)]
    pub provenance: Option<serde_json::Value>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ShiftedExactAuditReport {
    pub sign_convention: &'static str,
    pub coefficient_count: usize,
    pub nonzero_original_exact_residual_count: usize,
    pub original_exact_bound: String,
    pub gram_count: usize,
    pub original_psd_gram_count: usize,
    pub shifted_gram_count: usize,
    pub positive_definite_gram_count_after_shift: usize,
    pub semidefinite_gram_count_after_shift: usize,
    pub all_shifted_gram_matrices_exactly_positive_semidefinite: bool,
    pub minimum_nonzero_exact_ldl_pivot_after_shift: String,
    pub exact_total_occupation_multiplier: String,
    pub exact_total_terminal_discount: String,
    pub exact_discounted_bound: String,
    pub certified_bound: String,
    pub bound_margin: String,
    pub rigorous_bound: f64,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ExactShiftSearch {
    pub delta: String,
    pub bisection_steps: usize,
    pub exact_ldl_calls: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct ShiftedZeroCostCoordinate {
    pub coordinate_index: usize,
    pub zero_cost_basis_indices: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "reason", rename_all = "snake_case")]
pub enum ShiftedSalvageReason {
    NoFiniteCostRelativeBoundDerived {
        coordinates: Vec<ShiftedZeroCostCoordinate>,
    },
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ShiftedSalvageBlockRecord {
    pub block_index: usize,
    pub family: HausdorffGramFamily,
    pub original_exactly_psd: bool,
    pub required_delta: String,
    pub exact_ldl_calls: usize,
    pub bound_kind: ShiftedBoundKind,
    pub block_bound: Option<String>,
    pub salvageable: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure_reason: Option<ShiftedSalvageReason>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ShiftedSalvageFailureRecord {
    pub schema: String,
    pub status: String,
    pub order: u8,
    pub beta: String,
    pub formulation_hash: String,
    pub original_identity_exact: bool,
    pub blocks: Vec<ShiftedSalvageBlockRecord>,
    pub unsalvageable_blocks: Vec<usize>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
#[allow(clippy::large_enum_variant)]
pub enum ShiftedSalvageOutcome {
    Certified {
        certificate: ShiftedExactDualCertificate,
    },
    Unsalvageable {
        failure: ShiftedSalvageFailureRecord,
    },
}

#[derive(Debug, Error)]
pub enum ShiftedExactAuditError {
    #[error("unsupported shifted exact certificate schema {0:?}")]
    Schema(String),
    #[error("shifted certificate must embed {ORIGINAL_HAUSDORFF_SCHEMA_V1:?}, found {0:?}")]
    OriginalSchema(String),
    #[error("internal monolithic Hausdorff exact model error: {0}")]
    Model(String),
    #[error("shifted formulation hash {found:?} does not match regenerated hash {expected:?}")]
    FormulationHash { found: String, expected: String },
    #[error("shifted cost-lift exposure upper must be exactly 2935887/1000000")]
    ExposureUpper,
    #[error("wrong shifted block count: expected {expected}, found {found}")]
    BlockCount { expected: usize, found: usize },
    #[error("block {block} derivation metadata does not match the regenerated metadata")]
    Derivation { block: usize },
    #[error("original exact endpoint bound {bound} does not equal declared beta {beta}")]
    OriginalBound { bound: String, beta: String },
    #[error("originally PSD block {block} must have delta exactly zero")]
    UnexpectedShift { block: usize },
    #[error("originally non-PSD block {block} must have delta exactly positive")]
    MissingShift { block: usize },
    #[error("block {block} delta must be an exact nonnegative rational")]
    Delta { block: usize },
    #[error(
        "occupation block {block} coordinate {coordinate} is nonzero on the zero-cost face and has no finite cost-relative bound"
    )]
    UnsalvageableOccupation { block: usize, coordinate: usize },
    #[error("declared occupation multiplier {found} does not equal reconstructed {expected}")]
    OccupationMultiplier { found: String, expected: String },
    #[error("declared terminal discount {found} does not equal reconstructed {expected}")]
    TerminalDiscount { found: String, expected: String },
    #[error("declared discounted bound {found} does not equal reconstructed {expected}")]
    DiscountedBound { found: String, expected: String },
    #[error("certificate target {target} exceeds discounted bound; exact margin is {margin}")]
    TargetBound { target: String, margin: String },
    #[error("exact shift search requires a square, nonempty Gram matrix")]
    ShiftShape,
    #[error("exact shift search requires a finite floating minimum-eigenvalue seed")]
    ShiftSeed,
    #[error("exact shift search was requested for an already-PSD Gram")]
    AlreadyPsd,
    #[error("exact shift search could not find a passing rational bracket")]
    ShiftBracket,
    #[error(transparent)]
    Exact(#[from] ExactAuditError),
}

fn expected_derivation(
    block_index: usize,
    metadata: ExactGramShiftMetadata,
) -> ShiftedBlockDerivation {
    let transform_rows = metadata
        .transform_rows
        .iter()
        .map(|row| {
            row.iter()
                .map(|&(basis_index, coefficient)| ShiftedTransformEntry {
                    basis_index,
                    coefficient,
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let localizer_supremum = match metadata.localizer {
        HausdorffLocalizer::One => BigRational::one(),
        HausdorffLocalizer::XiOneMinusXi => BigRational::new(BigInt::one(), BigInt::from(4)),
    };
    let basis_squared_bounds = metadata
        .basis_cost_ratios
        .iter()
        .map(|ratio| {
            ratio.map(|value| {
                BigRational::new(
                    BigInt::from(value.numerator),
                    BigInt::from(value.denominator),
                )
                .to_string()
            })
        })
        .collect::<Vec<_>>();
    let coordinate_bounds = metadata
        .transform_rows
        .iter()
        .map(|row| {
            let mut l1 = BigInt::zero();
            let mut weighted = BigRational::zero();
            for &(basis_index, coefficient) in row {
                let absolute = BigInt::from(coefficient.abs());
                if absolute.is_zero() {
                    continue;
                }
                let ratio = metadata.basis_cost_ratios[basis_index]?;
                l1 += &absolute;
                weighted += BigRational::new(
                    &absolute * BigInt::from(ratio.numerator),
                    BigInt::from(ratio.denominator),
                );
            }
            Some((BigRational::from_integer(l1) * weighted * &localizer_supremum).to_string())
        })
        .collect::<Vec<_>>();
    let block_bound = coordinate_bounds
        .iter()
        .cloned()
        .collect::<Option<Vec<_>>>()
        .map(|bounds| {
            bounds
                .iter()
                .map(|bound| bound.parse::<BigRational>().expect("generated rational"))
                .sum::<BigRational>()
                .to_string()
        });
    let bound_kind = match metadata.family {
        HausdorffGramFamily::TerminalMoment | HausdorffGramFamily::TerminalXiOneMinusXi => {
            ShiftedBoundKind::TerminalAdditive
        }
        HausdorffGramFamily::OccupationMoment
        | HausdorffGramFamily::OccupationXiOneMinusXi
        | HausdorffGramFamily::OccupationIntervalDiagonal => {
            ShiftedBoundKind::OccupationCostRelative
        }
    };
    ShiftedBlockDerivation {
        block_index,
        family: metadata.family,
        gram_side: transform_rows.len(),
        basis_size: metadata.basis_size,
        basis_bound: metadata.basis_bound,
        transform_orientation: TRANSFORM_ORIENTATION_V1.into(),
        transform_rows,
        localizer: metadata.localizer,
        localizer_supremum: localizer_supremum.to_string(),
        basis_squared_bounds,
        coordinate_bounds,
        bound_kind,
        block_bound,
    }
}

/// Regenerate every exact family, face transform, and rational supremum bound.
pub fn shifted_block_derivations(
    order: u8,
) -> Result<Vec<ShiftedBlockDerivation>, ShiftedExactAuditError> {
    let model = exact_certificate_model(order).map_err(ShiftedExactAuditError::Model)?;
    Ok(model
        .gram_shift_metadata()
        .into_iter()
        .enumerate()
        .map(|(block, metadata)| expected_derivation(block, metadata))
        .collect())
}

pub(super) fn exact_rational(value: &str) -> Result<BigRational, ExactAuditError> {
    let value = ScalarParser::parse(value)?;
    if !value.sqrt2.is_zero() {
        return Err(ExactAuditError::InvalidScalar(
            "expected an exact rational, found a nonzero sqrt(2) coefficient".into(),
        ));
    }
    Ok(value.rational)
}

/// Assemble the shifted schema and recompute both sound discount fields.
/// Audit remains a separate mandatory operation: construction does not trust or
/// classify the supplied shifts.
pub fn build_shifted_exact_certificate(
    original: ExactDualCertificate,
    shifts: Vec<String>,
) -> Result<ShiftedExactDualCertificate, ShiftedExactAuditError> {
    if original.schema != ORIGINAL_HAUSDORFF_SCHEMA_V1 {
        return Err(ShiftedExactAuditError::OriginalSchema(original.schema));
    }
    let derivations = shifted_block_derivations(original.order)?;
    if shifts.len() != derivations.len() {
        return Err(ShiftedExactAuditError::BlockCount {
            expected: derivations.len(),
            found: shifts.len(),
        });
    }
    let mut occupation_multiplier = BigRational::zero();
    let mut terminal_discount = BigRational::zero();
    let blocks = derivations
        .into_iter()
        .zip(shifts)
        .map(|(derivation, delta)| {
            let delta_value = exact_rational(&delta)?;
            if delta_value.is_negative() {
                return Err(ShiftedExactAuditError::Delta {
                    block: derivation.block_index,
                });
            }
            if delta_value.is_positive() {
                let bound = derivation.block_bound.as_deref().ok_or_else(|| {
                    ShiftedExactAuditError::UnsalvageableOccupation {
                        block: derivation.block_index,
                        coordinate: derivation
                            .coordinate_bounds
                            .iter()
                            .position(Option::is_none)
                            .expect("missing block bound has a missing coordinate"),
                    }
                })?;
                let contribution = delta_value * exact_rational(bound)?;
                match derivation.bound_kind {
                    ShiftedBoundKind::OccupationCostRelative => {
                        occupation_multiplier += contribution;
                    }
                    ShiftedBoundKind::TerminalAdditive => terminal_discount += contribution,
                }
            }
            Ok(ShiftedGramBlock { derivation, delta })
        })
        .collect::<Result<Vec<_>, ShiftedExactAuditError>>()?;
    let beta = ScalarParser::parse(&original.bound_target)?;
    let numerator = beta.sub(&BigQsqrt2::from_rational(terminal_discount.clone()));
    let denominator = BigQsqrt2::from_rational(BigRational::one() + &occupation_multiplier);
    let discounted = numerator.div(&denominator)?;
    let formulation_hash = structure(original.order)
        .map_err(ShiftedExactAuditError::Model)?
        .formulation_hash;
    Ok(ShiftedExactDualCertificate {
        schema: SHIFTED_HAUSDORFF_SCHEMA_V1.into(),
        formulation_hash,
        original,
        blocks,
        total_occupation_multiplier: occupation_multiplier.to_string(),
        total_terminal_discount: terminal_discount.to_string(),
        discounted_bound: discounted.to_string(),
        bound_target: discounted.to_string(),
        provenance: None,
    })
}

fn flattened_grams(certificate: &ExactDualCertificate) -> Vec<&EncodedMatrix> {
    certificate
        .occupation_grams
        .iter()
        .chain(&certificate.terminal_grams)
        .collect()
}

fn accumulate_gram(
    model: &ExactCertificateModel,
    block: usize,
    matrix: &ParsedGram,
    identity: &mut [BigQsqrt2],
) {
    let dimension = match matrix {
        ParsedGram::Rational(values) => values.len(),
        ParsedGram::Quadratic(values) => values.len(),
    };
    for row in 0..dimension {
        for column in row..dimension {
            if matrix.entry_is_zero(row, column) {
                continue;
            }
            model.for_each_gram_entry_coefficient(block, row, column, |position, coefficient| {
                sub_assign(
                    &mut identity[position],
                    &matrix.entry_times_small(row, column, coefficient),
                );
            });
            if row != column {
                model.for_each_gram_entry_coefficient(
                    block,
                    column,
                    row,
                    |position, coefficient| {
                        sub_assign(
                            &mut identity[position],
                            &matrix.entry_times_small(row, column, coefficient),
                        );
                    },
                );
            }
        }
    }
}

fn reconstruct_original_identity_and_bound(
    certificate: &ExactDualCertificate,
    model: &ExactCertificateModel,
    dimensions: &[usize],
) -> Result<(Vec<BigQsqrt2>, BigQsqrt2), ShiftedExactAuditError> {
    if certificate.equalities.len() != model.equalities.len() {
        return Err(ExactAuditError::EqualityCount {
            expected: model.equalities.len(),
            found: certificate.equalities.len(),
        }
        .into());
    }
    if certificate.occupation_grams.len() != model.occupation_gram_count()
        || certificate.terminal_grams.len() != 2
    {
        return Err(ExactAuditError::GramCount {
            expected: dimensions.len(),
            found: certificate.occupation_grams.len() + certificate.terminal_grams.len(),
        }
        .into());
    }
    let grams = flattened_grams(certificate);
    if grams.len() != dimensions.len() {
        return Err(ExactAuditError::GramCount {
            expected: dimensions.len(),
            found: grams.len(),
        }
        .into());
    }
    let multipliers = certificate
        .equalities
        .iter()
        .map(|value| ScalarParser::parse(value))
        .collect::<Result<Vec<_>, _>>()?;
    let normalization = ScalarParser::parse(
        certificate
            .normalization
            .as_deref()
            .ok_or(ExactAuditError::Normalization)?,
    )?;
    let mut bound = normalization.neg();
    let mut identity = vec![BigQsqrt2::zero(); model.coefficient_count()];
    for &(position, coefficient) in &model.cost {
        add_assign(&mut identity[position], &BigQsqrt2::from_small(coefficient));
    }
    add_assign(&mut identity[model.normalization_position], &normalization);
    for (multiplier, row) in multipliers.iter().zip(&model.equalities) {
        add_assign(
            &mut bound,
            &multiplier.mul(&BigQsqrt2::from_rational(BigRational::from_integer(
                BigInt::from(row.initial),
            ))),
        );
        for &(position, coefficient) in &row.coefficients {
            add_assign(&mut identity[position], &multiplier.mul_small(coefficient));
        }
    }
    for (block, encoded) in grams.iter().enumerate() {
        let matrix = parse_matrix(block, encoded, dimensions[block])?;
        accumulate_gram(model, block, &matrix, &mut identity);
    }
    Ok((identity, bound))
}

pub(super) fn add_diagonal_shift(matrix: &mut ParsedGram, delta: &BigRational) {
    match matrix {
        ParsedGram::Rational(values) => {
            for (index, row) in values.iter_mut().enumerate() {
                row[index] += delta;
            }
        }
        ParsedGram::Quadratic(values) => {
            for (index, row) in values.iter_mut().enumerate() {
                row[index].rational += delta;
            }
        }
    }
}

pub(super) fn exact_psd_result(
    block: usize,
    matrix: &mut ParsedGram,
) -> Result<(Option<BigQsqrt2>, bool), ExactAuditError> {
    semidefinite_ldl_minimum(block, matrix)
}

fn exact_psd_predicate(
    matrix: &ParsedGram,
    delta: &BigRational,
    calls: &mut usize,
) -> Result<bool, ShiftedExactAuditError> {
    let mut shifted = matrix.clone();
    add_diagonal_shift(&mut shifted, delta);
    *calls += 1;
    match exact_psd_result(0, &mut shifted) {
        Ok(_) => Ok(true),
        Err(ExactAuditError::GramPivot { .. }) => Ok(false),
        Err(error) => Err(error.into()),
    }
}

/// Find an exact positive rational diagonal shift. The floating eigenvalue only
/// seeds a bracket; every bracket and bisection decision is made by exact LDLᵀ.
pub fn exact_rational_gram_shift(
    encoded: &[Vec<String>],
    floating_minimum_eigenvalue: f64,
) -> Result<ExactShiftSearch, ShiftedExactAuditError> {
    if encoded.is_empty() || encoded.iter().any(|row| row.len() != encoded.len()) {
        return Err(ShiftedExactAuditError::ShiftShape);
    }
    if !floating_minimum_eigenvalue.is_finite() {
        return Err(ShiftedExactAuditError::ShiftSeed);
    }
    let matrix = parse_matrix(0, encoded, encoded.len())?;
    let mut calls = 1;
    let mut original = matrix.clone();
    match exact_psd_result(0, &mut original) {
        Ok(_) => return Err(ShiftedExactAuditError::AlreadyPsd),
        Err(ExactAuditError::GramPivot { .. }) => {}
        Err(error) => return Err(error.into()),
    }

    let minimum_seed = BigRational::new(BigInt::one(), BigInt::one() << 40_u32);
    let seed = BigRational::from_float(floating_minimum_eigenvalue.abs())
        .ok_or(ShiftedExactAuditError::ShiftSeed)?;
    let mut upper = seed.max(minimum_seed);
    let mut bracketed = exact_psd_predicate(&matrix, &upper, &mut calls)?;
    for _ in 0..256 {
        if bracketed {
            break;
        }
        upper *= BigInt::from(2);
        bracketed = exact_psd_predicate(&matrix, &upper, &mut calls)?;
    }
    if !bracketed {
        return Err(ShiftedExactAuditError::ShiftBracket);
    }
    let mut lower = BigRational::zero();
    for _ in 0..EXACT_SHIFT_BISECTION_STEPS {
        let midpoint = (&lower + &upper) / BigInt::from(2);
        if exact_psd_predicate(&matrix, &midpoint, &mut calls)? {
            upper = midpoint;
        } else {
            lower = midpoint;
        }
    }
    Ok(ExactShiftSearch {
        delta: upper.to_string(),
        bisection_steps: EXACT_SHIFT_BISECTION_STEPS,
        exact_ldl_calls: calls,
    })
}

pub(super) fn floating_minimum_eigenvalue(matrix: &ParsedGram) -> Result<f64, ExactAuditError> {
    let dimension = match matrix {
        ParsedGram::Rational(values) => values.len(),
        ParsedGram::Quadratic(values) => values.len(),
    };
    let values = (0..dimension)
        .flat_map(|row| (0..dimension).map(move |column| (row, column)))
        .map(|(row, column)| match matrix {
            ParsedGram::Rational(values) => values[row][column].to_f64(),
            ParsedGram::Quadratic(values) => values[row][column].to_f64(),
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| {
            ExactAuditError::InvalidScalar(
                "exact Gram cannot be represented by a finite floating search seed".into(),
            )
        })?;
    let minimum = nalgebra::DMatrix::from_row_slice(dimension, dimension, &values)
        .symmetric_eigen()
        .eigenvalues
        .min();
    if !minimum.is_finite() {
        return Err(ExactAuditError::InvalidScalar(
            "exact Gram cannot be represented by a finite floating search seed".into(),
        ));
    }
    Ok(minimum)
}

/// Convert an identity-closed monolithic v1 candidate end-to-end. The original
/// value is consumed but never modified: all shifts live only in the wrapper.
/// Floating eigenvalues seed the search; exact LDL decides every shift.
pub fn salvage_exact_shifted_certificate(
    original: ExactDualCertificate,
) -> Result<ShiftedSalvageOutcome, ShiftedExactAuditError> {
    salvage_exact_shifted_certificate_inner(original)
}

/// End-to-end salvage with an explicit worker count for independent blocks.
pub fn salvage_exact_shifted_certificate_with_jobs(
    original: ExactDualCertificate,
    jobs: usize,
) -> Result<ShiftedSalvageOutcome, ShiftedExactAuditError> {
    if jobs == 0 {
        return Err(ExactAuditError::AuditJobs.into());
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|error| ExactAuditError::ThreadPool(error.to_string()))?
        .install(|| salvage_exact_shifted_certificate_inner(original))
}

fn salvage_exact_shifted_certificate_inner(
    original: ExactDualCertificate,
) -> Result<ShiftedSalvageOutcome, ShiftedExactAuditError> {
    if original.schema != ORIGINAL_HAUSDORFF_SCHEMA_V1 {
        return Err(ShiftedExactAuditError::OriginalSchema(
            original.schema.clone(),
        ));
    }
    let exposure = original
        .exposure_upper
        .as_deref()
        .ok_or(ShiftedExactAuditError::ExposureUpper)
        .and_then(|value| ScalarParser::parse(value).map_err(Into::into))?;
    if exposure != ScalarParser::parse(&EXPOSURE_UPPER.to_string())? {
        return Err(ShiftedExactAuditError::ExposureUpper);
    }
    let model = exact_certificate_model(original.order).map_err(ShiftedExactAuditError::Model)?;
    let dimensions = model.gram_dimensions();
    let (identity, bound) =
        reconstruct_original_identity_and_bound(&original, &model, &dimensions)?;
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if nonzero != 0 {
        return Err(ExactAuditError::Identity { count: nonzero }.into());
    }
    let beta = ScalarParser::parse(&original.bound_target)?;
    if bound != beta {
        return Err(ShiftedExactAuditError::OriginalBound {
            bound: bound.to_string(),
            beta: beta.to_string(),
        });
    }

    let derivations = shifted_block_derivations(original.order)?;
    let searches = flattened_grams(&original)
        .par_iter()
        .enumerate()
        .map(|(block, encoded)| {
            let matrix = parse_matrix(block, encoded, dimensions[block])?;
            let mut exact_check = matrix.clone();
            match exact_psd_result(block, &mut exact_check) {
                Ok(_) => Ok((true, "0".into(), 1_usize)),
                Err(ExactAuditError::GramPivot { .. }) => {
                    let seed = floating_minimum_eigenvalue(&matrix)?;
                    exact_rational_gram_shift(encoded, seed)
                        .map(|search| (false, search.delta, search.exact_ldl_calls + 1))
                }
                Err(error) => Err(error.into()),
            }
        })
        .collect::<Result<Vec<_>, ShiftedExactAuditError>>()?;
    let blocks = derivations
        .iter()
        .zip(&searches)
        .map(
            |(derivation, (original_exactly_psd, delta, exact_ldl_calls))| {
                let zero_cost_coordinates = if !original_exactly_psd
                    && derivation.bound_kind == ShiftedBoundKind::OccupationCostRelative
                {
                    derivation
                        .coordinate_bounds
                        .iter()
                        .enumerate()
                        .filter(|(_, bound)| bound.is_none())
                        .map(|(coordinate_index, _)| ShiftedZeroCostCoordinate {
                            coordinate_index,
                            zero_cost_basis_indices: derivation.transform_rows[coordinate_index]
                                .iter()
                                .filter(|entry| {
                                    derivation.basis_squared_bounds[entry.basis_index].is_none()
                                        && entry.coefficient != 0
                                })
                                .map(|entry| entry.basis_index)
                                .collect(),
                        })
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                let failure_reason = (!zero_cost_coordinates.is_empty()).then_some(
                    ShiftedSalvageReason::NoFiniteCostRelativeBoundDerived {
                        coordinates: zero_cost_coordinates,
                    },
                );
                ShiftedSalvageBlockRecord {
                    block_index: derivation.block_index,
                    family: derivation.family,
                    original_exactly_psd: *original_exactly_psd,
                    required_delta: delta.clone(),
                    exact_ldl_calls: *exact_ldl_calls,
                    bound_kind: derivation.bound_kind,
                    block_bound: derivation.block_bound.clone(),
                    salvageable: failure_reason.is_none(),
                    failure_reason,
                }
            },
        )
        .collect::<Vec<_>>();
    let unsalvageable_blocks = blocks
        .iter()
        .filter(|block| !block.salvageable)
        .map(|block| block.block_index)
        .collect::<Vec<_>>();
    if !unsalvageable_blocks.is_empty() {
        return Ok(ShiftedSalvageOutcome::Unsalvageable {
            failure: ShiftedSalvageFailureRecord {
                schema: SHIFTED_SALVAGE_FAILURE_SCHEMA_V1.into(),
                status: "unsalvageable".into(),
                order: original.order,
                beta: beta.to_string(),
                formulation_hash: structure(original.order)
                    .map_err(ShiftedExactAuditError::Model)?
                    .formulation_hash,
                original_identity_exact: true,
                blocks,
                unsalvageable_blocks,
            },
        });
    }
    let shifts = searches.into_iter().map(|(_, delta, _)| delta).collect();
    let certificate = build_shifted_exact_certificate(original, shifts)?;
    audit_shifted_exact_certificate(&certificate)?;
    Ok(ShiftedSalvageOutcome::Certified { certificate })
}

pub fn audit_shifted_exact_certificate(
    certificate: &ShiftedExactDualCertificate,
) -> Result<ShiftedExactAuditReport, ShiftedExactAuditError> {
    audit_shifted_exact_certificate_inner(certificate)
}

pub fn audit_shifted_exact_certificate_with_jobs(
    certificate: &ShiftedExactDualCertificate,
    jobs: usize,
) -> Result<ShiftedExactAuditReport, ShiftedExactAuditError> {
    if jobs == 0 {
        return Err(ExactAuditError::AuditJobs.into());
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|error| ExactAuditError::ThreadPool(error.to_string()))?
        .install(|| audit_shifted_exact_certificate_inner(certificate))
}

struct BlockAudit {
    shifted: bool,
    positive_definite: bool,
    minimum: Option<BigQsqrt2>,
    occupation_multiplier: BigRational,
    terminal_discount: BigRational,
}

fn audit_shifted_exact_certificate_inner(
    certificate: &ShiftedExactDualCertificate,
) -> Result<ShiftedExactAuditReport, ShiftedExactAuditError> {
    if certificate.schema != SHIFTED_HAUSDORFF_SCHEMA_V1 {
        return Err(ShiftedExactAuditError::Schema(certificate.schema.clone()));
    }
    let original = &certificate.original;
    if original.schema != ORIGINAL_HAUSDORFF_SCHEMA_V1 {
        return Err(ShiftedExactAuditError::OriginalSchema(
            original.schema.clone(),
        ));
    }
    let exposure = original
        .exposure_upper
        .as_deref()
        .ok_or(ShiftedExactAuditError::ExposureUpper)
        .and_then(|value| ScalarParser::parse(value).map_err(Into::into))?;
    if exposure != ScalarParser::parse(&EXPOSURE_UPPER.to_string())? {
        return Err(ShiftedExactAuditError::ExposureUpper);
    }
    let regenerated_structure = structure(original.order).map_err(ShiftedExactAuditError::Model)?;
    if certificate.formulation_hash != regenerated_structure.formulation_hash {
        return Err(ShiftedExactAuditError::FormulationHash {
            found: certificate.formulation_hash.clone(),
            expected: regenerated_structure.formulation_hash,
        });
    }
    let model = exact_certificate_model(original.order).map_err(ShiftedExactAuditError::Model)?;
    let dimensions = model.gram_dimensions();

    // This is intentionally first: salvage is valid only for a candidate that
    // already closes the unshifted coefficient identity exactly at beta.
    let (identity, original_bound) =
        reconstruct_original_identity_and_bound(original, &model, &dimensions)?;
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if nonzero != 0 {
        return Err(ExactAuditError::Identity { count: nonzero }.into());
    }
    let beta = ScalarParser::parse(&original.bound_target)?;
    if original_bound != beta {
        return Err(ShiftedExactAuditError::OriginalBound {
            bound: original_bound.to_string(),
            beta: beta.to_string(),
        });
    }

    let expected = shifted_block_derivations(original.order)?;
    if certificate.blocks.len() != expected.len() {
        return Err(ShiftedExactAuditError::BlockCount {
            expected: expected.len(),
            found: certificate.blocks.len(),
        });
    }
    for (block, (declared, regenerated)) in certificate.blocks.iter().zip(&expected).enumerate() {
        if declared.derivation != *regenerated {
            return Err(ShiftedExactAuditError::Derivation { block });
        }
    }

    let grams = flattened_grams(original);
    let audits = grams
        .par_iter()
        .zip(&certificate.blocks)
        .enumerate()
        .map(
            |(block, (encoded, declared))| -> Result<BlockAudit, ShiftedExactAuditError> {
                let matrix = parse_matrix(block, encoded, dimensions[block])?;
                let delta = exact_rational(&declared.delta)?;
                if delta.is_negative() {
                    return Err(ShiftedExactAuditError::Delta { block });
                }
                let mut original_check = matrix.clone();
                match exact_psd_result(block, &mut original_check) {
                    Ok((minimum, positive_definite)) => {
                        if !delta.is_zero() {
                            return Err(ShiftedExactAuditError::UnexpectedShift { block });
                        }
                        Ok(BlockAudit {
                            shifted: false,
                            positive_definite,
                            minimum,
                            occupation_multiplier: BigRational::zero(),
                            terminal_discount: BigRational::zero(),
                        })
                    }
                    Err(ExactAuditError::GramPivot { .. }) => {
                        if !delta.is_positive() {
                            return Err(ShiftedExactAuditError::MissingShift { block });
                        }
                        let mut shifted_matrix = matrix;
                        add_diagonal_shift(&mut shifted_matrix, &delta);
                        let (minimum, positive_definite) =
                            exact_psd_result(block, &mut shifted_matrix)?;
                        let bound =
                            declared.derivation.block_bound.as_deref().ok_or_else(|| {
                                ShiftedExactAuditError::UnsalvageableOccupation {
                                    block,
                                    coordinate: declared
                                        .derivation
                                        .coordinate_bounds
                                        .iter()
                                        .position(Option::is_none)
                                        .expect("missing block bound has a missing coordinate"),
                                }
                            })?;
                        let contribution = delta * exact_rational(bound)?;
                        let (occupation_multiplier, terminal_discount) =
                            match declared.derivation.bound_kind {
                                ShiftedBoundKind::OccupationCostRelative => {
                                    (contribution, BigRational::zero())
                                }
                                ShiftedBoundKind::TerminalAdditive => {
                                    (BigRational::zero(), contribution)
                                }
                            };
                        Ok(BlockAudit {
                            shifted: true,
                            positive_definite,
                            minimum,
                            occupation_multiplier,
                            terminal_discount,
                        })
                    }
                    Err(error) => Err(error.into()),
                }
            },
        )
        .collect::<Result<Vec<_>, _>>()?;

    let occupation_multiplier = audits
        .iter()
        .map(|audit| audit.occupation_multiplier.clone())
        .sum::<BigRational>();
    let terminal_discount = audits
        .iter()
        .map(|audit| audit.terminal_discount.clone())
        .sum::<BigRational>();
    let declared_occupation = exact_rational(&certificate.total_occupation_multiplier)?;
    if declared_occupation != occupation_multiplier {
        return Err(ShiftedExactAuditError::OccupationMultiplier {
            found: declared_occupation.to_string(),
            expected: occupation_multiplier.to_string(),
        });
    }
    let declared_terminal = exact_rational(&certificate.total_terminal_discount)?;
    if declared_terminal != terminal_discount {
        return Err(ShiftedExactAuditError::TerminalDiscount {
            found: declared_terminal.to_string(),
            expected: terminal_discount.to_string(),
        });
    }
    let numerator = beta.sub(&BigQsqrt2::from_rational(terminal_discount.clone()));
    let denominator = BigQsqrt2::from_rational(BigRational::one() + &occupation_multiplier);
    let discounted_bound = numerator.div(&denominator)?;
    let declared_discounted = ScalarParser::parse(&certificate.discounted_bound)?;
    if declared_discounted != discounted_bound {
        return Err(ShiftedExactAuditError::DiscountedBound {
            found: declared_discounted.to_string(),
            expected: discounted_bound.to_string(),
        });
    }
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let margin = numerator.sub(&target.mul(&denominator));
    if !margin.is_zero() && !margin.is_positive() {
        return Err(ShiftedExactAuditError::TargetBound {
            target: target.to_string(),
            margin: margin.to_string(),
        });
    }
    let rigorous_bound = target.to_f64().ok_or_else(|| {
        ExactAuditError::InvalidScalar(
            "certified bound cannot be represented as f64 for reporting".into(),
        )
    })?;
    let shifted_gram_count = audits.iter().filter(|audit| audit.shifted).count();
    let positive_definite_count = audits
        .iter()
        .filter(|audit| audit.positive_definite)
        .count();
    let minimum = audits
        .iter()
        .filter_map(|audit| audit.minimum.as_ref())
        .cloned()
        .reduce(|left, right| {
            if left.sub(&right).is_positive() {
                right
            } else {
                left
            }
        })
        .map_or_else(
            || "0 (all shifted Gram matrices exact zero)".into(),
            |value| value.to_string(),
        );
    Ok(ShiftedExactAuditReport {
        sign_convention: "original c + A^T lambda + n*terminal[0] - S^T G = 0; occupation trace <= K*c, terminal trace <= E, certify (beta-E)/(1+K)",
        coefficient_count: model.coefficient_count(),
        nonzero_original_exact_residual_count: 0,
        original_exact_bound: original_bound.to_string(),
        gram_count: dimensions.len(),
        original_psd_gram_count: dimensions.len() - shifted_gram_count,
        shifted_gram_count,
        positive_definite_gram_count_after_shift: positive_definite_count,
        semidefinite_gram_count_after_shift: dimensions.len() - positive_definite_count,
        all_shifted_gram_matrices_exactly_positive_semidefinite: true,
        minimum_nonzero_exact_ldl_pivot_after_shift: minimum,
        exact_total_occupation_multiplier: occupation_multiplier.to_string(),
        exact_total_terminal_discount: terminal_discount.to_string(),
        exact_discounted_bound: discounted_bound.to_string(),
        certified_bound: target.to_string(),
        bound_margin: margin.to_string(),
        rigorous_bound,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn zero_matrix(side: usize) -> EncodedMatrix {
        vec![vec!["0".into(); side]; side]
    }

    fn diagonal_operator(
        model: &ExactCertificateModel,
        block: usize,
        index: usize,
    ) -> BTreeMap<usize, BigQsqrt2> {
        let mut result = BTreeMap::new();
        model.for_each_gram_entry_coefficient(block, index, index, |position, coefficient| {
            add_assign(
                result.entry(position).or_insert_with(BigQsqrt2::zero),
                &BigQsqrt2::from_small(coefficient),
            );
        });
        result.retain(|_, coefficient| !coefficient.is_zero());
        result
    }

    fn weak_order_two_certificate() -> ExactDualCertificate {
        let order = 2;
        let model = exact_certificate_model(order).unwrap();
        let dimensions = model.gram_dimensions();
        let mut grams = dimensions
            .iter()
            .copied()
            .map(zero_matrix)
            .collect::<Vec<_>>();
        for &(cost_position, cost_coefficient) in &model.cost {
            let (block, gram_coefficient) = dimensions
                .iter()
                .enumerate()
                .filter(|(_, side)| **side == 1)
                .find_map(|(block, _)| {
                    let coefficients = diagonal_operator(&model, block, 0);
                    (coefficients.len() == 1 && coefficients.contains_key(&cost_position))
                        .then(|| (block, coefficients[&cost_position].clone()))
                })
                .expect("every running-cost coordinate has a one-dimensional SOS block");
            let value = BigQsqrt2::from_small(cost_coefficient)
                .div(&gram_coefficient)
                .unwrap();
            assert!(value.is_positive());
            grams[block][0][0] = value.to_string();
        }
        let terminal = grams.split_off(model.occupation_gram_count());
        let certificate = ExactDualCertificate {
            schema: ORIGINAL_HAUSDORFF_SCHEMA_V1.into(),
            order,
            bound_target: "0".into(),
            equalities: vec!["0".into(); model.equalities.len()],
            grams: Vec::new(),
            exposure_upper: Some(EXPOSURE_UPPER.to_string()),
            normalization: Some("0".into()),
            occupation_grams: grams,
            terminal_grams: terminal,
            residual_policy: None,
            residual_upper: None,
            formulation_hash: None,
            provenance: None,
        };
        let (identity, bound) =
            reconstruct_original_identity_and_bound(&certificate, &model, &dimensions).unwrap();
        assert!(identity.iter().all(BigQsqrt2::is_zero));
        assert!(bound.is_zero());
        certificate
    }

    fn add_rational(encoded: &mut String, value: &str) {
        *encoded = ScalarParser::parse(encoded)
            .unwrap()
            .add(&ScalarParser::parse(value).unwrap())
            .to_string();
    }

    fn add_failing_interval_diagonal(
        original: &mut ExactDualCertificate,
        require_finite_bound: bool,
    ) -> usize {
        let model = exact_certificate_model(original.order).unwrap();
        let metadata = model.gram_shift_metadata();
        let derivations = shifted_block_derivations(original.order).unwrap();
        let diagonal_block = metadata
            .iter()
            .enumerate()
            .find(|(block, metadata)| {
                metadata.family == HausdorffGramFamily::OccupationIntervalDiagonal
                    && original.occupation_grams[*block][0][0] == "0"
                    && derivations[*block].block_bound.is_some() == require_finite_bound
            })
            .map(|(block, _)| block)
            .expect("order two has both salvageable and zero-cost interval diagonals");
        let operator = diagonal_operator(&model, diagonal_block, 0);
        let (support_block, support_coordinate) = metadata
            .iter()
            .enumerate()
            .filter(|(_, block)| block.family == HausdorffGramFamily::OccupationXiOneMinusXi)
            .find_map(|(block, metadata)| {
                (0..metadata.transform_rows.len())
                    .find(|&coordinate| diagonal_operator(&model, block, coordinate) == operator)
                    .map(|coordinate| (block, coordinate))
            })
            .expect("every interval diagonal comes from a full interval block coordinate");
        add_rational(
            &mut original.occupation_grams[support_block][support_coordinate][support_coordinate],
            "1/1000",
        );
        original.occupation_grams[diagonal_block][0][0] = "-1/1000".into();
        let (identity, _) =
            reconstruct_original_identity_and_bound(original, &model, &model.gram_dimensions())
                .unwrap();
        assert!(identity.iter().all(BigQsqrt2::is_zero));
        diagonal_block
    }

    fn shifted_order_two_certificate() -> ShiftedExactDualCertificate {
        let mut original = weak_order_two_certificate();
        let shifted_block = add_failing_interval_diagonal(&mut original, true);
        let mut shifts = vec!["0".into(); shifted_block_derivations(2).unwrap().len()];
        shifts[shifted_block] = "1/1000".into();
        build_shifted_exact_certificate(original, shifts).unwrap()
    }

    #[test]
    fn regenerates_family_aware_supremum_formulas() {
        let blocks = shifted_block_derivations(2).unwrap();
        assert_eq!(blocks.len(), 27);
        assert_eq!(
            blocks
                .iter()
                .filter(|block| block.family == HausdorffGramFamily::OccupationMoment)
                .count(),
            13
        );
        assert!(blocks.iter().any(|block| {
            block.family == HausdorffGramFamily::OccupationIntervalDiagonal
                && block.basis_squared_bounds == vec![Some("2".into())]
                && block.block_bound.as_deref() == Some("1/2")
        }));
        assert!(blocks.iter().any(|block| {
            block.family == HausdorffGramFamily::OccupationIntervalDiagonal
                && block.basis_squared_bounds == vec![Some("4".into())]
                && block.block_bound.as_deref() == Some("1")
        }));
        assert!(blocks.iter().any(|block| {
            block.family == HausdorffGramFamily::OccupationIntervalDiagonal
                && block.basis_squared_bounds == vec![None]
                && block.block_bound.is_none()
        }));
        let terminal_moment = blocks
            .iter()
            .find(|block| block.family == HausdorffGramFamily::TerminalMoment)
            .unwrap();
        assert_eq!(terminal_moment.block_bound.as_deref(), Some("3"));
        let terminal_interval = blocks
            .iter()
            .find(|block| block.family == HausdorffGramFamily::TerminalXiOneMinusXi)
            .unwrap();
        assert_eq!(terminal_interval.block_bound.as_deref(), Some("1/2"));
    }

    #[test]
    fn order_six_known_failure_blocks_have_sound_cost_relative_classification() {
        let blocks = shifted_block_derivations(6).unwrap();
        assert_eq!(blocks[112].family, HausdorffGramFamily::OccupationMoment);
        assert_eq!(blocks[112].gram_side, 1);
        assert_eq!(blocks[112].basis_squared_bounds, vec![Some("2".into())]);
        assert_eq!(blocks[112].block_bound.as_deref(), Some("2"));

        assert_eq!(
            blocks[255].family,
            HausdorffGramFamily::OccupationIntervalDiagonal
        );
        assert_eq!(blocks[255].gram_side, 1);
        assert_eq!(blocks[255].basis_squared_bounds, vec![None]);
        assert_eq!(blocks[255].coordinate_bounds, vec![None]);
        assert!(blocks[255].block_bound.is_none());
    }

    #[test]
    fn float_seeded_shift_search_returns_only_an_exact_passing_rational() {
        let matrix = vec![vec!["-1".into(), "0".into()], vec!["0".into(), "2".into()]];
        let search = exact_rational_gram_shift(&matrix, -0.9).unwrap();
        let delta = exact_rational(&search.delta).unwrap();
        assert!(delta >= BigRational::one());
        assert_eq!(search.bisection_steps, 15);
        assert!((17..=19).contains(&search.exact_ldl_calls));
        let parsed = parse_matrix(0, &matrix, 2).unwrap();
        let mut calls = 0;
        assert!(exact_psd_predicate(&parsed, &delta, &mut calls).unwrap());
        assert_eq!(calls, 1);
    }

    #[test]
    fn shifted_audit_is_serial_parallel_identical_and_rejects_tampering() {
        let certificate = shifted_order_two_certificate();
        let shifted_block = certificate
            .blocks
            .iter()
            .position(|block| block.delta != "0")
            .unwrap();
        let serial = audit_shifted_exact_certificate_with_jobs(&certificate, 1).unwrap();
        let parallel = audit_shifted_exact_certificate_with_jobs(&certificate, 2).unwrap();
        assert_eq!(serial, parallel);
        assert_eq!(serial.shifted_gram_count, 1);
        assert_eq!(serial.original_exact_bound, "0");
        assert!(
            serial
                .exact_total_occupation_multiplier
                .parse::<BigRational>()
                .unwrap()
                .is_positive()
        );

        let mut tampered = certificate.clone();
        tampered.blocks[shifted_block].delta = "999/1000000".into();
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::Exact(
                ExactAuditError::GramPivot { .. }
            ))
        ));

        let mut tampered = certificate.clone();
        tampered.blocks[shifted_block].derivation.block_bound = Some("0".into());
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::Derivation { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(
            &mut tampered.original.occupation_grams[shifted_block][0][0],
            "1/1000000",
        );
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::Exact(
                ExactAuditError::Identity { .. }
            ))
        ));

        let mut tampered = certificate.clone();
        tampered.original.bound_target = "1".into();
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::OriginalBound { .. })
        ));

        let mut tampered = certificate.clone();
        let first_terminal = tampered.original.terminal_grams.remove(0);
        tampered.original.occupation_grams.push(first_terminal);
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::Exact(
                ExactAuditError::GramCount { .. }
            ))
        ));

        let mut tampered = certificate.clone();
        tampered.bound_target = "1".into();
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::TargetBound { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.total_occupation_multiplier, "1");
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::OccupationMultiplier { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.total_terminal_discount, "1");
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::TerminalDiscount { .. })
        ));

        let mut tampered = certificate;
        add_rational(&mut tampered.discounted_bound, "1");
        assert!(matches!(
            audit_shifted_exact_certificate(&tampered),
            Err(ShiftedExactAuditError::DiscountedBound { .. })
        ));
    }

    #[test]
    fn passing_blocks_require_canonical_zero_delta() {
        let original = weak_order_two_certificate();
        let mut certificate = build_shifted_exact_certificate(
            original,
            vec!["0".into(); shifted_block_derivations(2).unwrap().len()],
        )
        .unwrap();
        certificate.blocks[0].delta = "1/1000".into();
        assert!(matches!(
            audit_shifted_exact_certificate(&certificate),
            Err(ShiftedExactAuditError::UnexpectedShift { block: 0 })
        ));
    }

    #[test]
    fn end_to_end_salvage_finds_and_audits_exact_shifts() {
        let original = shifted_order_two_certificate().original;
        let serial = salvage_exact_shifted_certificate_with_jobs(original.clone(), 1).unwrap();
        let parallel = salvage_exact_shifted_certificate_with_jobs(original, 2).unwrap();
        assert_eq!(
            serde_json::to_value(&serial).unwrap(),
            serde_json::to_value(parallel).unwrap()
        );
        let ShiftedSalvageOutcome::Certified { certificate } = serial else {
            panic!("salvageable coordinate must produce a certificate")
        };
        let report = audit_shifted_exact_certificate(&certificate).unwrap();
        assert_eq!(report.shifted_gram_count, 1);
        let delta = certificate
            .blocks
            .iter()
            .find(|block| block.delta != "0")
            .map(|block| exact_rational(&block.delta))
            .unwrap()
            .unwrap();
        assert!(delta >= BigRational::new(BigInt::one(), BigInt::from(1000)));
    }

    #[test]
    fn salvage_scans_all_failures_and_records_unsalvageable_zero_cost_blocks() {
        let mut original = weak_order_two_certificate();
        let salvageable = add_failing_interval_diagonal(&mut original, true);
        let unsalvageable = add_failing_interval_diagonal(&mut original, false);
        let serial = salvage_exact_shifted_certificate_with_jobs(original.clone(), 1).unwrap();
        let outcome = salvage_exact_shifted_certificate_with_jobs(original, 2).unwrap();
        assert_eq!(
            serde_json::to_value(serial).unwrap(),
            serde_json::to_value(&outcome).unwrap()
        );
        let ShiftedSalvageOutcome::Unsalvageable { failure } = outcome else {
            panic!("a shifted zero-cost coordinate must reject salvage")
        };
        assert_eq!(
            failure.blocks.len(),
            shifted_block_derivations(2).unwrap().len()
        );
        assert_eq!(failure.unsalvageable_blocks, vec![unsalvageable]);
        assert!(
            exact_rational(&failure.blocks[salvageable].required_delta)
                .unwrap()
                .is_positive()
        );
        assert!(failure.blocks[salvageable].salvageable);
        assert!(
            exact_rational(&failure.blocks[unsalvageable].required_delta)
                .unwrap()
                .is_positive()
        );
        assert!(!failure.blocks[unsalvageable].salvageable);
        assert!(matches!(
            failure.blocks[unsalvageable].failure_reason,
            Some(ShiftedSalvageReason::NoFiniteCostRelativeBoundDerived { .. })
        ));
    }
}
