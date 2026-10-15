use super::{
    BigQsqrt2, ExactAuditError, ExactAuditReport, ParsedGram, ResidualGramCertificate,
    ScalarParser, add_assign, parse_matrix, residual_gram_certificate, sub_assign,
};
use crate::Rational;
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::stationary_hausdorff::EXPOSURE_UPPER;
use crate::stationary_hausdorff_split::{ExactSplitModel, SplitGrid, structure};
use nalgebra::DMatrix;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Mutex;
use thiserror::Error;

pub const SPLIT_EXACT_SCHEMA_V1: &str = "jan22-cost-lifted-split-exact-dual-q-v1";
const EQUALITY_ORDER_V1: &str = "cell_major_liouville_v1";
const GRAM_ORDER_V1: &str =
    "occupation_by_cell_then_interface_by_knot_then_terminal_pair_by_cell_v1";
const AXIS_ALIGNMENT_SQUARED_THRESHOLD: f64 = 0.999;

pub(super) type EncodedMatrix = Vec<Vec<String>>;

/// A split certificate has an intentionally separate, non-positional schema.
/// Every hierarchy-owned family is grouped by its physical cell or interface.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SplitExactDualCertificate {
    pub schema: String,
    pub order: u8,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub formulation_hash: String,
    pub exposure_upper: String,
    pub bound_target: String,
    pub equality_order: String,
    pub liouville_multipliers_by_cell: Vec<Vec<String>>,
    pub normalization: String,
    pub gram_order: String,
    pub occupation_grams_by_cell: Vec<Vec<EncodedMatrix>>,
    pub interface_grams_by_knot: Vec<Vec<EncodedMatrix>>,
    pub terminal_grams_by_cell: Vec<Vec<EncodedMatrix>>,
    #[serde(default)]
    pub provenance: Option<serde_json::Value>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitConeRepairDiagnostics {
    pub coefficient_count: usize,
    pub active_gram_count: usize,
    pub zero_gram_count: usize,
    pub repair_gram_count: usize,
    pub constrained_gram_count: usize,
    pub fixed_gram_count: usize,
    pub full_active_gram_coordinate_count: usize,
    pub constrained_gram_coordinate_count: usize,
    pub active_gram_square_count: u64,
    pub constrained_gram_square_count: u64,
    pub active_gram_cube_count: u64,
    pub constrained_gram_cube_count: u64,
    pub restricted_gram_coordinate_count: usize,
    pub signature_basis_coordinate_count: usize,
    pub vulnerable_gram_count: usize,
    pub strict_margin_gram_count: usize,
    pub repaired_margin_gram_count: usize,
    pub preserved_margin_gram_count: usize,
    pub semidefinite_face_gram_count: usize,
    pub vulnerable_coefficient_count: usize,
    pub expanded_neighbor_coordinate_count: usize,
    pub correction_variable_count: usize,
    pub cone_row_count: usize,
    #[serde(skip_serializing_if = "usize_is_zero")]
    pub rotated_kernel_gram_count: usize,
    #[serde(skip_serializing_if = "usize_is_zero")]
    pub rotated_kernel_equation_count: usize,
    pub initial_maximum_identity_residual: f64,
    pub initial_bound: f64,
    pub target: f64,
    pub affine_constraint_scale: f64,
    pub gram_constraint_scale: f64,
    pub margin_variable_scale: f64,
    pub affine_correction_radius: f64,
    pub gram_correction_radius: f64,
    pub correction_bounds_enforced: bool,
    pub fixed_common_margin: Option<f64>,
    pub margin_cap: f64,
    pub exact_input_parse_wall_seconds: f64,
    pub exact_identity_reconstruction_wall_seconds: f64,
}

fn usize_is_zero(value: &usize) -> bool {
    *value == 0
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitExactRepairDiagnostics {
    pub coefficient_count: usize,
    pub equation_count_with_bound: usize,
    pub full_active_gram_coordinate_count: usize,
    pub unique_gram_signature_count: usize,
    pub available_affine_variable_count: usize,
    pub selected_exact_rank: usize,
    pub selected_affine_variable_count: usize,
    pub selected_gram_variable_count: usize,
    pub minimum_selected_gram_margin_before_repair: Option<f64>,
    pub exact_component_count: usize,
    pub largest_exact_component: usize,
    pub maximum_absolute_exact_correction: f64,
    pub timings: SplitExactRepairTimings,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitExactRepairTimings {
    pub input_parse_and_residual_wall_seconds: f64,
    pub exact_gram_parse_wall_seconds: f64,
    pub initial_residual_reconstruction_wall_seconds: f64,
    pub gram_analysis_and_column_build_wall_seconds: f64,
    pub signature_deduplication_wall_seconds: f64,
    pub modular_basis_selection_wall_seconds: f64,
    pub exact_component_solve_wall_seconds: f64,
    pub correction_apply_wall_seconds: f64,
    pub write_back_wall_seconds: f64,
    pub post_repair_exact_check_wall_seconds: f64,
    pub total_wall_seconds: f64,
}

#[derive(Clone, Debug)]
pub struct SplitConeRepairPlan {
    variables: Vec<RepairVariable>,
    margin_variable: usize,
    margin_scale: f64,
}

#[derive(Clone, Debug)]
pub struct SplitRotatedConeRepairPlan {
    variables: Vec<FaceRepairVariable>,
    margin_variable: usize,
    margin_scale: f64,
}

#[derive(Clone)]
struct RotatedConeRepairColumn {
    variable: FaceRepairVariable,
    coefficients: BTreeMap<usize, BigQsqrt2>,
}

/// One exact Gram face `F K F^T`. Rows of `basis` are rows of `F`; the square
/// `coordinates` matrix is `K`. Exactification may change only `K`, so a
/// rank-deficient Gram never acquires a component in the discarded null face.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SplitFaceBlock {
    pub basis: Vec<Vec<String>>,
    pub coordinates: Vec<Vec<String>>,
}

/// Checkpoint state for a genuinely rotated or spectrally reduced Gram block.
/// Coordinate-selector faces are reconstructed directly from the certificate's
/// exact-zero rows and are intentionally omitted to keep checkpoints compact.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SplitRotatedFaceState {
    pub block: usize,
    pub face: SplitFaceBlock,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SplitRotatedFaceBuildReport {
    pub eigenvalue_threshold: f64,
    pub basis_dyadic_bits: u32,
    pub active_gram_count: usize,
    pub unchanged_full_face_block_count: usize,
    pub coordinate_reduced_block_count: usize,
    pub rotated_reduced_block_count: usize,
    pub zero_face_block_count: usize,
    pub discarded_direction_count: usize,
    pub retained_direction_count: usize,
    pub minimum_retained_floating_eigenvalue: f64,
    pub maximum_discarded_floating_eigenvalue: f64,
    pub representation: &'static str,
}

/// Frozen exact candidate kernel for one Gram block. `kernel` is a `d × k`
/// matrix stored by rows. Its columns are exact dyadic vectors selected from
/// floating near-null eigendirections; only subsequent exact affine closure
/// and the unchanged exact PSD audits can accept the resulting certificate.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SplitRotatedKernelState {
    pub block: usize,
    pub kernel: Vec<Vec<String>>,
}

/// One exact candidate face imposed directly on an original split SDP bar
/// variable. `range_projector` is the floating image of an exact rational
/// orthogonal projector `P`; the native solve uses `G = X + margin * P` and
/// constrains the positive-semidefinite bar variable `X` by
/// `<I-P, X> = 0`. This plan is advisory and is never serialized into a v1
/// exact certificate.
#[derive(Clone, Debug)]
pub struct SplitNativeBarFaceBlock {
    pub block: usize,
    pub range_projector: Vec<Vec<f64>>,
    pub rotated: bool,
    pub kernel_rank: usize,
}

#[derive(Clone, Debug)]
pub struct SplitNativeBarFacePlan {
    pub gram_count: usize,
    pub blocks: Vec<SplitNativeBarFaceBlock>,
}

#[derive(Clone)]
struct ParsedRotatedKernelState {
    block: usize,
    kernel: Vec<Vec<BigRational>>,
    small_kernel: Vec<Vec<crate::Qsqrt2>>,
    projector: Vec<Vec<BigRational>>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitRotatedKernelBuildReport {
    pub eigenvalue_threshold: f64,
    pub minimum_eligible_eigenvalue: f64,
    pub eligibility: &'static str,
    pub basis_dyadic_bits: u32,
    pub active_gram_count: usize,
    pub eligible_gram_count: usize,
    pub rotated_kernel_gram_count: usize,
    pub spectral_kernel_direction_count: usize,
    pub non_axis_aligned_kernel_direction_count: usize,
    pub coordinate_kernel_direction_count: usize,
    pub minimum_selected_floating_eigenvalue: f64,
    pub maximum_selected_floating_eigenvalue: f64,
    pub representation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitNearNullEigenDiagnostics {
    pub eigenvalue_threshold: f64,
    pub axis_alignment_squared_threshold: f64,
    pub active_gram_count: usize,
    pub gram_count_with_subthreshold_eigenvalues: usize,
    pub subthreshold_eigenvalue_count: usize,
    pub axis_aligned_eigenvalue_count: usize,
    pub rotated_eigenvalue_count: usize,
    pub minimum_eigenvalue: f64,
    pub maximum_subthreshold_eigenvalue: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitFaceRepairReport {
    pub coefficient_count: usize,
    pub identity_span: usize,
    pub identity_span_scan_complete: bool,
    pub affine_variable_count: usize,
    pub face_variable_count: usize,
    pub face_ranks: Vec<usize>,
    pub full_face_block_count: usize,
    pub zero_face_block_count: usize,
    pub nonzero_exact_residual_count_before_repair: usize,
    pub nonzero_exact_residual_count_after_repair: usize,
    pub exact_identity_closed: bool,
    pub coordinate_matrices_exactly_positive_semidefinite: bool,
    pub coordinate_psd_failure: Option<String>,
    pub minimum_reconstructed_coordinate_eigenvalue: f64,
    pub numerical_minimum_norm_iterations: usize,
    pub numerical_minimum_norm_relative_residual: f64,
    pub numerical_correction_maximum_absolute_value: f64,
    pub minimum_coordinate_eigenvalue_before_exact_tail: f64,
    pub selected_exact_correction_block_count: usize,
    pub selected_exact_correction_blocks: Vec<usize>,
}

#[derive(Debug, Error)]
pub enum SplitExactAuditError {
    #[error("unsupported split exact certificate schema {0:?}")]
    Schema(String),
    #[error("split certificate knots are not canonical exact rationals")]
    NoncanonicalKnots,
    #[error("invalid split grid: {0}")]
    Grid(String),
    #[error("split grid hash {found:?} does not match regenerated hash {expected:?}")]
    SplitGridHash { found: String, expected: String },
    #[error("split formulation hash {found:?} does not match regenerated hash {expected:?}")]
    FormulationHash { found: String, expected: String },
    #[error("split exposure upper must be exactly 2935887/1000000")]
    ExposureUpper,
    #[error("unsupported split equality ordering {0:?}")]
    EqualityOrder(String),
    #[error("unsupported split Gram ordering {0:?}")]
    GramOrder(String),
    #[error("wrong {family} outer count: expected {expected}, found {found}")]
    FamilyCount {
        family: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("wrong {family} count at group {group}: expected {expected}, found {found}")]
    GroupCount {
        family: &'static str,
        group: usize,
        expected: usize,
        found: usize,
    },
    #[error("internal split exact model error: {0}")]
    Model(String),
    #[error("split exact identity repair failed: {0}")]
    Repair(String),
    #[error(transparent)]
    Exact(#[from] ExactAuditError),
}

pub(super) struct ValidatedLayout {
    pub(super) grid: SplitGrid,
    pub(super) model: ExactSplitModel,
    pub(super) dimensions: Vec<usize>,
}

pub(super) fn validate_layout(
    certificate: &SplitExactDualCertificate,
) -> Result<ValidatedLayout, SplitExactAuditError> {
    if certificate.schema != SPLIT_EXACT_SCHEMA_V1 {
        return Err(SplitExactAuditError::Schema(certificate.schema.clone()));
    }
    if certificate.equality_order != EQUALITY_ORDER_V1 {
        return Err(SplitExactAuditError::EqualityOrder(
            certificate.equality_order.clone(),
        ));
    }
    if certificate.gram_order != GRAM_ORDER_V1 {
        return Err(SplitExactAuditError::GramOrder(
            certificate.gram_order.clone(),
        ));
    }
    let parsed_knots = certificate
        .knots
        .iter()
        .map(|value| value.parse::<Rational>())
        .collect::<Result<Vec<_>, _>>()
        .map_err(SplitExactAuditError::Grid)?;
    let grid = SplitGrid::new(parsed_knots).map_err(SplitExactAuditError::Grid)?;
    if certificate.knots != grid.canonical_knots() {
        return Err(SplitExactAuditError::NoncanonicalKnots);
    }
    let expected_grid_hash = grid.canonical_hash();
    if certificate.split_grid_hash != expected_grid_hash {
        return Err(SplitExactAuditError::SplitGridHash {
            found: certificate.split_grid_hash.clone(),
            expected: expected_grid_hash,
        });
    }
    let regenerated = structure(certificate.order, &grid).map_err(SplitExactAuditError::Model)?;
    if certificate.formulation_hash != regenerated.formulation_hash {
        return Err(SplitExactAuditError::FormulationHash {
            found: certificate.formulation_hash.clone(),
            expected: regenerated.formulation_hash,
        });
    }
    let exposure = ScalarParser::parse(&certificate.exposure_upper)?;
    let expected_exposure = ScalarParser::parse(&EXPOSURE_UPPER.to_string())?;
    if exposure != expected_exposure {
        return Err(SplitExactAuditError::ExposureUpper);
    }

    let model =
        ExactSplitModel::create(certificate.order, &grid).map_err(SplitExactAuditError::Model)?;
    check_outer(
        "Liouville cell",
        model.cell_count(),
        certificate.liouville_multipliers_by_cell.len(),
    )?;
    for (cell, values) in certificate.liouville_multipliers_by_cell.iter().enumerate() {
        check_group(
            "Liouville multiplier",
            cell,
            model.equality_count_per_cell(),
            values.len(),
        )?;
    }
    check_outer(
        "occupation cell",
        model.cell_count(),
        certificate.occupation_grams_by_cell.len(),
    )?;
    for (cell, values) in certificate.occupation_grams_by_cell.iter().enumerate() {
        check_group(
            "occupation Gram",
            cell,
            model.occupation_gram_count_per_cell(),
            values.len(),
        )?;
    }
    let interface_count = model.cell_count().saturating_sub(1);
    check_outer(
        "interface knot",
        interface_count,
        certificate.interface_grams_by_knot.len(),
    )?;
    for (interface, values) in certificate.interface_grams_by_knot.iter().enumerate() {
        check_group(
            "interface Gram",
            interface,
            model.interface_gram_count_per_interface(),
            values.len(),
        )?;
    }
    check_outer(
        "terminal cell",
        model.cell_count(),
        certificate.terminal_grams_by_cell.len(),
    )?;
    for (cell, values) in certificate.terminal_grams_by_cell.iter().enumerate() {
        check_group("terminal Gram", cell, 2, values.len())?;
    }
    let dimensions = model.gram_dimensions();
    let grams = flattened_grams(certificate);
    if grams.len() != dimensions.len() {
        return Err(SplitExactAuditError::Exact(ExactAuditError::GramCount {
            expected: dimensions.len(),
            found: grams.len(),
        }));
    }
    Ok(ValidatedLayout {
        grid,
        model,
        dimensions,
    })
}

fn check_outer(
    family: &'static str,
    expected: usize,
    found: usize,
) -> Result<(), SplitExactAuditError> {
    if expected != found {
        return Err(SplitExactAuditError::FamilyCount {
            family,
            expected,
            found,
        });
    }
    Ok(())
}

fn check_group(
    family: &'static str,
    group: usize,
    expected: usize,
    found: usize,
) -> Result<(), SplitExactAuditError> {
    if expected != found {
        return Err(SplitExactAuditError::GroupCount {
            family,
            group,
            expected,
            found,
        });
    }
    Ok(())
}

pub(super) fn flattened_grams(certificate: &SplitExactDualCertificate) -> Vec<&EncodedMatrix> {
    certificate
        .occupation_grams_by_cell
        .iter()
        .flatten()
        .chain(certificate.interface_grams_by_knot.iter().flatten())
        .chain(certificate.terminal_grams_by_cell.iter().flatten())
        .collect()
}

fn flattened_multipliers(
    certificate: &SplitExactDualCertificate,
) -> Result<Vec<BigQsqrt2>, ExactAuditError> {
    certificate
        .liouville_multipliers_by_cell
        .iter()
        .flatten()
        .map(|value| ScalarParser::parse(value))
        .collect()
}

pub(super) fn reconstructed_identity(
    model: &ExactSplitModel,
    multipliers: &[BigQsqrt2],
    normalization: &BigQsqrt2,
    grams: &[&EncodedMatrix],
    dimensions: &[usize],
) -> Result<Vec<BigQsqrt2>, ExactAuditError> {
    let mut identity = vec![BigQsqrt2::zero(); model.coefficient_count()];
    model.for_each_cost_coefficient(|position, coefficient| {
        add_assign(&mut identity[position], &BigQsqrt2::from_small(coefficient));
    });
    model.for_each_normalization_position(|position| {
        add_assign(&mut identity[position], normalization);
    });
    for (multiplier, row) in multipliers.iter().zip(&model.rows) {
        for &(position, coefficient) in &row.coefficients {
            add_assign(&mut identity[position], &multiplier.mul_small(coefficient));
        }
    }
    for (block, encoded) in grams.iter().enumerate() {
        let matrix = parse_matrix(block, encoded, dimensions[block])?;
        accumulate_gram(model, block, &matrix, &mut identity);
    }
    Ok(identity)
}

fn parse_gram_refs(
    grams: &[&EncodedMatrix],
    dimensions: &[usize],
) -> Result<Vec<ParsedGram>, ExactAuditError> {
    grams
        .par_iter()
        .enumerate()
        .map(|(block, encoded)| parse_matrix(block, encoded, dimensions[block]))
        .collect()
}

fn reconstructed_identity_from_parsed(
    model: &ExactSplitModel,
    multipliers: &[BigQsqrt2],
    normalization: &BigQsqrt2,
    grams: &[ParsedGram],
) -> Vec<BigQsqrt2> {
    let mut identity = vec![BigQsqrt2::zero(); model.coefficient_count()];
    model.for_each_cost_coefficient(|position, coefficient| {
        add_assign(&mut identity[position], &BigQsqrt2::from_small(coefficient));
    });
    model.for_each_normalization_position(|position| {
        add_assign(&mut identity[position], normalization);
    });
    for (multiplier, row) in multipliers.iter().zip(&model.rows) {
        for &(position, coefficient) in &row.coefficients {
            add_assign(&mut identity[position], &multiplier.mul_small(coefficient));
        }
    }
    let gram_contribution = grams
        .par_iter()
        .enumerate()
        .fold(
            || vec![BigQsqrt2::zero(); model.coefficient_count()],
            |mut contribution, (block, matrix)| {
                accumulate_gram(model, block, matrix, &mut contribution);
                contribution
            },
        )
        .reduce(
            || vec![BigQsqrt2::zero(); model.coefficient_count()],
            |mut left, right| {
                for (target, value) in left.iter_mut().zip(&right) {
                    add_assign(target, value);
                }
                left
            },
        );
    for (target, value) in identity.iter_mut().zip(&gram_contribution) {
        add_assign(target, value);
    }
    identity
}

fn parsed_gram_entry(matrix: &ParsedGram, row: usize, column: usize) -> BigQsqrt2 {
    match matrix {
        ParsedGram::Rational(values) => BigQsqrt2::from_rational(values[row][column].clone()),
        ParsedGram::Quadratic(values) => values[row][column].clone(),
    }
}

fn set_parsed_gram_entry(matrix: &mut ParsedGram, row: usize, column: usize, value: BigQsqrt2) {
    if let ParsedGram::Rational(values) = matrix
        && value.sqrt2.is_zero()
    {
        values[row][column] = value.rational.clone();
        values[column][row] = value.rational;
        return;
    }
    if let ParsedGram::Rational(values) = matrix {
        *matrix = ParsedGram::Quadratic(
            values
                .iter()
                .map(|values| {
                    values
                        .iter()
                        .cloned()
                        .map(BigQsqrt2::from_rational)
                        .collect()
                })
                .collect(),
        );
    }
    let ParsedGram::Quadratic(values) = matrix else {
        unreachable!("rational Gram was converted to quadratic")
    };
    values[row][column] = value.clone();
    values[column][row] = value;
}

fn accumulate_gram(
    model: &ExactSplitModel,
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

/// Exact unpivoted LDLᵀ for positive semidefinite matrices. A zero Schur
/// pivot is sound only when its remaining Schur-complement column is zero.
pub(super) fn semidefinite_ldl_minimum(
    block: usize,
    matrix: &mut ParsedGram,
) -> Result<(Option<BigQsqrt2>, bool), ExactAuditError> {
    if let Some(certificate) = fraction_free_semidefinite_ldl_minimum(block, matrix)? {
        return Ok(certificate);
    }
    match matrix {
        ParsedGram::Rational(values) => {
            let (minimum, positive_definite) = semidefinite_rational_ldl(block, values)?;
            Ok((minimum.map(BigQsqrt2::from_rational), positive_definite))
        }
        ParsedGram::Quadratic(values) => semidefinite_quadratic_ldl(block, values),
    }
}

#[derive(Clone)]
struct IntegerQsqrt2 {
    rational: BigInt,
    sqrt2: BigInt,
}

impl IntegerQsqrt2 {
    fn one() -> Self {
        Self {
            rational: BigInt::one(),
            sqrt2: BigInt::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.rational.is_zero() && self.sqrt2.is_zero()
    }

    fn is_positive(&self) -> bool {
        if self.sqrt2.is_zero() {
            return self.rational.is_positive();
        }
        if !self.rational.is_negative() && self.sqrt2.is_positive() {
            return true;
        }
        if !self.rational.is_positive() && self.sqrt2.is_negative() {
            return false;
        }
        let comparison =
            &self.rational * &self.rational - BigInt::from(2) * &self.sqrt2 * &self.sqrt2;
        if self.rational.is_positive() {
            comparison.is_positive()
        } else {
            comparison.is_negative()
        }
    }

    fn mul(&self, rhs: &Self) -> Self {
        Self {
            rational: &self.rational * &rhs.rational + BigInt::from(2) * &self.sqrt2 * &rhs.sqrt2,
            sqrt2: &self.rational * &rhs.sqrt2 + &self.sqrt2 * &rhs.rational,
        }
    }

    fn sub(&self, rhs: &Self) -> Self {
        Self {
            rational: &self.rational - &rhs.rational,
            sqrt2: &self.sqrt2 - &rhs.sqrt2,
        }
    }

    /// Exact division in Z[sqrt(2)]. Bareiss divisibility is guaranteed over
    /// an integral domain; returning None keeps the original rational LDL as a
    /// conservative fallback if an implementation or input violates it.
    fn exact_div(&self, rhs: &Self) -> Option<Self> {
        let norm = &rhs.rational * &rhs.rational - BigInt::from(2) * &rhs.sqrt2 * &rhs.sqrt2;
        if norm.is_zero() {
            return None;
        }
        let rational_numerator =
            &self.rational * &rhs.rational - BigInt::from(2) * &self.sqrt2 * &rhs.sqrt2;
        let sqrt2_numerator = &self.sqrt2 * &rhs.rational - &self.rational * &rhs.sqrt2;
        let (rational, rational_remainder) = rational_numerator.div_rem(&norm);
        let (sqrt2, sqrt2_remainder) = sqrt2_numerator.div_rem(&norm);
        if !rational_remainder.is_zero() || !sqrt2_remainder.is_zero() {
            return None;
        }
        Some(Self { rational, sqrt2 })
    }

    fn to_big_qsqrt2(&self) -> BigQsqrt2 {
        BigQsqrt2 {
            rational: BigRational::from_integer(self.rational.clone()),
            sqrt2: BigRational::from_integer(self.sqrt2.clone()),
        }
    }

    fn scaled_quotient(
        &self,
        divisor: &Self,
        common_denominator: &BigInt,
    ) -> Result<BigQsqrt2, ExactAuditError> {
        let scaled_divisor = Self {
            rational: &divisor.rational * common_denominator,
            sqrt2: &divisor.sqrt2 * common_denominator,
        };
        self.to_big_qsqrt2().div(&scaled_divisor.to_big_qsqrt2())
    }
}

/// Fraction-free Bareiss form of the same unpivoted semidefinite LDL test.
/// Clearing one positive common denominator preserves semidefiniteness. Each
/// positive pivot is the next leading principal minor; dividing by the prior
/// nonzero minor and the input scale recovers exactly the LDL Schur pivot.
/// A zero pivot is accepted only with a zero remaining fraction-free column,
/// exactly matching the rational fallback below.
fn fraction_free_semidefinite_ldl_minimum(
    block: usize,
    matrix: &ParsedGram,
) -> Result<Option<(Option<BigQsqrt2>, bool)>, ExactAuditError> {
    let dimension = match matrix {
        ParsedGram::Rational(values) => values.len(),
        ParsedGram::Quadratic(values) => values.len(),
    };
    let mut common_denominator = BigInt::one();
    for row in 0..dimension {
        for column in 0..=row {
            match matrix {
                ParsedGram::Rational(values) => {
                    common_denominator = common_denominator.lcm(values[row][column].denom());
                }
                ParsedGram::Quadratic(values) => {
                    common_denominator = common_denominator
                        .lcm(values[row][column].rational.denom())
                        .lcm(values[row][column].sqrt2.denom());
                }
            }
        }
    }
    let scaled_entry = |row: usize, column: usize| match matrix {
        ParsedGram::Rational(values) => IntegerQsqrt2 {
            rational: values[row][column].numer()
                * (&common_denominator / values[row][column].denom()),
            sqrt2: BigInt::zero(),
        },
        ParsedGram::Quadratic(values) => IntegerQsqrt2 {
            rational: values[row][column].rational.numer()
                * (&common_denominator / values[row][column].rational.denom()),
            sqrt2: values[row][column].sqrt2.numer()
                * (&common_denominator / values[row][column].sqrt2.denom()),
        },
    };
    let mut fraction_free = (0..dimension)
        .map(|row| {
            (0..=row)
                .map(|column| scaled_entry(row, column))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut previous_pivot = IntegerQsqrt2::one();
    let mut minimum: Option<BigQsqrt2> = None;
    let mut positive_definite = true;
    for column in 0..dimension {
        let pivot = fraction_free[column][column].clone();
        if !pivot.is_zero() && !pivot.is_positive() {
            let value = pivot.scaled_quotient(&previous_pivot, &common_denominator)?;
            return Err(ExactAuditError::GramPivot {
                block,
                pivot: column,
                value: value.to_string(),
            });
        }
        if pivot.is_zero() {
            positive_definite = false;
            for row in fraction_free.iter().skip(column + 1) {
                let coupling = &row[column];
                if !coupling.is_zero() {
                    let value = coupling.scaled_quotient(&previous_pivot, &common_denominator)?;
                    return Err(ExactAuditError::GramPivot {
                        block,
                        pivot: column,
                        value: format!("zero pivot with nonzero Schur coupling {value}"),
                    });
                }
            }
            continue;
        }
        let exact_pivot = pivot.scaled_quotient(&previous_pivot, &common_denominator)?;
        if minimum
            .as_ref()
            .is_none_or(|current| current.sub(&exact_pivot).is_positive())
        {
            minimum = Some(exact_pivot);
        }
        let eliminators = (column + 1..dimension)
            .map(|row| fraction_free[row][column].clone())
            .collect::<Vec<_>>();
        let update: Result<(), ()> = fraction_free[column + 1..]
            .par_iter_mut()
            .enumerate()
            .try_for_each(|(offset, row)| {
                let row_index = column + 1 + offset;
                for inner_column in column + 1..=row_index {
                    let numerator = pivot
                        .mul(&row[inner_column])
                        .sub(&eliminators[offset].mul(&eliminators[inner_column - column - 1]));
                    row[inner_column] = numerator.exact_div(&previous_pivot).ok_or(())?;
                }
                Ok(())
            });
        if update.is_err() {
            return Ok(None);
        }
        previous_pivot = pivot;
    }
    Ok(Some((minimum, positive_definite)))
}

enum SemidefiniteGramCertificate {
    Residual(ResidualGramCertificate),
    ExactLdl {
        minimum_pivot: Option<BigQsqrt2>,
        positive_definite: bool,
    },
}

fn semidefinite_certificate(
    block: usize,
    matrix: &mut ParsedGram,
) -> Result<SemidefiniteGramCertificate, ExactAuditError> {
    if let Some(certificate) = residual_gram_certificate(matrix) {
        return Ok(SemidefiniteGramCertificate::Residual(certificate));
    }
    let (minimum_pivot, positive_definite) = semidefinite_ldl_minimum(block, matrix)?;
    Ok(SemidefiniteGramCertificate::ExactLdl {
        minimum_pivot,
        positive_definite,
    })
}

fn semidefinite_rational_ldl(
    block: usize,
    matrix: &mut [Vec<BigRational>],
) -> Result<(Option<BigRational>, bool), ExactAuditError> {
    let dimension = matrix.len();
    let mut pivots = Vec::with_capacity(dimension);
    let mut minimum: Option<BigRational> = None;
    let mut positive_definite = true;
    for column in 0..dimension {
        let mut used = BigRational::zero();
        for previous in 0..column {
            used += &matrix[column][previous] * &matrix[column][previous] * &pivots[previous];
        }
        let pivot = &matrix[column][column] - used;
        if pivot.is_negative() {
            return Err(ExactAuditError::GramPivot {
                block,
                pivot: column,
                value: pivot.to_string(),
            });
        }
        if pivot.is_zero() {
            positive_definite = false;
            let (completed, remaining) = matrix.split_at_mut(column + 1);
            let pivot_row = &completed[column];
            remaining.par_iter_mut().try_for_each(|row| {
                let mut coupling = BigRational::zero();
                for previous in 0..column {
                    coupling += &row[previous] * &pivot_row[previous] * &pivots[previous];
                }
                let adjusted = &row[column] - coupling;
                if !adjusted.is_zero() {
                    return Err(ExactAuditError::GramPivot {
                        block,
                        pivot: column,
                        value: format!("zero pivot with nonzero Schur coupling {adjusted}"),
                    });
                }
                row[column] = BigRational::zero();
                Ok(())
            })?;
        } else {
            if minimum.as_ref().is_none_or(|current| current > &pivot) {
                minimum = Some(pivot.clone());
            }
            let (completed, remaining) = matrix.split_at_mut(column + 1);
            let pivot_row = &completed[column];
            remaining.par_iter_mut().for_each(|row| {
                let mut used = BigRational::zero();
                for previous in 0..column {
                    used += &row[previous] * &pivot_row[previous] * &pivots[previous];
                }
                row[column] = (&row[column] - used) / &pivot;
            });
        }
        pivots.push(pivot);
    }
    Ok((minimum, positive_definite))
}

fn semidefinite_quadratic_ldl(
    block: usize,
    matrix: &mut [Vec<BigQsqrt2>],
) -> Result<(Option<BigQsqrt2>, bool), ExactAuditError> {
    let dimension = matrix.len();
    let mut pivots = Vec::with_capacity(dimension);
    let mut minimum: Option<BigQsqrt2> = None;
    let mut positive_definite = true;
    for column in 0..dimension {
        let mut used = BigQsqrt2::zero();
        for previous in 0..column {
            let square = matrix[column][previous].mul(&matrix[column][previous]);
            used = used.add(&square.mul(&pivots[previous]));
        }
        let pivot = matrix[column][column].sub(&used);
        if !pivot.is_zero() && !pivot.is_positive() {
            return Err(ExactAuditError::GramPivot {
                block,
                pivot: column,
                value: pivot.to_string(),
            });
        }
        if pivot.is_zero() {
            positive_definite = false;
            let (completed, remaining) = matrix.split_at_mut(column + 1);
            let pivot_row = &completed[column];
            remaining.par_iter_mut().try_for_each(|row| {
                let mut coupling = BigQsqrt2::zero();
                for previous in 0..column {
                    let product = row[previous].mul(&pivot_row[previous]);
                    coupling = coupling.add(&product.mul(&pivots[previous]));
                }
                let adjusted = row[column].sub(&coupling);
                if !adjusted.is_zero() {
                    return Err(ExactAuditError::GramPivot {
                        block,
                        pivot: column,
                        value: format!("zero pivot with nonzero Schur coupling {adjusted}"),
                    });
                }
                row[column] = BigQsqrt2::zero();
                Ok(())
            })?;
        } else {
            if minimum
                .as_ref()
                .is_none_or(|current| current.sub(&pivot).is_positive())
            {
                minimum = Some(pivot.clone());
            }
            let (completed, remaining) = matrix.split_at_mut(column + 1);
            let pivot_row = &completed[column];
            remaining.par_iter_mut().try_for_each(|row| {
                let mut used = BigQsqrt2::zero();
                for previous in 0..column {
                    let product = row[previous].mul(&pivot_row[previous]);
                    used = used.add(&product.mul(&pivots[previous]));
                }
                row[column] = row[column].sub(&used).div(&pivot)?;
                Ok(())
            })?;
        }
        pivots.push(pivot);
    }
    Ok((minimum, positive_definite))
}

pub fn audit_split_exact_certificate(
    certificate: &SplitExactDualCertificate,
) -> Result<ExactAuditReport, SplitExactAuditError> {
    audit_split_exact_certificate_inner(certificate)
}

pub fn audit_split_exact_certificate_with_jobs(
    certificate: &SplitExactDualCertificate,
    jobs: usize,
) -> Result<ExactAuditReport, SplitExactAuditError> {
    if jobs == 0 {
        return Err(SplitExactAuditError::Exact(ExactAuditError::AuditJobs));
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|error| {
            SplitExactAuditError::Exact(ExactAuditError::ThreadPool(error.to_string()))
        })?
        .install(|| audit_split_exact_certificate_inner(certificate))
}

fn audit_split_exact_certificate_inner(
    certificate: &SplitExactDualCertificate,
) -> Result<ExactAuditReport, SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let _regenerated_grid = &layout.grid;
    let multipliers = flattened_multipliers(certificate)?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let grams = flattened_grams(certificate);

    let mut bound = normalization.neg();
    for (multiplier, row) in multipliers.iter().zip(&layout.model.rows) {
        let endpoint = BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(-row.rhs)));
        add_assign(&mut bound, &multiplier.mul(&endpoint));
    }
    let mut identity = vec![BigQsqrt2::zero(); layout.model.coefficient_count()];
    layout
        .model
        .for_each_cost_coefficient(|position, coefficient| {
            add_assign(&mut identity[position], &BigQsqrt2::from_small(coefficient));
        });
    layout.model.for_each_normalization_position(|position| {
        add_assign(&mut identity[position], &normalization);
    });
    for (multiplier, row) in multipliers.iter().zip(&layout.model.rows) {
        for &(position, coefficient) in &row.coefficients {
            add_assign(&mut identity[position], &multiplier.mul_small(coefficient));
        }
    }

    let identity = Mutex::new(identity);
    let minimum_pivot = Mutex::new(None::<BigQsqrt2>);
    let minimum_residual_bound = Mutex::new(None::<BigRational>);
    let residual_certified_count = Mutex::new(0_usize);
    let exact_ldl_certified_count = Mutex::new(0_usize);
    let positive_count = Mutex::new(0_usize);
    let zero_count = Mutex::new(0_usize);
    grams.par_iter().enumerate().try_for_each(
        |(block, encoded)| -> Result<(), ExactAuditError> {
            let mut matrix = parse_matrix(block, encoded, layout.dimensions[block])?;
            if matrix.is_zero_matrix() {
                *zero_count.lock().expect("zero-count mutex is not poisoned") += 1;
                return Ok(());
            }
            let positive_definite = match semidefinite_certificate(block, &mut matrix)? {
                SemidefiniteGramCertificate::Residual(certificate) => {
                    *residual_certified_count
                        .lock()
                        .expect("residual-count mutex is not poisoned") += 1;
                    let positive_definite = certificate.removed_zero_rows == 0;
                    let mut global = minimum_residual_bound
                        .lock()
                        .expect("minimum-residual-bound mutex is not poisoned");
                    if global
                        .as_ref()
                        .is_none_or(|current| current > &certificate.minimum_eigenvalue_lower_bound)
                    {
                        *global = Some(certificate.minimum_eigenvalue_lower_bound);
                    }
                    positive_definite
                }
                SemidefiniteGramCertificate::ExactLdl {
                    minimum_pivot: block_minimum_pivot,
                    positive_definite,
                } => {
                    *exact_ldl_certified_count
                        .lock()
                        .expect("exact-LDL-count mutex is not poisoned") += 1;
                    if let Some(block_minimum) = block_minimum_pivot {
                        let mut global = minimum_pivot
                            .lock()
                            .expect("minimum-pivot mutex is not poisoned");
                        if global
                            .as_ref()
                            .is_none_or(|current| current.sub(&block_minimum).is_positive())
                        {
                            *global = Some(block_minimum);
                        }
                    }
                    positive_definite
                }
            };
            if positive_definite {
                *positive_count
                    .lock()
                    .expect("positive-count mutex is not poisoned") += 1;
            }
            let mut contribution = vec![BigQsqrt2::zero(); layout.model.coefficient_count()];
            accumulate_gram(&layout.model, block, &matrix, &mut contribution);
            {
                let mut global = identity.lock().expect("identity mutex is not poisoned");
                for (target, value) in global.iter_mut().zip(&contribution) {
                    add_assign(target, value);
                }
            }
            Ok(())
        },
    )?;

    let identity = identity
        .into_inner()
        .expect("identity mutex is not poisoned");
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if nonzero != 0 {
        return Err(SplitExactAuditError::Exact(ExactAuditError::Identity {
            count: nonzero,
        }));
    }
    let difference = bound.sub(&target);
    if !difference.is_zero() && !difference.is_positive() {
        return Err(SplitExactAuditError::Exact(ExactAuditError::Bound {
            bound: bound.to_string(),
            target: target.to_string(),
        }));
    }
    let rigorous_bound = target.to_f64().ok_or_else(|| {
        SplitExactAuditError::Exact(ExactAuditError::InvalidScalar(
            "target cannot be represented as f64 for reporting".into(),
        ))
    })?;
    let positive_definite_gram_count = positive_count
        .into_inner()
        .expect("positive-count mutex is not poisoned");
    let zero_gram_count = zero_count
        .into_inner()
        .expect("zero-count mutex is not poisoned");
    let residual_certified_gram_count = residual_certified_count
        .into_inner()
        .expect("residual-count mutex is not poisoned");
    let exact_ldl_certified_gram_count = exact_ldl_certified_count
        .into_inner()
        .expect("exact-LDL-count mutex is not poisoned");
    let minimum_certified_gram_eigenvalue_lower_bound = minimum_residual_bound
        .into_inner()
        .expect("minimum-residual-bound mutex is not poisoned")
        .map_or_else(
            || "not applicable (no Gram matrix used residual certification)".into(),
            |value| value.to_string(),
        );
    let minimum_exact_ldl_pivot = minimum_pivot
        .into_inner()
        .expect("minimum-pivot mutex is not poisoned")
        .map_or_else(
            || "not applicable (no Gram matrix required exact LDL)".into(),
            |value| value.to_string(),
        );
    Ok(ExactAuditReport {
        sign_convention: "c + A_cell^T lambda + n*sum_cell terminal[0] - S^T Z = 0; bound=-sum(lambda*rhs)-n",
        coefficient_count: layout.model.coefficient_count(),
        nonzero_exact_residual_count: 0,
        all_gram_matrices_exactly_positive_definite: positive_definite_gram_count
            == layout.dimensions.len(),
        all_gram_matrices_exactly_positive_semidefinite: true,
        positive_definite_gram_count,
        zero_gram_count,
        residual_certified_gram_count,
        exact_ldl_certified_gram_count,
        minimum_certified_gram_eigenvalue_lower_bound,
        minimum_exact_ldl_pivot,
        exact_endpoint_bound: bound.to_string(),
        cost_relative_residual_upper: "0".into(),
        certified_bound: target.to_string(),
        endpoint_margin_after_residual: difference.to_string(),
        strictly_exceeds_target: !difference.is_zero(),
        rigorous_bound,
    })
}

#[derive(Clone, Copy, Debug)]
enum RepairVariable {
    Equality(usize),
    Normalization,
    Gram {
        block: usize,
        row: usize,
        column: usize,
    },
}

#[derive(Clone)]
struct RepairColumn {
    variable: RepairVariable,
    coefficients: BTreeMap<usize, crate::Qsqrt2>,
}

fn add_small(
    coefficients: &mut BTreeMap<usize, crate::Qsqrt2>,
    position: usize,
    value: crate::Qsqrt2,
) {
    let combined = coefficients
        .get(&position)
        .copied()
        .unwrap_or(crate::Qsqrt2::ZERO)
        + value;
    if combined == crate::Qsqrt2::ZERO {
        coefficients.remove(&position);
    } else {
        coefficients.insert(position, combined);
    }
}

fn affine_repair_columns(model: &ExactSplitModel, bound_row: usize) -> Vec<RepairColumn> {
    let mut columns = Vec::with_capacity(model.rows.len() + 1);
    for (index, equality) in model.rows.iter().enumerate() {
        let mut coefficients = BTreeMap::new();
        for &(position, value) in &equality.coefficients {
            add_small(&mut coefficients, position, value);
        }
        add_small(
            &mut coefficients,
            bound_row,
            crate::Qsqrt2::from(-equality.rhs),
        );
        columns.push(RepairColumn {
            variable: RepairVariable::Equality(index),
            coefficients,
        });
    }
    let mut coefficients = BTreeMap::new();
    model.for_each_normalization_position(|position| {
        add_small(&mut coefficients, position, crate::Qsqrt2::from(1));
    });
    add_small(&mut coefficients, bound_row, crate::Qsqrt2::from(-1));
    columns.push(RepairColumn {
        variable: RepairVariable::Normalization,
        coefficients,
    });
    columns
}

fn active_parsed_gram_blocks(grams: &[ParsedGram]) -> Vec<bool> {
    grams
        .iter()
        .map(|matrix| !matrix.is_zero_matrix())
        .collect()
}

fn active_parsed_gram_rows(grams: &[ParsedGram]) -> Vec<Vec<bool>> {
    grams
        .iter()
        .map(|matrix| {
            let dimension = match matrix {
                ParsedGram::Rational(values) => values.len(),
                ParsedGram::Quadratic(values) => values.len(),
            };
            (0..dimension)
                .map(|row| !matrix.entry_is_zero(row, row))
                .collect()
        })
        .collect()
}

fn all_gram_repair_columns(
    model: &ExactSplitModel,
    dimensions: &[usize],
    active: &[bool],
    active_rows: Option<&[Vec<bool>]>,
) -> (Vec<RepairColumn>, usize) {
    let mut columns = Vec::new();
    let mut full_coordinate_count = 0;
    for (block, (&dimension, &is_active)) in dimensions.iter().zip(active).enumerate() {
        if !is_active {
            continue;
        }
        full_coordinate_count += dimension * (dimension + 1) / 2;
        for distance in 0..dimension {
            for row in 0..dimension - distance {
                let column = row + distance;
                if active_rows.is_some_and(|rows| !rows[block][row] || !rows[block][column]) {
                    continue;
                }
                let mut coefficients = BTreeMap::new();
                model.for_each_gram_entry_coefficient(block, row, column, |position, value| {
                    add_small(&mut coefficients, position, -value)
                });
                if row != column {
                    model.for_each_gram_entry_coefficient(block, column, row, |position, value| {
                        add_small(&mut coefficients, position, -value)
                    });
                }
                if coefficients.is_empty() {
                    continue;
                }
                columns.push(RepairColumn {
                    variable: RepairVariable::Gram { block, row, column },
                    coefficients,
                });
            }
        }
    }
    (columns, full_coordinate_count)
}

fn augment_gram_columns_with_kernel_equalities(
    columns: &mut Vec<RepairColumn>,
    kernels: &[ParsedRotatedKernelState],
    dimensions: &[usize],
    active_rows: &[Vec<bool>],
    first_kernel_row: usize,
) -> (Vec<Option<usize>>, usize) {
    let mut row_offset_by_block = vec![None; dimensions.len()];
    let mut equation_count = 0;
    for state in kernels {
        row_offset_by_block[state.block] = Some(equation_count);
        equation_count += dimensions[state.block] * state.kernel[0].len();
    }
    if equation_count == 0 {
        return (row_offset_by_block, equation_count);
    }
    let mut coordinate_columns = columns
        .iter()
        .enumerate()
        .filter_map(|(index, column)| match column.variable {
            RepairVariable::Gram { block, row, column } => Some(((block, row, column), index)),
            RepairVariable::Equality(_) | RepairVariable::Normalization => None,
        })
        .collect::<HashMap<_, _>>();
    for state in kernels {
        let block = state.block;
        let dimension = dimensions[block];
        let block_row_offset =
            row_offset_by_block[block].expect("parsed rotated kernel has a row offset");
        for row in 0..dimension {
            if !active_rows[block][row] {
                continue;
            }
            for (column, &column_is_active) in active_rows[block].iter().enumerate().skip(row) {
                if !column_is_active {
                    continue;
                }
                let index = *coordinate_columns
                    .entry((block, row, column))
                    .or_insert_with(|| {
                        let index = columns.len();
                        columns.push(RepairColumn {
                            variable: RepairVariable::Gram { block, row, column },
                            coefficients: BTreeMap::new(),
                        });
                        index
                    });
                for kernel_column in 0..state.kernel[0].len() {
                    let left = state.small_kernel[column][kernel_column];
                    if left != crate::Qsqrt2::ZERO {
                        add_small(
                            &mut columns[index].coefficients,
                            first_kernel_row + block_row_offset + kernel_column * dimension + row,
                            left,
                        );
                    }
                    if row != column {
                        let right = state.small_kernel[row][kernel_column];
                        if right != crate::Qsqrt2::ZERO {
                            add_small(
                                &mut columns[index].coefficients,
                                first_kernel_row
                                    + block_row_offset
                                    + kernel_column * dimension
                                    + column,
                                right,
                            );
                        }
                    }
                }
            }
        }
    }
    (row_offset_by_block, equation_count)
}

fn reconstructed_parsed_matrix_minimum(
    matrix: &ParsedGram,
    dimension: usize,
) -> Result<f64, SplitExactAuditError> {
    let values = (0..dimension)
        .flat_map(|row| {
            (0..dimension).map(move |column| match matrix {
                ParsedGram::Rational(values) => values[row][column].to_f64(),
                ParsedGram::Quadratic(values) => values[row][column].to_f64(),
            })
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| {
            ExactAuditError::InvalidScalar(
                "an exact Gram entry cannot be represented as f64".into(),
            )
        })?;
    let matrix = nalgebra::DMatrix::from_row_slice(dimension, dimension, &values);
    let minimum = matrix.symmetric_eigen().eigenvalues.min();
    if !minimum.is_finite() {
        return Err(SplitExactAuditError::Model(
            "an exact Gram cannot be reconstructed as a finite f64 matrix".into(),
        ));
    }
    Ok(minimum)
}

fn reconstructed_bound(
    model: &ExactSplitModel,
    multipliers: &[BigQsqrt2],
    normalization: &BigQsqrt2,
) -> BigQsqrt2 {
    let mut bound = normalization.neg();
    for (multiplier, row) in multipliers.iter().zip(&model.rows) {
        let endpoint = BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(-row.rhs)));
        add_assign(&mut bound, &multiplier.mul(&endpoint));
    }
    bound
}

fn finite(value: &BigQsqrt2, label: &str) -> Result<f64, SplitExactAuditError> {
    value
        .to_f64()
        .filter(|value| value.is_finite())
        .ok_or_else(|| {
            SplitExactAuditError::Repair(format!("{label} cannot be represented as a finite f64"))
        })
}

/// Build a scaled PSD-constrained correction over all affine variables, every
/// active Gram diagonal, and one representative of every exact coefficient
/// signature. This freezes every other coordinate, avoiding both the
/// high-degree constant-coefficient vertex and full expansion of large negative
/// blocks; their selected diagonals can still move while the signature basis
/// closes the resulting affine changes elsewhere.
/// The returned floating problem is advisory: applying its solution is followed
/// by exact affine closure and the optimizer-free exact audit.
pub fn build_split_cone_repair_problem(
    certificate: &SplitExactDualCertificate,
    requested_margin: f64,
    margin_cap: f64,
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    build_split_cone_repair_problem_impl(
        certificate,
        requested_margin,
        margin_cap,
        true,
        1e-4,
        None,
        None,
    )
}

/// Build the same correction model without per-coordinate box cones. The
/// common margin is fixed at the requested value by one Zero row. The resulting
/// Zero/PSD-only feasibility problem uses MOSEK's native bar-variable dual
/// adapter instead of scalarized affine-cone rows.
pub fn build_split_bar_cone_repair_problem(
    certificate: &SplitExactDualCertificate,
    requested_margin: f64,
    margin_cap: f64,
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    build_split_bar_cone_repair_problem_scaled(certificate, requested_margin, margin_cap, 1e-4)
}

/// Build the native-bar correction with an explicit target scale for its PSD
/// rows. This changes numerical conditioning only; exact affine closure and
/// optimizer-free LDL remain mandatory after applying the advisory solution.
pub fn build_split_bar_cone_repair_problem_scaled(
    certificate: &SplitExactDualCertificate,
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    build_split_cone_repair_problem_impl(
        certificate,
        requested_margin,
        margin_cap,
        false,
        gram_scale_target,
        None,
        None,
    )
}

/// Build native-bar cone repair while allowing Gram corrections only in the
/// supplied blocks (plus any materially negative block).
/// Other nonzero Grams remain fixed and are still checked by the final exact
/// audit, so omitting them from the advisory KKT system cannot certify them.
pub fn build_split_bar_cone_repair_problem_scaled_restricted(
    certificate: &SplitExactDualCertificate,
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
    repair_gram_blocks: &[usize],
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    let repair_grams = split_gram_selection_mask(certificate, repair_gram_blocks)?;
    build_split_cone_repair_problem_impl(
        certificate,
        requested_margin,
        margin_cap,
        false,
        gram_scale_target,
        Some(&repair_grams),
        None,
    )
}

/// Build the established native-Gram cone repair while imposing exact dyadic
/// candidate kernels through sparse linear `G*N=0` rows. The PSD offset is
/// `G-m*P`, where `P=I-N*(N^T*N)^-1*N^T` is formed exactly over the rationals
/// and converted to floating coefficients only for this advisory MOSEK solve.
pub fn build_split_kernel_bar_cone_repair_problem_scaled(
    certificate: &SplitExactDualCertificate,
    kernels: &[SplitRotatedKernelState],
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    build_split_cone_repair_problem_impl(
        certificate,
        requested_margin,
        margin_cap,
        false,
        gram_scale_target,
        None,
        Some(kernels),
    )
}

pub fn build_split_kernel_bar_cone_repair_problem_scaled_restricted(
    certificate: &SplitExactDualCertificate,
    kernels: &[SplitRotatedKernelState],
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
    repair_gram_blocks: &[usize],
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    let repair_grams = split_gram_selection_mask(certificate, repair_gram_blocks)?;
    build_split_cone_repair_problem_impl(
        certificate,
        requested_margin,
        margin_cap,
        false,
        gram_scale_target,
        Some(&repair_grams),
        Some(kernels),
    )
}

fn build_split_cone_repair_problem_impl(
    certificate: &SplitExactDualCertificate,
    requested_margin: f64,
    margin_cap: f64,
    correction_bounds_enforced: bool,
    gram_scale_target: f64,
    allowed_grams: Option<&[bool]>,
    kernels: Option<&[SplitRotatedKernelState]>,
) -> Result<
    (
        ConicProblem,
        SplitConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    if !requested_margin.is_finite() || requested_margin <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "cone-repair requested margin must be finite and positive".into(),
        ));
    }
    if !margin_cap.is_finite() || margin_cap <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "cone-repair margin cap must be finite and positive".into(),
        ));
    }
    if requested_margin > margin_cap {
        return Err(SplitExactAuditError::Repair(
            "cone-repair requested margin cannot exceed its cap".into(),
        ));
    }
    if !gram_scale_target.is_finite() || gram_scale_target <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "cone-repair Gram scale target must be finite and positive".into(),
        ));
    }
    const AFFINE_CORRECTION_RADIUS: f64 = 1.0;
    const GRAM_CORRECTION_RADIUS: f64 = 0.01;
    // Native-bar repair previously stopped with a 1e-8-scale primal residual,
    // large enough for the subsequent exact projection to reopen singular Gram
    // faces. Scaling only Zero-cone rows leaves the feasible set unchanged but
    // makes that residual expensive relative to the PSD rows.
    const AFFINE_CONSTRAINT_SCALE: f64 = 1e4;
    let input_parse_started = std::time::Instant::now();
    let layout = validate_layout(certificate)?;
    let multipliers = flattened_multipliers(certificate)?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let gram_refs = flattened_grams(certificate);
    let parsed_grams = parse_gram_refs(&gram_refs, &layout.dimensions)?;
    let parsed_kernels = parse_split_rotated_kernels(kernels.unwrap_or(&[]), &layout.dimensions)?;
    let mut kernel_by_block = vec![None; layout.dimensions.len()];
    for (index, state) in parsed_kernels.iter().enumerate() {
        kernel_by_block[state.block] = Some(index);
    }
    let exact_input_parse_wall_seconds = input_parse_started.elapsed().as_secs_f64();
    let identity_started = std::time::Instant::now();
    let identity = reconstructed_identity_from_parsed(
        &layout.model,
        &multipliers,
        &normalization,
        &parsed_grams,
    );
    let exact_identity_reconstruction_wall_seconds = identity_started.elapsed().as_secs_f64();
    let bound = reconstructed_bound(&layout.model, &multipliers, &normalization);
    let coefficient_count = layout.model.coefficient_count();
    let bound_row = coefficient_count;
    let active = active_parsed_gram_blocks(&parsed_grams);
    // Exact zero diagonals define a PSD face: their complete rows and columns
    // must remain zero. Excluding those coordinates lets a later cone pass
    // reclose affine identities after facial reduction without reopening the
    // selected face.
    let vulnerable_threshold = 10.0 * requested_margin;
    let reconstructed_minima = parsed_grams
        .iter()
        .zip(&layout.dimensions)
        .zip(&active)
        .map(|((matrix, &dimension), &is_active)| {
            if is_active {
                Ok(Some(reconstructed_parsed_matrix_minimum(
                    matrix, dimension,
                )?))
            } else {
                Ok(None)
            }
        })
        .collect::<Result<Vec<_>, SplitExactAuditError>>()?;
    let vulnerable = reconstructed_minima
        .iter()
        .map(|minimum| minimum.is_some_and(|minimum| minimum < vulnerable_threshold))
        .collect::<Vec<_>>();
    // Some exact dual faces contain nonzero but necessarily singular Grams.
    // Keep those blocks PSD without falsely demanding strict definiteness.
    // Optimize a common margin only for materially negative blocks, while
    // preserving the requested fixed cushion on already-interior blocks.
    let repaired_margin = reconstructed_minima
        .iter()
        .enumerate()
        .map(|(block, minimum)| {
            kernel_by_block[block].is_some()
                || minimum.is_some_and(|minimum| minimum <= -requested_margin)
        })
        .collect::<Vec<_>>();
    let repair_active = active
        .iter()
        .enumerate()
        .map(|(block, &is_active)| {
            is_active
                && (allowed_grams.is_none_or(|allowed| allowed[block]) || repaired_margin[block])
        })
        .collect::<Vec<_>>();
    let active_rows = active_parsed_gram_rows(&parsed_grams);
    let (mut all_gram_columns, full_active_gram_coordinate_count) = all_gram_repair_columns(
        &layout.model,
        &layout.dimensions,
        &repair_active,
        Some(&active_rows),
    );
    let kernel_row_start = coefficient_count + 1;
    let (_kernel_row_offset_by_block, kernel_equation_count) =
        augment_gram_columns_with_kernel_equalities(
            &mut all_gram_columns,
            &parsed_kernels,
            &layout.dimensions,
            &active_rows,
            kernel_row_start,
        );
    let preserved_margin = reconstructed_minima
        .iter()
        .enumerate()
        .map(|(block, minimum)| {
            kernel_by_block[block].is_none()
                && minimum.is_some_and(|minimum| minimum >= vulnerable_threshold)
        })
        .collect::<Vec<_>>();
    let strict_margin = repaired_margin
        .iter()
        .zip(&preserved_margin)
        .map(|(&repaired, &preserved)| repaired || preserved)
        .collect::<Vec<_>>();
    let mut vulnerable_coefficients = HashSet::new();
    for column in &all_gram_columns {
        let RepairVariable::Gram { block, .. } = column.variable else {
            unreachable!("Gram column builder returned a non-Gram variable")
        };
        if repaired_margin[block] {
            vulnerable_coefficients.extend(column.coefficients.keys().copied());
        }
    }
    let mut signatures = HashSet::new();
    let mut signature_basis_coordinate_count = 0;
    let expanded_neighbor_coordinate_count = 0;
    let gram_columns = all_gram_columns
        .into_iter()
        .filter(|column| {
            let RepairVariable::Gram {
                row, column: col, ..
            } = column.variable
            else {
                unreachable!("Gram column builder returned a non-Gram variable")
            };
            let signature = column
                .coefficients
                .iter()
                .map(|(&position, &value)| (position, value))
                .collect::<Vec<_>>();
            let first_with_signature = signatures.insert(signature);
            let in_signature_basis = row == col || first_with_signature;
            if in_signature_basis {
                signature_basis_coordinate_count += 1;
                return true;
            }
            false
        })
        .collect::<Vec<_>>();
    let restricted_gram_coordinate_count = gram_columns.len();
    let mut columns = affine_repair_columns(&layout.model, bound_row);
    columns.extend(gram_columns);
    let variables = columns
        .iter()
        .map(|column| column.variable)
        .collect::<Vec<_>>();
    let margin_variable = variables.len();
    let q = vec![0.0; margin_variable + 1];
    // Scale the fixed common margin to [0, 1]. Keeping the PSD rows near unit
    // scale prevents a useful 1e-7 margin from being hidden beneath the conic
    // solver's absolute tolerances.
    let margin_scale = margin_cap;
    let gram_constraint_scale = (gram_scale_target / requested_margin).max(1.0);

    let mut sparse = BTreeMap::<(usize, usize), f64>::new();
    for (column, repair) in columns.iter().enumerate() {
        for (&row, value) in &repair.coefficients {
            let value = AFFINE_CONSTRAINT_SCALE * value.to_f64();
            if value != 0.0 {
                *sparse.entry((column, row)).or_default() += value;
            }
        }
    }
    let mut b = identity
        .iter()
        .map(|value| {
            finite(&value.neg(), "exact identity residual")
                .map(|value| AFFINE_CONSTRAINT_SCALE * value)
        })
        .collect::<Result<Vec<_>, _>>()?;
    b.push(AFFINE_CONSTRAINT_SCALE * finite(&target.sub(&bound), "exact bound correction")?);
    b.extend(
        exact_kernel_residuals(&parsed_grams, &parsed_kernels, &layout.dimensions)
            .iter()
            .map(|value| {
                finite(&value.neg(), "exact rotated-kernel residual")
                    .map(|value| AFFINE_CONSTRAINT_SCALE * value)
            })
            .collect::<Result<Vec<_>, _>>()?,
    );
    debug_assert_eq!(b.len(), coefficient_count + 1 + kernel_equation_count);
    let mut cones = vec![Cone::Zero(b.len())];
    let coordinate_variables = variables
        .iter()
        .enumerate()
        .filter_map(|(variable, repair)| match *repair {
            RepairVariable::Gram { block, row, column } => Some(((block, row, column), variable)),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let variable_gram_blocks = coordinate_variables
        .keys()
        .map(|&(block, _, _)| block)
        .collect::<HashSet<_>>();
    // A PSD block that has no repair coordinate is constant in this advisory
    // problem. Sending that redundant cone to MOSEK bloats the native-bar KKT
    // system without constraining a variable. Keep every block that can move,
    // plus a materially negative fixed block so infeasibility is not hidden.
    // Exact affine closure and the optimizer-independent LDL audit still check
    // every Gram in the certificate after the advisory solve.
    let constrained_grams =
        cone_constrained_gram_blocks(&active, &repaired_margin, &variable_gram_blocks);
    let constrained_gram_coordinate_count = constrained_grams
        .iter()
        .zip(&layout.dimensions)
        .filter_map(|(&constrained, &dimension)| {
            constrained.then_some(dimension * (dimension + 1) / 2)
        })
        .sum();
    let block_power_sum = |selected: &[bool], power: u32| {
        selected
            .iter()
            .zip(&layout.dimensions)
            .filter_map(|(&selected, &dimension)| selected.then_some((dimension as u64).pow(power)))
            .sum()
    };
    let mut row_offset = b.len();
    for (block, ((matrix, &dimension), &is_active)) in parsed_grams
        .iter()
        .zip(&layout.dimensions)
        .zip(&active)
        .enumerate()
    {
        if !is_active || !constrained_grams[block] {
            continue;
        }
        for column in 0..dimension {
            for row in 0..=column {
                let scale = if row == column {
                    1.0
                } else {
                    std::f64::consts::SQRT_2
                };
                let base = finite(&parsed_gram_entry(matrix, row, column), "exact Gram entry")?;
                let fixed_margin = if kernel_by_block[block].is_some() {
                    0.0
                } else if row == column && preserved_margin[block] {
                    requested_margin
                } else {
                    0.0
                };
                b.push(gram_constraint_scale * scale * (base - fixed_margin));
                let cone_row = row_offset + column * (column + 1) / 2 + row;
                if let Some(&variable) = coordinate_variables.get(&(block, row, column)) {
                    sparse.insert((variable, cone_row), -gram_constraint_scale * scale);
                }
                if repaired_margin[block] {
                    let projector = kernel_by_block[block]
                        .map(|index| {
                            parsed_kernels[index].projector[row][column]
                                .to_f64()
                                .filter(|value| value.is_finite())
                                .ok_or_else(|| {
                                    SplitExactAuditError::Repair(format!(
                                        "rotated-kernel block {block} projector entry cannot be represented as finite f64"
                                    ))
                                })
                        })
                        .transpose()?
                        .unwrap_or(if row == column { 1.0 } else { 0.0 });
                    let value = gram_constraint_scale * scale * margin_scale * projector;
                    if value != 0.0 {
                        sparse.insert((margin_variable, cone_row), value);
                    }
                }
            }
        }
        let cone_dimension = dimension * (dimension + 1) / 2;
        cones.push(Cone::PsdTriangle(dimension));
        row_offset += cone_dimension;
    }
    if correction_bounds_enforced {
        let bounds_start = row_offset;
        for (variable, repair) in variables.iter().enumerate() {
            let radius = match repair {
                RepairVariable::Equality(_) | RepairVariable::Normalization => {
                    AFFINE_CORRECTION_RADIUS
                }
                RepairVariable::Gram { .. } => GRAM_CORRECTION_RADIUS,
            };
            b.push(radius);
            sparse.insert((variable, row_offset), 1.0);
            row_offset += 1;
            b.push(radius);
            sparse.insert((variable, row_offset), -1.0);
            row_offset += 1;
        }
        b.push(0.0);
        sparse.insert((margin_variable, row_offset), -1.0);
        row_offset += 1;
        b.push(1.0);
        sparse.insert((margin_variable, row_offset), 1.0);
        row_offset += 1;
        cones.push(Cone::Nonnegative(row_offset - bounds_start));
    }
    b.push(requested_margin / margin_scale);
    sparse.insert((margin_variable, row_offset), 1.0);
    row_offset += 1;
    cones.push(Cone::Zero(1));

    let entries = sparse
        .into_iter()
        .filter_map(|((column, row), value)| (value != 0.0).then_some((row, column, value)))
        .collect();
    let problem = ConicProblem {
        q,
        a: SparseMatrix {
            rows: row_offset,
            cols: margin_variable + 1,
            entries,
        },
        b,
        cones,
    };
    problem.validate().map_err(SplitExactAuditError::Model)?;
    let diagnostics = SplitConeRepairDiagnostics {
        coefficient_count,
        active_gram_count: active.iter().filter(|&&value| value).count(),
        zero_gram_count: active.iter().filter(|&&value| !value).count(),
        repair_gram_count: repair_active.iter().filter(|&&value| value).count(),
        constrained_gram_count: constrained_grams.iter().filter(|&&value| value).count(),
        fixed_gram_count: active
            .iter()
            .zip(&constrained_grams)
            .filter(|(active, constrained)| **active && !**constrained)
            .count(),
        full_active_gram_coordinate_count,
        constrained_gram_coordinate_count,
        active_gram_square_count: block_power_sum(&active, 2),
        constrained_gram_square_count: block_power_sum(&constrained_grams, 2),
        active_gram_cube_count: block_power_sum(&active, 3),
        constrained_gram_cube_count: block_power_sum(&constrained_grams, 3),
        restricted_gram_coordinate_count,
        signature_basis_coordinate_count,
        vulnerable_gram_count: vulnerable.iter().filter(|&&value| value).count(),
        strict_margin_gram_count: strict_margin.iter().filter(|&&value| value).count(),
        repaired_margin_gram_count: repaired_margin.iter().filter(|&&value| value).count(),
        preserved_margin_gram_count: preserved_margin.iter().filter(|&&value| value).count(),
        semidefinite_face_gram_count: active
            .iter()
            .zip(&strict_margin)
            .filter(|(active, strict)| **active && !**strict)
            .count(),
        vulnerable_coefficient_count: vulnerable_coefficients.len(),
        expanded_neighbor_coordinate_count,
        correction_variable_count: margin_variable,
        cone_row_count: row_offset,
        rotated_kernel_gram_count: parsed_kernels.len(),
        rotated_kernel_equation_count: kernel_equation_count,
        initial_maximum_identity_residual: identity
            .iter()
            .map(|value| finite(value, "exact identity residual").map(f64::abs))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .fold(0.0, f64::max),
        initial_bound: finite(&bound, "exact endpoint bound")?,
        target: finite(&target, "exact target")?,
        affine_constraint_scale: AFFINE_CONSTRAINT_SCALE,
        gram_constraint_scale,
        margin_variable_scale: margin_scale,
        affine_correction_radius: AFFINE_CORRECTION_RADIUS,
        gram_correction_radius: GRAM_CORRECTION_RADIUS,
        correction_bounds_enforced,
        fixed_common_margin: Some(requested_margin),
        margin_cap,
        exact_input_parse_wall_seconds,
        exact_identity_reconstruction_wall_seconds,
    };
    Ok((
        problem,
        SplitConeRepairPlan {
            variables,
            margin_variable,
            margin_scale,
        },
        diagnostics,
    ))
}

pub fn build_split_rotated_bar_cone_repair_problem_scaled(
    certificate: &SplitExactDualCertificate,
    faces: &[SplitFaceBlock],
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
) -> Result<
    (
        ConicProblem,
        SplitRotatedConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    build_split_rotated_cone_repair_problem_impl(
        certificate,
        faces,
        requested_margin,
        margin_cap,
        gram_scale_target,
        None,
    )
}

pub fn build_split_rotated_bar_cone_repair_problem_scaled_restricted(
    certificate: &SplitExactDualCertificate,
    faces: &[SplitFaceBlock],
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
    repair_gram_blocks: &[usize],
) -> Result<
    (
        ConicProblem,
        SplitRotatedConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    let repair_grams = split_gram_selection_mask(certificate, repair_gram_blocks)?;
    build_split_rotated_cone_repair_problem_impl(
        certificate,
        faces,
        requested_margin,
        margin_cap,
        gram_scale_target,
        Some(&repair_grams),
    )
}

fn build_split_rotated_cone_repair_problem_impl(
    certificate: &SplitExactDualCertificate,
    faces: &[SplitFaceBlock],
    requested_margin: f64,
    margin_cap: f64,
    gram_scale_target: f64,
    allowed_grams: Option<&[bool]>,
) -> Result<
    (
        ConicProblem,
        SplitRotatedConeRepairPlan,
        SplitConeRepairDiagnostics,
    ),
    SplitExactAuditError,
> {
    if !requested_margin.is_finite() || requested_margin <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "cone-repair requested margin must be finite and positive".into(),
        ));
    }
    if !margin_cap.is_finite() || margin_cap <= 0.0 || requested_margin > margin_cap {
        return Err(SplitExactAuditError::Repair(
            "cone-repair margin cap must be finite, positive, and at least the requested margin"
                .into(),
        ));
    }
    if !gram_scale_target.is_finite() || gram_scale_target <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "cone-repair Gram scale target must be finite and positive".into(),
        ));
    }
    const AFFINE_CONSTRAINT_SCALE: f64 = 1e4;
    let input_parse_started = std::time::Instant::now();
    let layout = validate_layout(certificate)?;
    let multipliers = flattened_multipliers(certificate)?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let gram_refs = flattened_grams(certificate);
    let parsed_grams = parse_gram_refs(&gram_refs, &layout.dimensions)?;
    let parsed_faces = parse_face_blocks(faces, &layout.dimensions)?;
    for (block, (face, gram)) in parsed_faces.iter().zip(&parsed_grams).enumerate() {
        let reconstructed = reconstruct_face_gram(face);
        for (row, entries) in reconstructed.iter().enumerate() {
            for (column, entry) in entries.iter().enumerate() {
                if ScalarParser::parse(entry)? != parsed_gram_entry(gram, row, column) {
                    return Err(SplitExactAuditError::Repair(format!(
                        "rotated face block {block} does not exactly reconstruct its certificate Gram"
                    )));
                }
            }
        }
    }
    let exact_input_parse_wall_seconds = input_parse_started.elapsed().as_secs_f64();
    let identity_started = std::time::Instant::now();
    let identity = reconstructed_identity_from_parsed(
        &layout.model,
        &multipliers,
        &normalization,
        &parsed_grams,
    );
    let exact_identity_reconstruction_wall_seconds = identity_started.elapsed().as_secs_f64();
    let bound = reconstructed_bound(&layout.model, &multipliers, &normalization);
    let coefficient_count = layout.model.coefficient_count();
    let bound_row = coefficient_count;
    let face_ranks = parsed_faces
        .iter()
        .map(|face| face.coordinates.len())
        .collect::<Vec<_>>();
    let active = face_ranks.iter().map(|&rank| rank != 0).collect::<Vec<_>>();
    let vulnerable_threshold = 10.0 * requested_margin;
    let reconstructed_minima = parsed_faces
        .iter()
        .zip(&active)
        .map(|(face, &is_active)| {
            if !is_active {
                return Ok(None);
            }
            let rank = face.coordinates.len();
            let matrix = ParsedGram::Quadratic(face.coordinates.clone());
            reconstructed_parsed_matrix_minimum(&matrix, rank).map(Some)
        })
        .collect::<Result<Vec<_>, SplitExactAuditError>>()?;
    let vulnerable = reconstructed_minima
        .iter()
        .map(|minimum| minimum.is_some_and(|minimum| minimum < vulnerable_threshold))
        .collect::<Vec<_>>();
    let preserved_margin = reconstructed_minima
        .iter()
        .map(|minimum| minimum.is_some_and(|minimum| minimum >= vulnerable_threshold))
        .collect::<Vec<_>>();
    // Unlike an unreduced Gram, every active H block should be interior on its
    // selected face. Raise each vulnerable H to the requested common margin;
    // already well-interior blocks retain that margin as a fixed cushion.
    let repaired_margin = active
        .iter()
        .zip(&preserved_margin)
        .map(|(&is_active, &preserved)| is_active && !preserved)
        .collect::<Vec<_>>();
    let strict_margin = active.clone();
    let repair_active = active
        .iter()
        .enumerate()
        .map(|(block, &is_active)| {
            is_active
                && (allowed_grams.is_none_or(|allowed| allowed[block]) || repaired_margin[block])
        })
        .collect::<Vec<_>>();

    let mut full_active_gram_coordinate_count = 0;
    let mut all_gram_columns = Vec::new();
    for (block, (&rank, &is_active)) in face_ranks.iter().zip(&repair_active).enumerate() {
        if !is_active {
            continue;
        }
        full_active_gram_coordinate_count += rank * (rank + 1) / 2;
        let active_rows = (0..rank)
            .map(|row| !parsed_faces[block].coordinates[row][row].is_zero())
            .collect::<Vec<_>>();
        for distance in 0..rank {
            for row in 0..rank - distance {
                let column = row + distance;
                if !active_rows[row] || !active_rows[column] {
                    continue;
                }
                let coefficients = face_coordinate_column(
                    &layout.model,
                    block,
                    &parsed_faces[block].basis,
                    row,
                    column,
                );
                if coefficients.is_empty() {
                    continue;
                }
                all_gram_columns.push(RotatedConeRepairColumn {
                    variable: FaceRepairVariable::Coordinate { block, row, column },
                    coefficients,
                });
            }
        }
    }
    let mut vulnerable_coefficients = HashSet::new();
    for column in &all_gram_columns {
        let FaceRepairVariable::Coordinate { block, .. } = column.variable else {
            unreachable!("rotated Gram column has a non-coordinate variable")
        };
        if repaired_margin[block] {
            vulnerable_coefficients.extend(column.coefficients.keys().copied());
        }
    }
    let mut signatures = HashSet::new();
    let mut signature_basis_coordinate_count = 0;
    let gram_columns = all_gram_columns
        .into_iter()
        .filter(|column| {
            let FaceRepairVariable::Coordinate {
                row, column: col, ..
            } = column.variable
            else {
                unreachable!("rotated Gram column has a non-coordinate variable")
            };
            let signature = column
                .coefficients
                .iter()
                .map(|(&position, value)| (position, value.to_string()))
                .collect::<Vec<_>>();
            let first_with_signature = signatures.insert(signature);
            if row == col || first_with_signature {
                signature_basis_coordinate_count += 1;
                true
            } else {
                false
            }
        })
        .collect::<Vec<_>>();
    let restricted_gram_coordinate_count = gram_columns.len();

    let mut columns = Vec::with_capacity(layout.model.rows.len() + 1 + gram_columns.len());
    for (index, equality) in layout.model.rows.iter().enumerate() {
        let mut coefficients = BTreeMap::new();
        for &(position, value) in &equality.coefficients {
            add_assign(
                coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
                &BigQsqrt2::from_small(value),
            );
        }
        add_assign(
            coefficients
                .entry(bound_row)
                .or_insert_with(BigQsqrt2::zero),
            &BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(-equality.rhs))),
        );
        columns.push(RotatedConeRepairColumn {
            variable: FaceRepairVariable::Equality(index),
            coefficients,
        });
    }
    let mut normalization_coefficients = BTreeMap::new();
    layout.model.for_each_normalization_position(|position| {
        normalization_coefficients.insert(position, BigQsqrt2::from_rational(BigRational::one()));
    });
    normalization_coefficients.insert(
        bound_row,
        BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(-1))),
    );
    columns.push(RotatedConeRepairColumn {
        variable: FaceRepairVariable::Normalization,
        coefficients: normalization_coefficients,
    });
    columns.extend(gram_columns);
    let variables = columns
        .iter()
        .map(|column| column.variable)
        .collect::<Vec<_>>();
    let margin_variable = variables.len();
    let margin_scale = margin_cap;
    let gram_constraint_scale = (gram_scale_target / requested_margin).max(1.0);
    let mut sparse = BTreeMap::<(usize, usize), f64>::new();
    for (column, repair) in columns.iter().enumerate() {
        for (&row, value) in &repair.coefficients {
            let value = AFFINE_CONSTRAINT_SCALE * finite(value, "rotated face coefficient")?;
            if value != 0.0 {
                *sparse.entry((column, row)).or_default() += value;
            }
        }
    }
    let mut b = identity
        .iter()
        .map(|value| {
            finite(&value.neg(), "exact identity residual")
                .map(|value| AFFINE_CONSTRAINT_SCALE * value)
        })
        .collect::<Result<Vec<_>, _>>()?;
    b.push(AFFINE_CONSTRAINT_SCALE * finite(&target.sub(&bound), "exact bound correction")?);
    let mut cones = vec![Cone::Zero(coefficient_count + 1)];
    let coordinate_variables = variables
        .iter()
        .enumerate()
        .filter_map(|(variable, repair)| match *repair {
            FaceRepairVariable::Coordinate { block, row, column } => {
                Some(((block, row, column), variable))
            }
            FaceRepairVariable::Equality(_) | FaceRepairVariable::Normalization => None,
        })
        .collect::<HashMap<_, _>>();
    let variable_gram_blocks = coordinate_variables
        .keys()
        .map(|&(block, _, _)| block)
        .collect::<HashSet<_>>();
    let constrained_grams =
        cone_constrained_gram_blocks(&active, &repaired_margin, &variable_gram_blocks);
    let constrained_gram_coordinate_count = constrained_grams
        .iter()
        .zip(&face_ranks)
        .filter_map(|(&constrained, &rank)| constrained.then_some(rank * (rank + 1) / 2))
        .sum();
    let block_power_sum = |selected: &[bool], power: u32| {
        selected
            .iter()
            .zip(&face_ranks)
            .filter_map(|(&selected, &rank)| selected.then_some((rank as u64).pow(power)))
            .sum()
    };
    let mut row_offset = b.len();
    for (block, (face, &is_active)) in parsed_faces.iter().zip(&active).enumerate() {
        if !is_active || !constrained_grams[block] {
            continue;
        }
        let rank = face.coordinates.len();
        for column in 0..rank {
            for row in 0..=column {
                let scale = if row == column {
                    1.0
                } else {
                    std::f64::consts::SQRT_2
                };
                let base = finite(&face.coordinates[row][column], "exact face coordinate")?;
                let fixed_margin = if row == column && preserved_margin[block] {
                    requested_margin
                } else {
                    0.0
                };
                b.push(gram_constraint_scale * scale * (base - fixed_margin));
                let cone_row = row_offset + column * (column + 1) / 2 + row;
                if let Some(&variable) = coordinate_variables.get(&(block, row, column)) {
                    sparse.insert((variable, cone_row), -gram_constraint_scale * scale);
                }
                if row == column && repaired_margin[block] {
                    sparse.insert(
                        (margin_variable, cone_row),
                        gram_constraint_scale * margin_scale,
                    );
                }
            }
        }
        cones.push(Cone::PsdTriangle(rank));
        row_offset += rank * (rank + 1) / 2;
    }
    b.push(requested_margin / margin_scale);
    sparse.insert((margin_variable, row_offset), 1.0);
    row_offset += 1;
    cones.push(Cone::Zero(1));
    let entries = sparse
        .into_iter()
        .filter_map(|((column, row), value)| (value != 0.0).then_some((row, column, value)))
        .collect();
    let problem = ConicProblem {
        q: vec![0.0; margin_variable + 1],
        a: SparseMatrix {
            rows: row_offset,
            cols: margin_variable + 1,
            entries,
        },
        b,
        cones,
    };
    problem.validate().map_err(SplitExactAuditError::Model)?;
    let diagnostics = SplitConeRepairDiagnostics {
        coefficient_count,
        active_gram_count: active.iter().filter(|&&value| value).count(),
        zero_gram_count: active.iter().filter(|&&value| !value).count(),
        repair_gram_count: repair_active.iter().filter(|&&value| value).count(),
        constrained_gram_count: constrained_grams.iter().filter(|&&value| value).count(),
        fixed_gram_count: active
            .iter()
            .zip(&constrained_grams)
            .filter(|(active, constrained)| **active && !**constrained)
            .count(),
        full_active_gram_coordinate_count,
        constrained_gram_coordinate_count,
        active_gram_square_count: block_power_sum(&active, 2),
        constrained_gram_square_count: block_power_sum(&constrained_grams, 2),
        active_gram_cube_count: block_power_sum(&active, 3),
        constrained_gram_cube_count: block_power_sum(&constrained_grams, 3),
        restricted_gram_coordinate_count,
        signature_basis_coordinate_count,
        vulnerable_gram_count: vulnerable.iter().filter(|&&value| value).count(),
        strict_margin_gram_count: strict_margin.iter().filter(|&&value| value).count(),
        repaired_margin_gram_count: repaired_margin.iter().filter(|&&value| value).count(),
        preserved_margin_gram_count: preserved_margin.iter().filter(|&&value| value).count(),
        semidefinite_face_gram_count: active
            .iter()
            .zip(&strict_margin)
            .filter(|(active, strict)| **active && !**strict)
            .count(),
        vulnerable_coefficient_count: vulnerable_coefficients.len(),
        expanded_neighbor_coordinate_count: 0,
        correction_variable_count: margin_variable,
        cone_row_count: row_offset,
        rotated_kernel_gram_count: 0,
        rotated_kernel_equation_count: 0,
        initial_maximum_identity_residual: identity
            .iter()
            .map(|value| finite(value, "exact identity residual").map(f64::abs))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .fold(0.0, f64::max),
        initial_bound: finite(&bound, "exact endpoint bound")?,
        target: finite(&target, "exact target")?,
        affine_constraint_scale: AFFINE_CONSTRAINT_SCALE,
        gram_constraint_scale,
        margin_variable_scale: margin_scale,
        affine_correction_radius: 1.0,
        gram_correction_radius: 0.01,
        correction_bounds_enforced: false,
        fixed_common_margin: Some(requested_margin),
        margin_cap,
        exact_input_parse_wall_seconds,
        exact_identity_reconstruction_wall_seconds,
    };
    Ok((
        problem,
        SplitRotatedConeRepairPlan {
            variables,
            margin_variable,
            margin_scale,
        },
        diagnostics,
    ))
}

fn cone_constrained_gram_blocks(
    active: &[bool],
    repaired_margin: &[bool],
    variable_blocks: &HashSet<usize>,
) -> Vec<bool> {
    active
        .iter()
        .enumerate()
        .map(|(block, &is_active)| {
            is_active && (variable_blocks.contains(&block) || repaired_margin[block])
        })
        .collect()
}

pub fn apply_split_cone_repair(
    certificate: &mut SplitExactDualCertificate,
    plan: &SplitConeRepairPlan,
    corrections: &[String],
) -> Result<f64, SplitExactAuditError> {
    if corrections.len() != plan.margin_variable + 1 {
        return Err(SplitExactAuditError::Repair(format!(
            "cone repair returned {} variables, expected {}",
            corrections.len(),
            plan.margin_variable + 1
        )));
    }
    validate_layout(certificate)?;
    let mut multipliers = flattened_multipliers(certificate)?;
    let mut normalization = ScalarParser::parse(&certificate.normalization)?;
    let mut gram_corrections = BTreeMap::<usize, Vec<(usize, usize, BigQsqrt2)>>::new();
    for (&variable, correction) in plan.variables.iter().zip(corrections) {
        let correction = ScalarParser::parse(correction)?;
        match variable {
            RepairVariable::Equality(index) => {
                multipliers[index] = multipliers[index].add(&correction);
            }
            RepairVariable::Normalization => normalization = normalization.add(&correction),
            RepairVariable::Gram { block, row, column } => {
                gram_corrections
                    .entry(block)
                    .or_default()
                    .push((row, column, correction));
            }
        }
    }
    for (block, matrix) in certificate
        .occupation_grams_by_cell
        .iter_mut()
        .flatten()
        .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
        .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
        .enumerate()
    {
        let Some(updates) = gram_corrections.remove(&block) else {
            continue;
        };
        for (row, column, correction) in updates {
            let current = ScalarParser::parse(&matrix[row][column])?;
            let repaired = current.add(&correction).to_string();
            matrix[row][column] = repaired.clone();
            matrix[column][row] = repaired;
        }
    }
    debug_assert!(gram_corrections.is_empty());
    for (target, value) in certificate
        .liouville_multipliers_by_cell
        .iter_mut()
        .flatten()
        .zip(multipliers)
    {
        *target = value.to_string();
    }
    certificate.normalization = normalization.to_string();
    Ok(finite(
        &ScalarParser::parse(&corrections[plan.margin_variable])?,
        "cone repair margin",
    )? * plan.margin_scale)
}

pub fn apply_split_rotated_cone_repair(
    certificate: &mut SplitExactDualCertificate,
    faces: &mut [SplitFaceBlock],
    plan: &SplitRotatedConeRepairPlan,
    corrections: &[String],
) -> Result<f64, SplitExactAuditError> {
    if corrections.len() != plan.margin_variable + 1 {
        return Err(SplitExactAuditError::Repair(format!(
            "rotated cone repair returned {} variables, expected {}",
            corrections.len(),
            plan.margin_variable + 1
        )));
    }
    let layout = validate_layout(certificate)?;
    let mut multipliers = flattened_multipliers(certificate)?;
    let mut normalization = ScalarParser::parse(&certificate.normalization)?;
    let mut parsed_faces = parse_face_blocks(faces, &layout.dimensions)?;
    for (&variable, correction) in plan.variables.iter().zip(corrections) {
        let correction = ScalarParser::parse(correction)?;
        apply_face_correction(
            variable,
            &correction,
            &mut multipliers,
            &mut normalization,
            &mut parsed_faces,
        );
    }
    let gram_values = parsed_faces
        .iter()
        .map(reconstruct_face_gram)
        .collect::<Vec<_>>();
    write_back(
        certificate,
        &layout.model,
        &multipliers,
        &normalization,
        gram_values,
    );
    for (face, parsed) in faces.iter_mut().zip(parsed_faces) {
        face.coordinates = parsed
            .coordinates
            .into_iter()
            .map(|row| row.into_iter().map(|value| value.to_string()).collect())
            .collect();
    }
    Ok(finite(
        &ScalarParser::parse(&corrections[plan.margin_variable])?,
        "rotated cone repair margin",
    )? * plan.margin_scale)
}

/// Apply the existing diagonal facial-reduction rule to the inner `H`
/// coordinates of a rotated face, then reconstruct every exact Gram. For a
/// coordinate-selector basis this is exactly the legacy Gram-row operation.
pub fn zero_small_split_face_coordinate_rows(
    certificate: &mut SplitExactDualCertificate,
    faces: &mut [SplitFaceBlock],
    threshold: f64,
) -> Result<usize, SplitExactAuditError> {
    if !threshold.is_finite() || threshold < 0.0 {
        return Err(SplitExactAuditError::Repair(
            "face-coordinate row zero threshold must be finite and nonnegative".into(),
        ));
    }
    let layout = validate_layout(certificate)?;
    let mut zeroed = 0;
    for face in faces.iter_mut() {
        let rank = face.coordinates.len();
        let mut keep = Vec::with_capacity(rank);
        for row in 0..rank {
            let row_is_zero = face.coordinates[row]
                .iter()
                .take(rank)
                .all(|value| ScalarParser::parse(value).is_ok_and(|value| value.is_zero()));
            if row_is_zero {
                continue;
            }
            let diagonal = ScalarParser::parse(&face.coordinates[row][row])?;
            if finite(&diagonal, "face-coordinate diagonal")?.abs() > threshold {
                keep.push(row);
            } else {
                zeroed += 1;
            }
        }
        face.basis = face
            .basis
            .iter()
            .map(|values| keep.iter().map(|&column| values[column].clone()).collect())
            .collect();
        face.coordinates = keep
            .iter()
            .map(|&row| {
                keep.iter()
                    .map(|&column| face.coordinates[row][column].clone())
                    .collect()
            })
            .collect();
    }
    let parsed_faces = parse_face_blocks(faces, &layout.dimensions)?;
    write_face_grams(certificate, &layout, &parsed_faces)?;
    Ok(zeroed)
}

/// Fix numerically vulnerable Gram rows to the exact zero face after the cone
/// solve. A PSD matrix with a zero diagonal has an identically zero row and
/// column. This remains a candidate facial reduction: exact affine closure and
/// the native exact LDL audit are mandatory.
pub fn zero_small_split_gram_rows(
    certificate: &mut SplitExactDualCertificate,
    threshold: f64,
) -> Result<usize, SplitExactAuditError> {
    if !threshold.is_finite() || threshold < 0.0 {
        return Err(SplitExactAuditError::Repair(
            "Gram-row zero threshold must be finite and nonnegative".into(),
        ));
    }
    let layout = validate_layout(certificate)?;
    let mut zeroed = 0;
    for (matrix, &dimension) in certificate
        .occupation_grams_by_cell
        .iter_mut()
        .flatten()
        .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
        .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
        .zip(&layout.dimensions)
    {
        let mut row = 0;
        while row < dimension {
            let diagonal = ScalarParser::parse(&matrix[row][row])?;
            if finite(&diagonal, "Gram diagonal entry")?.abs() > threshold
                || !matrix[row]
                    .iter()
                    .take(dimension)
                    .any(|entry| ScalarParser::parse(entry).is_ok_and(|value| !value.is_zero()))
            {
                row += 1;
                continue;
            }
            for entry in matrix[row].iter_mut().take(dimension) {
                *entry = "0".into();
            }
            for matrix_row in matrix.iter_mut().take(dimension) {
                matrix_row[row] = "0".into();
            }
            zeroed += 1;
            row += 1;
        }
    }
    Ok(zeroed)
}

/// Require exact coefficient closure and exact target reconstruction without
/// checking the Gram cones. This is the safe resume gate for a pre-cone
/// checkpoint; full PSD remains the responsibility of the native audit.
pub fn check_split_exact_affine_closure(
    certificate: &SplitExactDualCertificate,
) -> Result<(), SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let multipliers = flattened_multipliers(certificate)?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let grams = flattened_grams(certificate);
    let nonzero = reconstructed_identity(
        &layout.model,
        &multipliers,
        &normalization,
        &grams,
        &layout.dimensions,
    )?
    .iter()
    .filter(|value| !value.is_zero())
    .count();
    let bound = reconstructed_bound(&layout.model, &multipliers, &normalization);
    if nonzero != 0 || bound != target {
        return Err(SplitExactAuditError::Repair(format!(
            "pre-cone checkpoint has {nonzero} nonzero coefficients and bound {bound} instead of target {target}"
        )));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
enum FaceRepairVariable {
    Equality(usize),
    Normalization,
    Coordinate {
        block: usize,
        row: usize,
        column: usize,
    },
}

#[derive(Clone)]
struct ParsedFaceBlock {
    basis: Vec<Vec<BigQsqrt2>>,
    coordinates: Vec<Vec<BigQsqrt2>>,
}

fn coordinate_selector_face(matrix: &EncodedMatrix, live_rows: &[usize]) -> SplitFaceBlock {
    let dimension = matrix.len();
    let rank = live_rows.len();
    let mut basis = vec![vec!["0".into(); rank]; dimension];
    for (column, &row) in live_rows.iter().enumerate() {
        basis[row][column] = "1".into();
    }
    let coordinates = live_rows
        .iter()
        .map(|&row| {
            live_rows
                .iter()
                .map(|&column| matrix[row][column].clone())
                .collect()
        })
        .collect();
    SplitFaceBlock { basis, coordinates }
}

fn face_is_coordinate_selector(face: &SplitFaceBlock) -> bool {
    let rank = face.coordinates.len();
    let mut selected_rows = vec![false; face.basis.len()];
    for column in 0..rank {
        let mut selected = None;
        for (row, values) in face.basis.iter().enumerate() {
            match values[column].as_str() {
                "0" => {}
                "1" if selected.is_none() && !selected_rows[row] => selected = Some(row),
                _ => return false,
            }
        }
        let Some(row) = selected else {
            return false;
        };
        selected_rows[row] = true;
    }
    true
}

fn write_face_grams(
    certificate: &mut SplitExactDualCertificate,
    layout: &ValidatedLayout,
    faces: &[ParsedFaceBlock],
) -> Result<(), SplitExactAuditError> {
    let multipliers = flattened_multipliers(certificate)?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let grams = faces.iter().map(reconstruct_face_gram).collect();
    write_back(
        certificate,
        &layout.model,
        &multipliers,
        &normalization,
        grams,
    );
    Ok(())
}

/// Select exact dyadic range bases for all active Grams whose reconstructed
/// spectrum has eigenvalues below `threshold`. Existing exact-zero coordinate
/// rows are removed first through coordinate selectors. The certificate Grams
/// are replaced by the exact `F K F^T` reconstruction; this is only a candidate
/// face, and subsequent exact affine closure and PSD audits remain mandatory.
pub fn select_split_rotated_gram_faces(
    certificate: &mut SplitExactDualCertificate,
    threshold: f64,
    basis_bits: u32,
) -> Result<
    (
        Vec<SplitFaceBlock>,
        Vec<SplitRotatedFaceState>,
        SplitRotatedFaceBuildReport,
    ),
    SplitExactAuditError,
> {
    if !threshold.is_finite() || threshold <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "rotated facial threshold must be finite and positive".into(),
        ));
    }
    if basis_bits > 60 {
        return Err(SplitExactAuditError::Repair(
            "rotated facial basis precision must be at most 60 bits".into(),
        ));
    }
    let layout = validate_layout(certificate)?;
    let gram_refs = flattened_grams(certificate);
    let parsed_grams = parse_gram_refs(&gram_refs, &layout.dimensions)?;
    let mut faces = Vec::with_capacity(parsed_grams.len());
    let mut states = Vec::new();
    let mut active_gram_count = 0;
    let mut unchanged_full_face_block_count = 0;
    let mut coordinate_reduced_block_count = 0;
    let mut rotated_reduced_block_count = 0;
    let mut zero_face_block_count = 0;
    let mut discarded_direction_count = 0;
    let mut retained_direction_count = 0;
    let mut minimum_retained = f64::INFINITY;
    let mut maximum_discarded = f64::NEG_INFINITY;

    for (block, ((matrix, encoded), &dimension)) in parsed_grams
        .iter()
        .zip(&gram_refs)
        .zip(&layout.dimensions)
        .enumerate()
    {
        if matrix.is_zero_matrix() {
            zero_face_block_count += 1;
            discarded_direction_count += dimension;
            maximum_discarded = maximum_discarded.max(0.0);
            faces.push(SplitFaceBlock {
                basis: vec![Vec::new(); dimension],
                coordinates: Vec::new(),
            });
            continue;
        }
        active_gram_count += 1;
        let live_rows = (0..dimension)
            .filter(|&row| !matrix.entry_is_zero(row, row))
            .collect::<Vec<_>>();
        if live_rows.is_empty() {
            zero_face_block_count += 1;
            discarded_direction_count += dimension;
            maximum_discarded = maximum_discarded.max(0.0);
            faces.push(SplitFaceBlock {
                basis: vec![Vec::new(); dimension],
                coordinates: Vec::new(),
            });
            continue;
        }
        let live_dimension = live_rows.len();
        let numeric = DMatrix::from_fn(live_dimension, live_dimension, |row, column| {
            parsed_gram_entry(matrix, live_rows[row], live_rows[column])
                .to_f64()
                .unwrap_or(f64::NAN)
        });
        let eigen = numeric.symmetric_eigen();
        if eigen.eigenvalues.iter().any(|value| !value.is_finite()) {
            return Err(SplitExactAuditError::Repair(format!(
                "Gram block {block} has a non-finite reconstructed eigenvalue"
            )));
        }
        let retained = eigen
            .eigenvalues
            .iter()
            .enumerate()
            .filter_map(|(index, &value)| (value >= threshold).then_some(index))
            .collect::<Vec<_>>();
        for (index, &value) in eigen.eigenvalues.iter().enumerate() {
            if retained.contains(&index) {
                minimum_retained = minimum_retained.min(value);
            } else {
                maximum_discarded = maximum_discarded.max(value);
            }
        }
        retained_direction_count += retained.len();
        discarded_direction_count += dimension - retained.len();

        if retained.len() == live_dimension {
            if live_dimension == dimension {
                unchanged_full_face_block_count += 1;
            } else {
                coordinate_reduced_block_count += 1;
                maximum_discarded = maximum_discarded.max(0.0);
            }
            faces.push(coordinate_selector_face(encoded, &live_rows));
            continue;
        }
        if retained.is_empty() {
            zero_face_block_count += 1;
            let face = SplitFaceBlock {
                basis: vec![Vec::new(); dimension],
                coordinates: Vec::new(),
            };
            faces.push(face);
            continue;
        }

        rotated_reduced_block_count += 1;
        let rank = retained.len();
        let scaled_range = DMatrix::from_fn(live_dimension, rank, |row, column| {
            let eigen_column = retained[column];
            eigen.eigenvectors[(row, eigen_column)] * eigen.eigenvalues[eigen_column].sqrt()
        });
        // Put the rounded range in sparse graph form. Pivoted QR chooses an
        // invertible set of `rank` rows P, then F = B B_P^-1 has F_P = I and
        // only the `k = d-rank` non-pivot rows are dense. This preserves the
        // candidate range while reducing transformed coefficient construction
        // from dense quartic products to O(rank^2 k^2) nonzero products.
        let qr = scaled_range.transpose().col_piv_qr();
        let mut permutation = DMatrix::from_row_iterator(1, live_dimension, 0..live_dimension);
        qr.p().permute_columns(&mut permutation);
        let pivot_rows = permutation
            .row(0)
            .iter()
            .take(rank)
            .copied()
            .collect::<Vec<_>>();
        let pivot_matrix = DMatrix::from_fn(rank, rank, |row, column| {
            scaled_range[(pivot_rows[row], column)]
        });
        let pivot_inverse = pivot_matrix.clone().try_inverse().ok_or_else(|| {
            SplitExactAuditError::Repair(format!(
                "Gram block {block} retained range has no invertible floating pivot minor"
            ))
        })?;
        let graph_basis = &scaled_range * pivot_inverse;
        if graph_basis.iter().any(|value| !value.is_finite()) {
            return Err(SplitExactAuditError::Repair(format!(
                "Gram block {block} sparse range basis is not finite"
            )));
        }
        let pivot_lookup = pivot_rows
            .iter()
            .enumerate()
            .map(|(column, &row)| (row, column))
            .collect::<HashMap<_, _>>();
        let mut exact_basis = vec![vec![BigQsqrt2::zero(); rank]; dimension];
        for (live_row, &matrix_row) in live_rows.iter().enumerate() {
            if let Some(&pivot_column) = pivot_lookup.get(&live_row) {
                exact_basis[matrix_row][pivot_column] =
                    BigQsqrt2::from_rational(BigRational::one());
            } else {
                for column in 0..rank {
                    exact_basis[matrix_row][column] =
                        round_dyadic(graph_basis[(live_row, column)], basis_bits)?;
                }
            }
        }
        let numeric_coordinates = &pivot_matrix * pivot_matrix.transpose();
        // Entrywise dyadic rounding can move a numerical PSD matrix by at
        // most `rank * 2^-bits` in spectral norm. Add that amount (and the
        // selected face threshold) to the diagonal. This is an initialization
        // aid only; exact H-PSD and reconstructed G-PSD audits remain the
        // acceptance gates.
        let coordinate_shift = threshold.max((rank as f64) * 2_f64.powi(-(basis_bits as i32)));
        let coordinate_shift = round_dyadic(coordinate_shift, basis_bits)?;
        let coordinates = (0..rank)
            .map(|row| {
                (0..rank)
                    .map(|column| {
                        let mut value =
                            round_dyadic(numeric_coordinates[(row, column)], basis_bits)?;
                        if row == column {
                            value = value.add(&coordinate_shift);
                        }
                        Ok(value.to_string())
                    })
                    .collect::<Result<Vec<_>, SplitExactAuditError>>()
            })
            .collect::<Result<Vec<_>, SplitExactAuditError>>()?;
        let basis = exact_basis
            .into_iter()
            .map(|row| row.into_iter().map(|value| value.to_string()).collect())
            .collect();
        let face = SplitFaceBlock { basis, coordinates };
        states.push(SplitRotatedFaceState {
            block,
            face: face.clone(),
        });
        faces.push(face);
    }

    let parsed_faces = parse_face_blocks(&faces, &layout.dimensions)?;
    write_face_grams(certificate, &layout, &parsed_faces)?;
    if minimum_retained == f64::INFINITY {
        minimum_retained = 0.0;
    }
    if maximum_discarded == f64::NEG_INFINITY {
        maximum_discarded = 0.0;
    }
    Ok((
        faces,
        states,
        SplitRotatedFaceBuildReport {
            eigenvalue_threshold: threshold,
            basis_dyadic_bits: basis_bits,
            active_gram_count,
            unchanged_full_face_block_count,
            coordinate_reduced_block_count,
            rotated_reduced_block_count,
            zero_face_block_count,
            discarded_direction_count,
            retained_direction_count,
            minimum_retained_floating_eigenvalue: minimum_retained,
            maximum_discarded_floating_eigenvalue: maximum_discarded,
            representation: "exact dyadic sparse graph F H F^T; F=V^T has an identity pivot minor and H is initialized from a rounded floating factor product plus a dyadic spectral shift; only exact affine closure and exact PSD audits can accept the reconstructed certificate",
        },
    ))
}

/// Restore the frozen reduced faces from checkpoint state. Blocks without a
/// stored rotated state use the exact coordinate selector implied by their
/// current zero rows, so full-rank blocks do not duplicate their Grams in
/// provenance.
pub fn restore_split_rotated_gram_faces(
    certificate: &SplitExactDualCertificate,
    states: &[SplitRotatedFaceState],
) -> Result<Vec<SplitFaceBlock>, SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let gram_refs = flattened_grams(certificate);
    let parsed_grams = parse_gram_refs(&gram_refs, &layout.dimensions)?;
    let mut faces = parsed_grams
        .iter()
        .zip(&gram_refs)
        .zip(&layout.dimensions)
        .map(|((matrix, encoded), &dimension)| {
            let live_rows = (0..dimension)
                .filter(|&row| !matrix.entry_is_zero(row, row))
                .collect::<Vec<_>>();
            coordinate_selector_face(encoded, &live_rows)
        })
        .collect::<Vec<_>>();
    let mut seen = HashSet::new();
    for state in states {
        if state.block >= faces.len() {
            return Err(SplitExactAuditError::Repair(format!(
                "rotated face checkpoint block {} is outside {} Grams",
                state.block,
                faces.len()
            )));
        }
        if !seen.insert(state.block) {
            return Err(SplitExactAuditError::Repair(format!(
                "rotated face checkpoint repeats block {}",
                state.block
            )));
        }
        faces[state.block] = state.face.clone();
    }
    let parsed_faces = parse_face_blocks(&faces, &layout.dimensions)?;
    for (block, (face, matrix)) in parsed_faces.iter().zip(&parsed_grams).enumerate() {
        let reconstructed = reconstruct_face_gram(face);
        for (row, entries) in reconstructed.iter().enumerate() {
            for (column, entry) in entries.iter().enumerate() {
                if ScalarParser::parse(entry)? != parsed_gram_entry(matrix, row, column) {
                    return Err(SplitExactAuditError::Repair(format!(
                        "rotated face checkpoint block {block} does not exactly reconstruct its certificate Gram"
                    )));
                }
            }
        }
    }
    Ok(faces)
}

pub fn split_rotated_face_states(faces: &[SplitFaceBlock]) -> Vec<SplitRotatedFaceState> {
    faces
        .iter()
        .enumerate()
        .filter(|(_, face)| !face_is_coordinate_selector(face))
        .map(|(block, face)| SplitRotatedFaceState {
            block,
            face: face.clone(),
        })
        .collect()
}

fn invert_rational_matrix(
    matrix: &[Vec<BigRational>],
) -> Result<Vec<Vec<BigRational>>, SplitExactAuditError> {
    let dimension = matrix.len();
    if matrix.iter().any(|row| row.len() != dimension) {
        return Err(SplitExactAuditError::Repair(
            "rotated-kernel Gram matrix is not square".into(),
        ));
    }
    let mut augmented = matrix
        .iter()
        .enumerate()
        .map(|(row, values)| {
            values
                .iter()
                .cloned()
                .chain((0..dimension).map(|column| {
                    if row == column {
                        BigRational::one()
                    } else {
                        BigRational::zero()
                    }
                }))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    for column in 0..dimension {
        let pivot = (column..dimension)
            .find(|&row| !augmented[row][column].is_zero())
            .ok_or_else(|| {
                SplitExactAuditError::Repair(
                    "rotated-kernel columns are not exactly independent".into(),
                )
            })?;
        augmented.swap(column, pivot);
        let divisor = augmented[column][column].clone();
        for value in &mut augmented[column] {
            *value /= &divisor;
        }
        let pivot_row = augmented[column].clone();
        for (row, values) in augmented.iter_mut().enumerate() {
            if row == column || values[column].is_zero() {
                continue;
            }
            let factor = values[column].clone();
            for (value, pivot_value) in values.iter_mut().zip(&pivot_row) {
                *value -= &factor * pivot_value;
            }
        }
    }
    Ok(augmented
        .into_iter()
        .map(|row| row.into_iter().skip(dimension).collect())
        .collect())
}

fn exact_kernel_projector(
    kernel: &[Vec<BigRational>],
) -> Result<Vec<Vec<BigRational>>, SplitExactAuditError> {
    let dimension = kernel.len();
    let rank = kernel.first().map_or(0, Vec::len);
    if kernel.iter().any(|row| row.len() != rank) {
        return Err(SplitExactAuditError::Repair(
            "rotated kernel has inconsistent row lengths".into(),
        ));
    }
    if rank == 0 {
        return Ok((0..dimension)
            .map(|row| {
                (0..dimension)
                    .map(|column| {
                        if row == column {
                            BigRational::one()
                        } else {
                            BigRational::zero()
                        }
                    })
                    .collect()
            })
            .collect());
    }
    let gram = (0..rank)
        .map(|row| {
            (0..rank)
                .map(|column| {
                    kernel
                        .iter()
                        .map(|values| &values[row] * &values[column])
                        .sum()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let inverse = invert_rational_matrix(&gram)?;
    let range = (0..dimension)
        .map(|row| {
            (0..rank)
                .map(|column| {
                    (0..rank)
                        .map(|inner| &kernel[row][inner] * &inverse[inner][column])
                        .sum::<BigRational>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut projector = vec![vec![BigRational::zero(); dimension]; dimension];
    for row in 0..dimension {
        for column in 0..dimension {
            let removed = (0..rank)
                .map(|inner| &range[row][inner] * &kernel[column][inner])
                .sum::<BigRational>();
            projector[row][column] = if row == column {
                BigRational::one() - removed
            } else {
                -removed
            };
        }
    }
    Ok(projector)
}

fn parse_split_rotated_kernels(
    states: &[SplitRotatedKernelState],
    dimensions: &[usize],
) -> Result<Vec<ParsedRotatedKernelState>, SplitExactAuditError> {
    let mut seen = HashSet::new();
    for state in states {
        let dimension = dimensions.get(state.block).copied().ok_or_else(|| {
            SplitExactAuditError::Repair(format!(
                "rotated-kernel checkpoint block {} is outside {} Grams",
                state.block,
                dimensions.len()
            ))
        })?;
        if !seen.insert(state.block) {
            return Err(SplitExactAuditError::Repair(format!(
                "rotated-kernel checkpoint repeats block {}",
                state.block
            )));
        }
        if state.kernel.len() != dimension {
            return Err(SplitExactAuditError::Repair(format!(
                "rotated-kernel block {} has {} rows, expected {dimension}",
                state.block,
                state.kernel.len()
            )));
        }
        let rank = state.kernel.first().map_or(0, Vec::len);
        if rank == 0 || state.kernel.iter().any(|row| row.len() != rank) {
            return Err(SplitExactAuditError::Repair(format!(
                "rotated-kernel block {} has an empty or inconsistent kernel",
                state.block
            )));
        }
    }
    states
        .par_iter()
        .map(|state| {
            let small_kernel = state
                .kernel
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|value| {
                            value
                                .parse::<Rational>()
                                .map(|value| crate::Qsqrt2::new(value, Rational::ZERO))
                                .map_err(|error| {
                                    SplitExactAuditError::Repair(format!(
                                        "rotated-kernel block {} contains an invalid rational entry: {error}",
                                        state.block
                                    ))
                                })
                        })
                        .collect::<Result<Vec<_>, SplitExactAuditError>>()
                })
                .collect::<Result<Vec<_>, SplitExactAuditError>>()?;
            let kernel = small_kernel
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|value| {
                            BigRational::new(
                                BigInt::from(value.rational.numerator),
                                BigInt::from(value.rational.denominator),
                            )
                        })
                        .collect()
                })
                .collect::<Vec<_>>();
            let projector = exact_kernel_projector(&kernel)?;
            Ok(ParsedRotatedKernelState {
                block: state.block,
                kernel,
                small_kernel,
                projector,
            })
        })
        .collect()
}

/// Build the sparsity-preserving native-bar face plan. Rotated blocks use the
/// exact orthogonal complement of their frozen kernels. Unselected blocks keep
/// the coordinate faces already proved by exact zero diagonals; full-rank
/// blocks need no extra native-bar constraint and are omitted.
pub fn build_split_native_bar_face_plan(
    certificate: &SplitExactDualCertificate,
    states: &[SplitRotatedKernelState],
) -> Result<SplitNativeBarFacePlan, SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let gram_refs = flattened_grams(certificate);
    let parsed_states = parse_split_rotated_kernels(states, &layout.dimensions)?;
    let mut state_by_block = vec![None; layout.dimensions.len()];
    for state in &parsed_states {
        state_by_block[state.block] = Some(state);
    }
    let mut blocks = Vec::new();
    for (block, (&dimension, matrix)) in layout.dimensions.iter().zip(&gram_refs).enumerate() {
        let (projector, rotated, kernel_rank) = if let Some(state) = state_by_block[block] {
            (
                state.projector.clone(),
                true,
                state.kernel.first().map_or(0, Vec::len),
            )
        } else {
            let zero_rows = (0..dimension)
                .map(|row| ScalarParser::parse(&matrix[row][row]).map(|value| value.is_zero()))
                .collect::<Result<Vec<_>, _>>()?;
            let kernel_rank = zero_rows.iter().filter(|&&zero| zero).count();
            if kernel_rank == 0 {
                continue;
            }
            let projector = (0..dimension)
                .map(|row| {
                    (0..dimension)
                        .map(|column| {
                            if row == column && !zero_rows[row] {
                                BigRational::one()
                            } else {
                                BigRational::zero()
                            }
                        })
                        .collect()
                })
                .collect();
            (projector, false, kernel_rank)
        };
        let range_projector =
            projector
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|value| {
                            value.to_f64().filter(|value| value.is_finite()).ok_or_else(|| {
                            SplitExactAuditError::Repair(format!(
                                "native-bar face projector for Gram block {block} is not finite"
                            ))
                        })
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
        blocks.push(SplitNativeBarFaceBlock {
            block,
            range_projector,
            rotated,
            kernel_rank,
        });
    }
    Ok(SplitNativeBarFacePlan {
        gram_count: layout.dimensions.len(),
        blocks,
    })
}

fn graph_kernel_face(
    state: &ParsedRotatedKernelState,
    matrix: &ParsedGram,
    dimension: usize,
) -> Result<ParsedFaceBlock, SplitExactAuditError> {
    let kernel_rank = state.kernel.first().map_or(0, Vec::len);
    let mut pivot_rows = vec![None; kernel_rank];
    let one = BigRational::one();
    for (kernel_column, pivot_row) in pivot_rows.iter_mut().enumerate() {
        for row in 0..dimension {
            if pivot_row.is_some() {
                break;
            }
            if state.kernel[row][kernel_column] != one
                || state.kernel[row]
                    .iter()
                    .enumerate()
                    .any(|(column, value)| column != kernel_column && !value.is_zero())
            {
                continue;
            }
            *pivot_row = Some(row);
        }
        if pivot_row.is_none() {
            return Err(SplitExactAuditError::Repair(format!(
                "rotated-kernel block {} column {kernel_column} has no exact graph pivot",
                state.block
            )));
        }
    }
    let pivot_rows = pivot_rows
        .into_iter()
        .map(Option::unwrap)
        .collect::<Vec<_>>();
    if pivot_rows.iter().copied().collect::<HashSet<_>>().len() != kernel_rank {
        return Err(SplitExactAuditError::Repair(format!(
            "rotated-kernel block {} reuses a graph pivot row",
            state.block
        )));
    }
    let pivot_set = pivot_rows.iter().copied().collect::<HashSet<_>>();
    let free_rows = (0..dimension)
        .filter(|row| !pivot_set.contains(row))
        .collect::<Vec<_>>();
    let rank = free_rows.len();
    let free_lookup = free_rows
        .iter()
        .enumerate()
        .map(|(column, &row)| (row, column))
        .collect::<HashMap<_, _>>();
    let pivot_lookup = pivot_rows
        .iter()
        .enumerate()
        .map(|(kernel_column, &row)| (row, kernel_column))
        .collect::<HashMap<_, _>>();
    let basis = (0..dimension)
        .map(|row| {
            (0..rank)
                .map(|column| {
                    let value = if free_lookup.get(&row) == Some(&column) {
                        BigRational::one()
                    } else if let Some(&kernel_column) = pivot_lookup.get(&row) {
                        -state.kernel[free_rows[column]][kernel_column].clone()
                    } else {
                        BigRational::zero()
                    };
                    BigQsqrt2::from_rational(value)
                })
                .collect()
        })
        .collect::<Vec<_>>();
    let coordinates = free_rows
        .iter()
        .map(|&row| {
            free_rows
                .iter()
                .map(|&column| parsed_gram_entry(matrix, row, column))
                .collect()
        })
        .collect();
    Ok(ParsedFaceBlock { basis, coordinates })
}

/// Project only the selected Grams onto their frozen exact graph-form range
/// faces. The free-row principal submatrix is retained as the face coordinate
/// matrix, so the resulting full rational Gram satisfies `G*N=0` exactly.
/// Affine identities can subsequently be closed using unselected Grams without
/// ever adding kernel rows to a correction signature.
pub fn project_split_grams_to_rotated_kernels(
    certificate: &mut SplitExactDualCertificate,
    states: &[SplitRotatedKernelState],
) -> Result<(), SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let parsed_states = parse_split_rotated_kernels(states, &layout.dimensions)?;
    let mut grams = certificate
        .occupation_grams_by_cell
        .iter_mut()
        .flatten()
        .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
        .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
        .collect::<Vec<_>>();
    for state in &parsed_states {
        let matrix = parse_matrix(
            state.block,
            grams[state.block],
            layout.dimensions[state.block],
        )?;
        let face = graph_kernel_face(state, &matrix, layout.dimensions[state.block])?;
        *grams[state.block] = reconstruct_face_gram(&face);
    }
    Ok(())
}

/// Validate frozen rotated-kernel checkpoint state and its exact rational
/// complementary projector. The certificate itself need not satisfy the
/// kernel equalities until the post-cone exact affine closure runs.
pub fn validate_split_rotated_gram_kernels(
    certificate: &SplitExactDualCertificate,
    states: &[SplitRotatedKernelState],
) -> Result<(), SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    parse_split_rotated_kernels(states, &layout.dimensions).map(|_| ())
}

/// Select only near-feasible Gram blocks with genuinely non-axis-aligned
/// sub-threshold modes. Exact dyadic kernel vectors are stored in sparse graph
/// form, with exact coordinate axes included for rows already reduced to zero.
/// This selection is advisory; no floating eigendirection is itself a proof.
pub fn select_split_rotated_gram_kernels(
    certificate: &SplitExactDualCertificate,
    threshold: f64,
    requested_margin: f64,
    basis_bits: u32,
) -> Result<(Vec<SplitRotatedKernelState>, SplitRotatedKernelBuildReport), SplitExactAuditError> {
    if !threshold.is_finite() || threshold <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "rotated facial threshold must be finite and positive".into(),
        ));
    }
    if !requested_margin.is_finite() || requested_margin <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "rotated facial selection margin must be finite and positive".into(),
        ));
    }
    if basis_bits > 60 {
        return Err(SplitExactAuditError::Repair(
            "rotated facial basis precision must be at most 60 bits".into(),
        ));
    }
    struct Selection {
        state: Option<SplitRotatedKernelState>,
        active: usize,
        eligible: usize,
        spectral: usize,
        non_axis: usize,
        coordinate: usize,
        minimum: f64,
        maximum: f64,
    }
    let layout = validate_layout(certificate)?;
    let gram_refs = flattened_grams(certificate);
    let parsed = parse_gram_refs(&gram_refs, &layout.dimensions)?;
    let minimum_eligible = -10.0 * requested_margin;
    let selections = parsed
        .par_iter()
        .zip(&layout.dimensions)
        .enumerate()
        .map(
            |(block, (matrix, &dimension))| -> Result<Selection, SplitExactAuditError> {
                if matrix.is_zero_matrix() {
                    return Ok(Selection {
                        state: None,
                        active: 0,
                        eligible: 0,
                        spectral: 0,
                        non_axis: 0,
                        coordinate: 0,
                        minimum: f64::INFINITY,
                        maximum: f64::NEG_INFINITY,
                    });
                }
                let live_rows = (0..dimension)
                    .filter(|&row| !matrix.entry_is_zero(row, row))
                    .collect::<Vec<_>>();
                if live_rows.is_empty() {
                    return Ok(Selection {
                        state: None,
                        active: 1,
                        eligible: 0,
                        spectral: 0,
                        non_axis: 0,
                        coordinate: 0,
                        minimum: f64::INFINITY,
                        maximum: f64::NEG_INFINITY,
                    });
                }
                let numeric = DMatrix::from_fn(live_rows.len(), live_rows.len(), |row, column| {
                    parsed_gram_entry(matrix, live_rows[row], live_rows[column])
                        .to_f64()
                        .unwrap_or(f64::NAN)
                });
                let numeric_scale = numeric.iter().copied().map(f64::abs).fold(1.0, f64::max);
                let eigen = numeric.symmetric_eigen();
                if eigen.eigenvalues.iter().any(|value| !value.is_finite()) {
                    return Err(SplitExactAuditError::Repair(format!(
                        "Gram block {block} has a non-finite reconstructed eigenvalue"
                    )));
                }
                let minimum = eigen.eigenvalues.min();
                let spectral = eigen
                    .eigenvalues
                    .iter()
                    .enumerate()
                    .filter_map(|(index, &value)| (value < threshold).then_some(index))
                    .collect::<Vec<_>>();
                let non_axis = spectral
                    .iter()
                    .filter(|&&index| {
                        eigen
                            .eigenvectors
                            .column(index)
                            .iter()
                            .map(|entry| entry * entry)
                            .fold(0.0, f64::max)
                            < AXIS_ALIGNMENT_SQUARED_THRESHOLD
                    })
                    .count();
                // Rotated kernels repair blocks that have actually left the
                // cone after exact reconstruction; they are not a global
                // reparameterization of every singular PSD block. Symmetric
                // eigensolvers can report a tiny negative value for an exact
                // zero eigenvalue, so require negativity beyond a
                // scale-aware roundoff allowance. The upper threshold still
                // controls which eigendirections enter an eligible block's
                // candidate kernel.
                let negative_roundoff_tolerance =
                    64.0 * f64::EPSILON * live_rows.len() as f64 * numeric_scale;
                let eligible = minimum > minimum_eligible
                    && minimum < -negative_roundoff_tolerance
                    && minimum < threshold;
                if !eligible || non_axis == 0 {
                    return Ok(Selection {
                        state: None,
                        active: 1,
                        eligible: usize::from(eligible),
                        spectral: 0,
                        non_axis: 0,
                        coordinate: 0,
                        minimum: f64::INFINITY,
                        maximum: f64::NEG_INFINITY,
                    });
                }

                let spectral_rank = spectral.len();
                let live_dimension = live_rows.len();
                let numeric_kernel =
                    DMatrix::from_fn(live_dimension, spectral_rank, |row, column| {
                        eigen.eigenvectors[(row, spectral[column])]
                    });
                let qr = numeric_kernel.transpose().col_piv_qr();
                let mut permutation =
                    DMatrix::from_row_iterator(1, live_dimension, 0..live_dimension);
                qr.p().permute_columns(&mut permutation);
                let pivot_rows = permutation
                    .row(0)
                    .iter()
                    .take(spectral_rank)
                    .copied()
                    .collect::<Vec<_>>();
                let pivot = DMatrix::from_fn(spectral_rank, spectral_rank, |row, column| {
                    numeric_kernel[(pivot_rows[row], column)]
                });
                let inverse = pivot.try_inverse().ok_or_else(|| {
                    SplitExactAuditError::Repair(format!(
                        "Gram block {block} near-null kernel has no floating pivot minor"
                    ))
                })?;
                let graph_kernel = numeric_kernel * inverse;
                if graph_kernel.iter().any(|value| !value.is_finite()) {
                    return Err(SplitExactAuditError::Repair(format!(
                        "Gram block {block} sparse kernel basis is not finite"
                    )));
                }
                let zero_rows = (0..dimension)
                    .filter(|&row| matrix.entry_is_zero(row, row))
                    .collect::<Vec<_>>();
                let coordinate_rank = zero_rows.len();
                let total_rank = coordinate_rank + spectral_rank;
                let pivot_lookup = pivot_rows
                    .iter()
                    .enumerate()
                    .map(|(column, &row)| (row, column))
                    .collect::<HashMap<_, _>>();
                let zero_lookup = zero_rows
                    .iter()
                    .enumerate()
                    .map(|(column, &row)| (row, column))
                    .collect::<HashMap<_, _>>();
                let mut exact_kernel = vec![vec!["0".into(); total_rank]; dimension];
                for (live_row, &matrix_row) in live_rows.iter().enumerate() {
                    if let Some(&pivot_column) = pivot_lookup.get(&live_row) {
                        exact_kernel[matrix_row][coordinate_rank + pivot_column] = "1".into();
                    } else {
                        for column in 0..spectral_rank {
                            exact_kernel[matrix_row][coordinate_rank + column] =
                                round_dyadic(graph_kernel[(live_row, column)], basis_bits)?
                                    .to_string();
                        }
                    }
                }
                for (&row, &column) in &zero_lookup {
                    exact_kernel[row][column] = "1".into();
                }
                let selected_minimum = spectral
                    .iter()
                    .map(|&index| eigen.eigenvalues[index])
                    .fold(f64::INFINITY, f64::min);
                let selected_maximum = spectral
                    .iter()
                    .map(|&index| eigen.eigenvalues[index])
                    .fold(f64::NEG_INFINITY, f64::max);
                Ok(Selection {
                    state: Some(SplitRotatedKernelState {
                        block,
                        kernel: exact_kernel,
                    }),
                    active: 1,
                    eligible: 1,
                    spectral: spectral_rank,
                    non_axis,
                    coordinate: coordinate_rank,
                    minimum: selected_minimum,
                    maximum: selected_maximum,
                })
            },
        )
        .collect::<Result<Vec<_>, SplitExactAuditError>>()?;
    let mut states = Vec::new();
    let mut active_gram_count = 0;
    let mut eligible_gram_count = 0;
    let mut spectral_kernel_direction_count = 0;
    let mut non_axis_aligned_kernel_direction_count = 0;
    let mut coordinate_kernel_direction_count = 0;
    let mut minimum_selected = f64::INFINITY;
    let mut maximum_selected = f64::NEG_INFINITY;
    for selection in selections {
        active_gram_count += selection.active;
        eligible_gram_count += selection.eligible;
        spectral_kernel_direction_count += selection.spectral;
        non_axis_aligned_kernel_direction_count += selection.non_axis;
        coordinate_kernel_direction_count += selection.coordinate;
        minimum_selected = minimum_selected.min(selection.minimum);
        maximum_selected = maximum_selected.max(selection.maximum);
        if let Some(state) = selection.state {
            states.push(state);
        }
    }
    if minimum_selected == f64::INFINITY {
        minimum_selected = 0.0;
    }
    if maximum_selected == f64::NEG_INFINITY {
        maximum_selected = 0.0;
    }
    let rotated_kernel_gram_count = states.len();
    Ok((
        states,
        SplitRotatedKernelBuildReport {
            eigenvalue_threshold: threshold,
            minimum_eligible_eigenvalue: minimum_eligible,
            eligibility: "minimum reconstructed eigenvalue is in (-10*margin, -64*eps*live_dimension*max(1,max_abs_entry)) and at least one sub-threshold eigenvector is non-axis-aligned",
            basis_dyadic_bits: basis_bits,
            active_gram_count,
            eligible_gram_count,
            rotated_kernel_gram_count,
            spectral_kernel_direction_count,
            non_axis_aligned_kernel_direction_count,
            coordinate_kernel_direction_count,
            minimum_selected_floating_eigenvalue: minimum_selected,
            maximum_selected_floating_eigenvalue: maximum_selected,
            representation: "native Gram variables with exact dyadic N, sparse G*N=0 equalities, and exact rational P=I-N*(N^T*N)^-1*N^T range-margin offset; only exact affine closure and exact PSD audits accept a certificate",
        },
    ))
}

/// Add newly exact-zero coordinate rows to each frozen kernel. If an axis is
/// already in the exact kernel span it is left implicit; otherwise appending
/// it preserves full column rank and keeps the range-margin projector zero on
/// that coordinate during the next resumed pass.
pub fn augment_split_rotated_kernels_with_zero_rows(
    certificate: &SplitExactDualCertificate,
    states: &mut [SplitRotatedKernelState],
) -> Result<(), SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let grams = flattened_grams(certificate);
    let parsed_grams = parse_gram_refs(&grams, &layout.dimensions)?;
    for state in &mut *states {
        let matrix = parsed_grams.get(state.block).ok_or_else(|| {
            SplitExactAuditError::Repair(format!(
                "rotated-kernel checkpoint block {} is outside {} Grams",
                state.block,
                parsed_grams.len()
            ))
        })?;
        let old_rank = state.kernel.first().map_or(0, Vec::len);
        for row in 0..layout.dimensions[state.block] {
            if !matrix.entry_is_zero(row, row) {
                continue;
            }
            let mut candidate = state.kernel.clone();
            for (index, values) in candidate.iter_mut().enumerate() {
                values.push(if index == row { "1" } else { "0" }.into());
            }
            let parsed = candidate
                .iter()
                .map(|values| {
                    values
                        .iter()
                        .map(|value| ScalarParser::parse(value))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            if face_basis_has_full_column_rank(&parsed)? {
                state.kernel = candidate;
            }
        }
        debug_assert!(state.kernel.first().map_or(0, Vec::len) >= old_rank);
    }
    parse_split_rotated_kernels(states, &layout.dimensions).map(|_| ())
}

fn exact_kernel_residuals(
    grams: &[ParsedGram],
    states: &[ParsedRotatedKernelState],
    dimensions: &[usize],
) -> Vec<BigQsqrt2> {
    let mut residuals = Vec::new();
    for state in states {
        let dimension = dimensions[state.block];
        let rank = state.kernel[0].len();
        for column in 0..rank {
            for row in 0..dimension {
                let mut residual = BigQsqrt2::zero();
                for inner in 0..dimension {
                    let term = parsed_gram_entry(&grams[state.block], row, inner).mul(
                        &BigQsqrt2::from_rational(state.kernel[inner][column].clone()),
                    );
                    add_assign(&mut residual, &term);
                }
                residuals.push(residual);
            }
        }
    }
    residuals
}

/// Require every frozen exact kernel to be an exact kernel of its certificate
/// Gram. This supplements, but never replaces, exact affine and PSD audits.
pub fn check_split_exact_kernel_closure(
    certificate: &SplitExactDualCertificate,
    states: &[SplitRotatedKernelState],
) -> Result<(), SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let grams = flattened_grams(certificate);
    let parsed_grams = parse_gram_refs(&grams, &layout.dimensions)?;
    let parsed_states = parse_split_rotated_kernels(states, &layout.dimensions)?;
    let nonzero = exact_kernel_residuals(&parsed_grams, &parsed_states, &layout.dimensions)
        .iter()
        .filter(|value| !value.is_zero())
        .count();
    if nonzero != 0 {
        return Err(SplitExactAuditError::Repair(format!(
            "rotated Gram kernels have {nonzero} nonzero exact residuals"
        )));
    }
    Ok(())
}

/// Project a rounded split dual onto both the exact coefficient identity and
/// the exact target hyperplane. Gram signatures are deduplicated before sparse
/// finite-field rank selection, and disconnected exact systems are solved
/// independently. Modular arithmetic remains advisory; the final identity,
/// bound, and PSD checks are exact over `Q(sqrt(2))`.
pub fn repair_split_exact_identity(
    certificate: &mut SplitExactDualCertificate,
) -> Result<(), SplitExactAuditError> {
    repair_split_exact_identity_inner(certificate, None).map(|_| ())
}

/// Run the componentwise exact repair and retain its conditioning and sparsity
/// diagnostics for campaign provenance.
pub fn repair_split_exact_identity_componentwise(
    certificate: &mut SplitExactDualCertificate,
) -> Result<SplitExactRepairDiagnostics, SplitExactAuditError> {
    repair_split_exact_identity_inner(certificate, None).map(|(diagnostics, _)| diagnostics)
}

/// Run the full componentwise exact repair and return both its diagnostics and
/// the Gram blocks selected for the exact affine correction. The support can
/// be reused to restrict a subsequent advisory cone repair without restricting
/// the exact closure itself.
pub fn repair_split_exact_identity_componentwise_with_support(
    certificate: &mut SplitExactDualCertificate,
) -> Result<(SplitExactRepairDiagnostics, Vec<usize>), SplitExactAuditError> {
    repair_split_exact_identity_inner(certificate, None)
}

/// Close the exact coefficient identity, target equation, and all frozen
/// rotated `G*N=0` equations jointly over `Q(sqrt(2))`. The sparse kernel rows
/// are acceptance constraints for this repair, while the unchanged exact Gram
/// audit remains the only PSD acceptance gate.
pub fn repair_split_exact_identity_with_kernels(
    certificate: &mut SplitExactDualCertificate,
    kernels: &[SplitRotatedKernelState],
) -> Result<SplitExactRepairDiagnostics, SplitExactAuditError> {
    let assembled = assemble_split_repair_with_kernels(certificate, None, kernels)?;
    finish_split_repair(certificate, assembled, None).map(|(diagnostics, _)| diagnostics)
}

/// Repair with the full nonzero Gram graph and return the Gram blocks whose
/// entries were selected for the exact affine correction.
pub fn repair_split_exact_identity_with_support(
    certificate: &mut SplitExactDualCertificate,
) -> Result<Vec<usize>, SplitExactAuditError> {
    repair_split_exact_identity_inner(certificate, None).map(|(_, support)| support)
}

/// Repair the exact identity while allowing Gram corrections only in the
/// supplied blocks. Equality and normalization multipliers remain available.
pub fn repair_split_exact_identity_restricted(
    certificate: &mut SplitExactDualCertificate,
    active_gram_blocks: &[usize],
) -> Result<SplitExactRepairDiagnostics, SplitExactAuditError> {
    let active = split_gram_selection_mask(certificate, active_gram_blocks)?;
    repair_split_exact_identity_inner(certificate, Some(&active))
        .map(|(diagnostics, _)| diagnostics)
}

fn split_gram_selection_mask(
    certificate: &SplitExactDualCertificate,
    active_gram_blocks: &[usize],
) -> Result<Vec<bool>, SplitExactAuditError> {
    let gram_count = flattened_grams(certificate).len();
    let mut active = vec![false; gram_count];
    for &block in active_gram_blocks {
        let selected = active.get_mut(block).ok_or_else(|| {
            SplitExactAuditError::Repair(format!(
                "restricted repair Gram block {block} is outside {gram_count} blocks"
            ))
        })?;
        if *selected {
            return Err(SplitExactAuditError::Repair(format!(
                "restricted repair Gram block {block} is repeated"
            )));
        }
        *selected = true;
    }
    if !active.iter().any(|&selected| selected) {
        return Err(SplitExactAuditError::Repair(
            "restricted repair requires at least one active Gram block".into(),
        ));
    }
    Ok(active)
}

/// Repair with a caller-supplied preference order over the assembled
/// repair-variable pool (for example an LP-guided low-damage support computed
/// from [`export_split_repair_system`]). Preferred variables are offered to
/// the advisory modular basis selection first, so a spanning LP support stays
/// the selected basis; unlisted variables remain available as a fallback.
/// The solve and all acceptance checks remain exact over Q(sqrt(2)).
pub fn repair_split_exact_identity_ordered(
    certificate: &mut SplitExactDualCertificate,
    preference: &[usize],
) -> Result<(SplitExactRepairDiagnostics, Vec<usize>), SplitExactAuditError> {
    if preference.is_empty() {
        return Err(SplitExactAuditError::Repair(
            "an ordered exact repair requires a nonempty preference".into(),
        ));
    }
    let assembled = assemble_split_repair(certificate, None)?;
    finish_split_repair(certificate, assembled, Some(preference))
}

pub const SPLIT_REPAIR_SYSTEM_SCHEMA_V1: &str = "minexposure/split-repair-system-v1";

/// Compact provenance summary of an exported split repair system.
#[derive(Clone, Debug, Serialize)]
pub struct SplitRepairSystemSummary {
    pub rows: usize,
    pub variable_count: usize,
    pub gram_variable_count: usize,
    pub affine_variable_count: usize,
    pub nonzero_residual_count: usize,
    pub unique_gram_signature_count: usize,
}

/// Export the assembled exact repair system (identity + bound residual, the
/// deduplicated sparse repair columns, and per-block reconstructed spectral
/// margins) as JSON, so an external LP can select a low-damage repair support
/// for [`repair_split_exact_identity_ordered`]. Variable indices in the
/// export are exactly the pool positions the preference order refers to.
pub fn export_split_repair_system(
    certificate: &SplitExactDualCertificate,
    output: &std::path::Path,
) -> Result<SplitRepairSystemSummary, SplitExactAuditError> {
    let assembled = assemble_split_repair(certificate, None)?;
    let gram_variable_count = assembled
        .columns
        .iter()
        .filter(|column| matches!(column.variable, RepairVariable::Gram { .. }))
        .count();
    let variables = assembled
        .columns
        .iter()
        .map(|column| match column.variable {
            RepairVariable::Equality(index) => serde_json::json!({
                "kind": "equality",
                "index": index,
            }),
            RepairVariable::Normalization => serde_json::json!({
                "kind": "normalization",
            }),
            RepairVariable::Gram { block, row, column } => serde_json::json!({
                "kind": "gram",
                "block": block,
                "row": row,
                "column": column,
                "block_dimension": assembled.layout.dimensions[block],
                "block_margin": finite_or_null(assembled.block_margins[block]),
            }),
        })
        .collect::<Vec<_>>();
    let columns = assembled
        .columns
        .iter()
        .map(|column| {
            column
                .coefficients
                .iter()
                .map(|(&row, value)| (row, value.to_f64()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // Active Gram values as floats (upper triangle), so an external SDP/SOCP
    // support search can impose the true cone constraint G + X ⪰ 0 rather than
    // a scalar margin proxy. Advisory only; the exact audit still decides.
    let gram_values_f64 = assembled
        .parsed_grams
        .iter()
        .zip(&assembled.layout.dimensions)
        .zip(&assembled.block_margins)
        .map(
            |((matrix, &dimension), &margin)| -> Result<serde_json::Value, ExactAuditError> {
                if !margin.is_finite() {
                    return Ok(serde_json::Value::Null);
                }
                let mut entries = Vec::new();
                for row in 0..dimension {
                    for column in row..dimension {
                        let value =
                            parsed_gram_entry(matrix, row, column)
                                .to_f64()
                                .ok_or_else(|| {
                                    ExactAuditError::InvalidScalar(
                                        "exact Gram entry cannot be represented as f64".into(),
                                    )
                                })?;
                        entries.push((row, column, value));
                    }
                }
                Ok(serde_json::json!({
                    "dimension": dimension,
                    "entries": entries,
                }))
            },
        )
        .collect::<Result<Vec<_>, ExactAuditError>>()?;
    let payload = serde_json::json!({
        "schema": SPLIT_REPAIR_SYSTEM_SCHEMA_V1,
        "rows": assembled.rows,
        "residual_exact": assembled
            .residual
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "residual_f64": assembled
            .residual
            .iter()
            .map(|value| value.to_f64())
            .collect::<Vec<_>>(),
        "block_dimensions": assembled.layout.dimensions,
        "block_margins": assembled
            .block_margins
            .iter()
            .map(|&margin| finite_or_null(margin))
            .collect::<Vec<_>>(),
        "variables": variables,
        "gram_values_f64": gram_values_f64,
        "columns": columns,
    });
    let file = std::fs::File::create(output).map_err(|error| {
        SplitExactAuditError::Model(format!(
            "could not create repair-system export {}: {error}",
            output.display()
        ))
    })?;
    serde_json::to_writer(std::io::BufWriter::new(file), &payload).map_err(|error| {
        SplitExactAuditError::Model(format!(
            "could not write repair-system export {}: {error}",
            output.display()
        ))
    })?;
    Ok(SplitRepairSystemSummary {
        rows: assembled.rows,
        variable_count: assembled.columns.len(),
        gram_variable_count,
        affine_variable_count: assembled.available_affine_variable_count,
        nonzero_residual_count: assembled
            .residual
            .iter()
            .filter(|value| !value.is_zero())
            .count(),
        unique_gram_signature_count: assembled.unique_gram_signature_count,
    })
}

fn finite_or_null(value: f64) -> Option<f64> {
    value.is_finite().then_some(value)
}

/// Rebuild every Gram as `F K F^T` and close the exact coefficient identity by
/// changing only the inner symmetric coordinates `K`. A numerical minimum-norm
/// correction is rounded first; the remaining residual is then eliminated and
/// checked exactly over `Q(sqrt(2))`. The modular pass selects an exact column
/// basis only and cannot make the final identity or PSD checks pass.
pub fn repair_split_exact_identity_on_faces(
    certificate: &mut SplitExactDualCertificate,
    faces: &[SplitFaceBlock],
    correction_dyadic_bits: u32,
    zero_correction: bool,
    known_span: Option<usize>,
) -> Result<SplitFaceRepairReport, SplitExactAuditError> {
    repair_split_exact_identity_on_faces_inner(
        certificate,
        faces,
        correction_dyadic_bits,
        zero_correction,
        known_span,
        false,
        None,
    )
}

/// Close every exact coefficient identity and preserve the exact target while
/// changing only the inner `H` coordinates of frozen rotated Gram faces.
pub fn repair_split_exact_identity_on_rotated_faces(
    certificate: &mut SplitExactDualCertificate,
    faces: &mut [SplitFaceBlock],
    correction_dyadic_bits: u32,
) -> Result<SplitFaceRepairReport, SplitExactAuditError> {
    let input_faces = faces.to_vec();
    repair_split_exact_identity_on_faces_inner(
        certificate,
        &input_faces,
        correction_dyadic_bits,
        false,
        None,
        true,
        Some(faces),
    )
}

fn repair_split_exact_identity_on_faces_inner(
    certificate: &mut SplitExactDualCertificate,
    faces: &[SplitFaceBlock],
    correction_dyadic_bits: u32,
    zero_correction: bool,
    known_span: Option<usize>,
    preserve_exact_target: bool,
    updated_faces: Option<&mut [SplitFaceBlock]>,
) -> Result<SplitFaceRepairReport, SplitExactAuditError> {
    if correction_dyadic_bits > 60 {
        return Err(SplitExactAuditError::Repair(
            "face correction dyadic precision must be at most 60 bits".into(),
        ));
    }
    let layout = validate_layout(certificate)?;
    let mut multipliers = flattened_multipliers(certificate)?;
    let mut normalization = ScalarParser::parse(&certificate.normalization)?;
    let mut faces = parse_face_blocks(faces, &layout.dimensions)?;
    let face_ranks = faces
        .iter()
        .map(|face| face.coordinates.len())
        .collect::<Vec<_>>();
    let full_face_block_count = face_ranks
        .iter()
        .zip(&layout.dimensions)
        .filter(|(rank, dimension)| rank == dimension)
        .count();
    let zero_face_block_count = face_ranks.iter().filter(|&&rank| rank == 0).count();
    let mut gram_values = faces.iter().map(reconstruct_face_gram).collect::<Vec<_>>();
    write_back(
        certificate,
        &layout.model,
        &multipliers,
        &normalization,
        gram_values.clone(),
    );
    let gram_refs = gram_values.iter().collect::<Vec<_>>();
    let mut identity = reconstructed_identity(
        &layout.model,
        &multipliers,
        &normalization,
        &gram_refs,
        &layout.dimensions,
    )?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    if preserve_exact_target {
        identity
            .push(reconstructed_bound(&layout.model, &multipliers, &normalization).sub(&target));
    }
    let nonzero_before = identity.iter().filter(|value| !value.is_zero()).count();
    let rows = identity.len();
    if known_span.is_some_and(|span| span == 0 || span > rows) {
        return Err(SplitExactAuditError::Repair(format!(
            "known face span must be between 1 and {rows}"
        )));
    }

    let mut variables = Vec::new();
    let mut columns = Vec::<BTreeMap<usize, BigQsqrt2>>::new();
    for (index, equality) in layout.model.rows.iter().enumerate() {
        let mut coefficients = BTreeMap::new();
        for &(position, value) in &equality.coefficients {
            add_assign(
                coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
                &BigQsqrt2::from_small(value),
            );
        }
        if preserve_exact_target {
            coefficients.insert(
                rows - 1,
                BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(-equality.rhs))),
            );
        }
        variables.push(FaceRepairVariable::Equality(index));
        columns.push(coefficients);
    }
    let mut normalization_column = BTreeMap::new();
    layout.model.for_each_normalization_position(|position| {
        normalization_column.insert(position, BigQsqrt2::from_rational(BigRational::one()));
    });
    if preserve_exact_target {
        normalization_column.insert(
            rows - 1,
            BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(-1))),
        );
    }
    variables.push(FaceRepairVariable::Normalization);
    columns.push(normalization_column);

    let mut face_order = (0..faces.len())
        .filter(|&block| !faces[block].coordinates.is_empty())
        .collect::<Vec<_>>();
    face_order.sort_by(|&left, &right| {
        let left_full = face_ranks[left] == layout.dimensions[left];
        let right_full = face_ranks[right] == layout.dimensions[right];
        right_full
            .cmp(&left_full)
            .then_with(|| face_ranks[right].cmp(&face_ranks[left]))
            .then_with(|| left.cmp(&right))
    });
    let scalar_variable_count = columns.len();
    for block in face_order {
        let rank = face_ranks[block];
        let diagonal_basis = diagonal_face_basis(&faces[block].basis);
        for distance in 0..rank {
            for row in 0..rank - distance {
                let column = row + distance;
                columns.push(if let Some(diagonal) = &diagonal_basis {
                    gram_entry_column(
                        &layout.model,
                        block,
                        row,
                        column,
                        &diagonal[row].mul(&diagonal[column]),
                    )
                } else {
                    face_coordinate_column(&layout.model, block, &faces[block].basis, row, column)
                });
                variables.push(FaceRepairVariable::Coordinate { block, row, column });
            }
        }
    }
    let face_variable_count = columns.len() - scalar_variable_count;
    let stop_rank = known_span.unwrap_or(rows);
    let selected = if face_ranks
        .iter()
        .zip(&layout.dimensions)
        .all(|(rank, dimension)| *rank == 0 || rank == dimension)
    {
        select_face_modular_column_basis_until(rows, &columns, stop_rank)?
    } else {
        select_sparse_modular_column_basis(rows, &columns, stop_rank)?
    };
    let identity_span = selected.len();
    let identity_span_scan_complete = stop_rank == rows || identity_span < stop_rank;
    let mut numerical_iterations = 0;
    let mut numerical_relative_residual = 1.0;
    let mut numerical_correction_maximum = 0.0_f64;
    let mut corrected_identity = identity.clone();
    let mut selected_exact_correction_blocks = std::collections::BTreeSet::new();
    let mut minimum_coordinate_eigenvalue_before_exact_tail =
        minimum_face_coordinate_eigenvalue(&faces);

    if !zero_correction {
        let independent_rows = selected.iter().map(|&(row, _)| row).collect::<Vec<_>>();
        let numerical = numerical_minimum_norm_correction(&identity, &columns, &independent_rows)?;
        numerical_iterations = numerical.iterations;
        numerical_relative_residual = numerical.relative_residual;
        for (candidate, value) in numerical.values.into_iter().enumerate() {
            numerical_correction_maximum = numerical_correction_maximum.max(value.abs());
            let correction = round_dyadic(value, correction_dyadic_bits)?;
            if correction.is_zero() {
                continue;
            }
            apply_face_correction(
                variables[candidate],
                &correction,
                &mut multipliers,
                &mut normalization,
                &mut faces,
            );
            for (&position, coefficient) in &columns[candidate] {
                add_assign(
                    &mut corrected_identity[position],
                    &coefficient.mul(&correction),
                );
            }
        }
        minimum_coordinate_eigenvalue_before_exact_tail =
            minimum_face_coordinate_eigenvalue(&faces);

        let rank = selected.len();
        let mut system = selected
            .iter()
            .map(|&(row, _)| {
                let mut values = selected
                    .iter()
                    .map(|&(_, candidate)| {
                        columns[candidate]
                            .get(&row)
                            .cloned()
                            .unwrap_or_else(BigQsqrt2::zero)
                    })
                    .collect::<Vec<_>>();
                values.push(corrected_identity[row].neg());
                values
            })
            .collect::<Vec<_>>();
        exact_gaussian_elimination(&mut system)?;
        for (column, &(_, candidate)) in selected.iter().enumerate() {
            let correction = &system[column][rank];
            if correction.is_zero() {
                continue;
            }
            if let FaceRepairVariable::Coordinate { block, .. } = variables[candidate] {
                selected_exact_correction_blocks.insert(block);
            }
            apply_face_correction(
                variables[candidate],
                correction,
                &mut multipliers,
                &mut normalization,
                &mut faces,
            );
        }
    }

    gram_values = faces.iter().map(reconstruct_face_gram).collect::<Vec<_>>();
    write_back(
        certificate,
        &layout.model,
        &multipliers,
        &normalization,
        gram_values,
    );
    let gram_refs = flattened_grams(certificate);
    let mut repaired_identity = reconstructed_identity(
        &layout.model,
        &multipliers,
        &normalization,
        &gram_refs,
        &layout.dimensions,
    )?;
    if preserve_exact_target {
        repaired_identity
            .push(reconstructed_bound(&layout.model, &multipliers, &normalization).sub(&target));
    }
    let nonzero_after = repaired_identity
        .iter()
        .filter(|value| !value.is_zero())
        .count();
    let (coordinate_psd, coordinate_psd_failure, minimum_coordinate_eigenvalue) =
        coordinate_psd_diagnostics(&faces);
    let selected_exact_correction_blocks = selected_exact_correction_blocks
        .into_iter()
        .collect::<Vec<_>>();
    if let Some(updated_faces) = updated_faces {
        for (face, parsed) in updated_faces.iter_mut().zip(&faces) {
            face.coordinates = parsed
                .coordinates
                .iter()
                .map(|row| row.iter().map(ToString::to_string).collect())
                .collect();
        }
    }
    Ok(SplitFaceRepairReport {
        coefficient_count: rows,
        identity_span,
        identity_span_scan_complete,
        affine_variable_count: columns.len(),
        face_variable_count,
        face_ranks,
        full_face_block_count,
        zero_face_block_count,
        nonzero_exact_residual_count_before_repair: nonzero_before,
        nonzero_exact_residual_count_after_repair: nonzero_after,
        exact_identity_closed: nonzero_after == 0,
        coordinate_matrices_exactly_positive_semidefinite: coordinate_psd,
        coordinate_psd_failure,
        minimum_reconstructed_coordinate_eigenvalue: minimum_coordinate_eigenvalue,
        numerical_minimum_norm_iterations: numerical_iterations,
        numerical_minimum_norm_relative_residual: numerical_relative_residual,
        numerical_correction_maximum_absolute_value: numerical_correction_maximum,
        minimum_coordinate_eigenvalue_before_exact_tail,
        selected_exact_correction_block_count: selected_exact_correction_blocks.len(),
        selected_exact_correction_blocks,
    })
}

fn parse_face_blocks(
    faces: &[SplitFaceBlock],
    dimensions: &[usize],
) -> Result<Vec<ParsedFaceBlock>, SplitExactAuditError> {
    if faces.len() != dimensions.len() {
        return Err(SplitExactAuditError::Repair(format!(
            "face block count mismatch: expected {}, found {}",
            dimensions.len(),
            faces.len()
        )));
    }
    faces
        .iter()
        .zip(dimensions)
        .enumerate()
        .map(|(block, (face, &dimension))| {
            if face.basis.len() != dimension {
                return Err(SplitExactAuditError::Repair(format!(
                    "face block {block} basis row count mismatch: expected {dimension}, found {}",
                    face.basis.len()
                )));
            }
            let rank = face.coordinates.len();
            if face.basis.iter().any(|row| row.len() != rank)
                || face.coordinates.iter().any(|row| row.len() != rank)
            {
                return Err(SplitExactAuditError::Repair(format!(
                    "face block {block} has inconsistent basis or coordinate shape"
                )));
            }
            let coordinate_selector = face_is_coordinate_selector(face);
            let basis = face
                .basis
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|value| ScalarParser::parse(value))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            let coordinates = face
                .coordinates
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|value| ScalarParser::parse(value))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            for (row, values) in coordinates.iter().enumerate() {
                for (column, value) in values.iter().take(row).enumerate() {
                    if value != &coordinates[column][row] {
                        return Err(SplitExactAuditError::Repair(format!(
                            "face block {block} coordinates are not exactly symmetric at ({row}, {column})"
                        )));
                    }
                }
            }
            if !coordinate_selector && !face_basis_has_full_column_rank(&basis)? {
                return Err(SplitExactAuditError::Repair(format!(
                    "face block {block} basis does not have exact full column rank {rank}"
                )));
            }
            Ok(ParsedFaceBlock { basis, coordinates })
        })
        .collect()
}

fn face_basis_has_full_column_rank(basis: &[Vec<BigQsqrt2>]) -> Result<bool, SplitExactAuditError> {
    const PRIME: u64 = 2_147_483_629;
    let columns = basis.first().map_or(0, Vec::len);
    if columns == 0 {
        return Ok(true);
    }
    let modular = basis
        .iter()
        .map(|row| {
            row.iter()
                .map(|value| quadratic_mod(value, PRIME))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>();
    if let Ok(mut modular) = modular {
        let mut pivot_row = 0;
        for column in 0..columns {
            let Some(found) =
                (pivot_row..modular.len()).find(|&row| modular[row][column] != ModQsqrt2::ZERO)
            else {
                break;
            };
            modular.swap(pivot_row, found);
            let inverse = modular[pivot_row][column].inverse(PRIME)?;
            for value in &mut modular[pivot_row][column..] {
                *value = value.mul(inverse, PRIME);
            }
            let pivot_values = modular[pivot_row][column..].to_vec();
            for values in modular.iter_mut().skip(pivot_row + 1) {
                let factor = values[column];
                if factor == ModQsqrt2::ZERO {
                    continue;
                }
                for (value, &pivot) in values[column..].iter_mut().zip(&pivot_values) {
                    *value = value.sub(factor.mul(pivot, PRIME), PRIME);
                }
            }
            pivot_row += 1;
            if pivot_row == columns {
                return Ok(true);
            }
        }
    }
    // A full-rank modular image proves exact full rank. A deficient image can
    // be an unlucky specialization, so retain the slower exact fallback for
    // user-supplied face bases and malformed-input diagnostics.
    Ok(exact_face_basis_column_rank(basis)? == columns)
}

fn exact_face_basis_column_rank(basis: &[Vec<BigQsqrt2>]) -> Result<usize, SplitExactAuditError> {
    let columns = basis.first().map_or(0, Vec::len);
    if columns == 0 {
        return Ok(0);
    }
    let mut matrix = basis.to_vec();
    let mut pivot_row = 0;
    for column in 0..columns {
        let Some(found) = (pivot_row..matrix.len()).find(|&row| !matrix[row][column].is_zero())
        else {
            continue;
        };
        matrix.swap(pivot_row, found);
        let pivot = matrix[pivot_row][column].clone();
        let pivot_values = matrix[pivot_row][column..].to_vec();
        for values in matrix.iter_mut().skip(pivot_row + 1) {
            if values[column].is_zero() {
                continue;
            }
            let factor = values[column].div(&pivot)?;
            values[column] = BigQsqrt2::zero();
            for (value, pivot_value) in values[column + 1..].iter_mut().zip(&pivot_values[1..]) {
                *value = value.sub(&factor.mul(pivot_value));
            }
        }
        pivot_row += 1;
        if pivot_row == columns {
            break;
        }
    }
    Ok(pivot_row)
}

fn diagonal_face_basis(basis: &[Vec<BigQsqrt2>]) -> Option<Vec<BigQsqrt2>> {
    let rank = basis.first().map_or(0, Vec::len);
    if basis.len() != rank {
        return None;
    }
    let mut diagonal = Vec::with_capacity(rank);
    for (row, values) in basis.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            if row == column {
                if value.is_zero() {
                    return None;
                }
                diagonal.push(value.clone());
            } else if !value.is_zero() {
                return None;
            }
        }
    }
    Some(diagonal)
}

fn diagonal_coordinates(coordinates: &[Vec<BigQsqrt2>]) -> Option<Vec<BigQsqrt2>> {
    let mut diagonal = Vec::with_capacity(coordinates.len());
    for (row, values) in coordinates.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            if row == column {
                diagonal.push(value.clone());
            } else if !value.is_zero() {
                return None;
            }
        }
    }
    Some(diagonal)
}

fn reconstruct_face_gram(face: &ParsedFaceBlock) -> EncodedMatrix {
    let dimension = face.basis.len();
    let rank = face.coordinates.len();
    if let Some(diagonal) = diagonal_face_basis(&face.basis) {
        return (0..dimension)
            .map(|row| {
                (0..dimension)
                    .map(|column| {
                        diagonal[row]
                            .mul(&face.coordinates[row][column])
                            .mul(&diagonal[column])
                            .to_string()
                    })
                    .collect()
            })
            .collect();
    }
    if let Some(diagonal) = diagonal_coordinates(&face.coordinates) {
        return (0..dimension)
            .map(|row| {
                (0..dimension)
                    .map(|column| {
                        let mut value = BigQsqrt2::zero();
                        for (face_column, coordinate) in diagonal.iter().enumerate() {
                            let term = face.basis[row][face_column]
                                .mul(coordinate)
                                .mul(&face.basis[column][face_column]);
                            add_assign(&mut value, &term);
                        }
                        value.to_string()
                    })
                    .collect()
            })
            .collect();
    }
    let supports = (0..rank)
        .map(|face_column| {
            face.basis
                .iter()
                .enumerate()
                .filter_map(|(row, values)| {
                    (!values[face_column].is_zero()).then_some((row, &values[face_column]))
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut reconstructed = vec![vec![BigQsqrt2::zero(); dimension]; dimension];
    for left in 0..rank {
        for right in 0..rank {
            let coordinate = &face.coordinates[left][right];
            if coordinate.is_zero() {
                continue;
            }
            for &(row, left_value) in &supports[left] {
                for &(column, right_value) in &supports[right] {
                    let term = left_value.mul(coordinate).mul(right_value);
                    add_assign(&mut reconstructed[row][column], &term);
                }
            }
        }
    }
    reconstructed
        .into_iter()
        .map(|row| row.into_iter().map(|value| value.to_string()).collect())
        .collect()
}

fn face_coordinate_column(
    model: &ExactSplitModel,
    block: usize,
    basis: &[Vec<BigQsqrt2>],
    face_row: usize,
    face_column: usize,
) -> BTreeMap<usize, BigQsqrt2> {
    let left_support = basis
        .iter()
        .enumerate()
        .filter_map(|(row, values)| (!values[face_row].is_zero()).then_some(row))
        .collect::<Vec<_>>();
    let right_support = basis
        .iter()
        .enumerate()
        .filter_map(|(row, values)| (!values[face_column].is_zero()).then_some(row))
        .collect::<Vec<_>>();
    let mut gram_effects = BTreeMap::<(usize, usize), BigQsqrt2>::new();
    let mut accumulate_effect =
        |left: &[usize], right: &[usize], left_column: usize, right_column: usize| {
            for &row in left {
                for &column in right {
                    if row > column {
                        continue;
                    }
                    let effect = basis[row][left_column].mul(&basis[column][right_column]);
                    add_assign(
                        gram_effects
                            .entry((row, column))
                            .or_insert_with(BigQsqrt2::zero),
                        &effect,
                    );
                }
            }
        };
    accumulate_effect(&left_support, &right_support, face_row, face_column);
    if face_row != face_column {
        accumulate_effect(&right_support, &left_support, face_column, face_row);
    }
    let mut coefficients = BTreeMap::new();
    for ((row, column), effect) in gram_effects {
        if effect.is_zero() {
            continue;
        }
        for (position, value) in gram_entry_column(model, block, row, column, &effect) {
            add_assign(
                coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
                &value,
            );
        }
    }
    coefficients
}

fn gram_entry_column(
    model: &ExactSplitModel,
    block: usize,
    row: usize,
    column: usize,
    scale: &BigQsqrt2,
) -> BTreeMap<usize, BigQsqrt2> {
    let mut coefficients = BTreeMap::new();
    model.for_each_gram_entry_coefficient(block, row, column, |position, value| {
        let value = BigQsqrt2::from_small(value).neg().mul(scale);
        add_assign(
            coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
            &value,
        );
    });
    if row != column {
        model.for_each_gram_entry_coefficient(block, column, row, |position, value| {
            let value = BigQsqrt2::from_small(value).neg().mul(scale);
            add_assign(
                coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
                &value,
            );
        });
    }
    coefficients
}

struct NumericalCorrection {
    values: Vec<f64>,
    iterations: usize,
    relative_residual: f64,
}

fn numerical_minimum_norm_correction(
    identity: &[BigQsqrt2],
    columns: &[BTreeMap<usize, BigQsqrt2>],
    independent_rows: &[usize],
) -> Result<NumericalCorrection, SplitExactAuditError> {
    let rows = independent_rows.len();
    let mut compressed_rows = vec![None; identity.len()];
    for (row, &identity_row) in independent_rows.iter().enumerate() {
        compressed_rows[identity_row] = Some(row);
    }
    let mut numeric_columns = columns
        .iter()
        .map(|column| {
            column
                .iter()
                .filter_map(|(&identity_row, value)| {
                    compressed_rows[identity_row].map(|row| {
                        value.to_f64().map(|value| (row, value)).ok_or_else(|| {
                            SplitExactAuditError::Repair(
                                "a face correction coefficient cannot be represented as f64".into(),
                            )
                        })
                    })
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut rhs = independent_rows
        .iter()
        .map(|&row| {
            let value = &identity[row];
            value.to_f64().map(|value| -value).ok_or_else(|| {
                SplitExactAuditError::Repair(
                    "a face correction residual cannot be represented as f64".into(),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut numeric_rows = vec![Vec::new(); rows];
    for (column_index, column) in numeric_columns.iter().enumerate() {
        for &(row, value) in column {
            numeric_rows[row].push((column_index, value));
        }
    }
    let row_norms = numeric_rows
        .par_iter()
        .map(|row| {
            row.iter()
                .map(|(_, value)| value * value)
                .sum::<f64>()
                .sqrt()
        })
        .collect::<Vec<_>>();
    if row_norms
        .iter()
        .any(|norm| !norm.is_finite() || *norm == 0.0)
    {
        return Err(SplitExactAuditError::Repair(
            "face correction LSQR has a zero or non-finite row norm".into(),
        ));
    }
    numeric_columns.par_iter_mut().for_each(|column| {
        for (row, value) in column {
            *value /= row_norms[*row];
        }
    });
    numeric_rows
        .par_iter_mut()
        .zip(row_norms.par_iter())
        .for_each(|(row, norm)| {
            for (_, value) in row {
                *value /= norm;
            }
        });
    rhs.par_iter_mut()
        .zip(row_norms.par_iter())
        .for_each(|(value, norm)| *value /= norm);
    let rhs_norm = rhs.iter().map(|value| value * value).sum::<f64>().sqrt();
    if rhs_norm == 0.0 {
        return Ok(NumericalCorrection {
            values: vec![0.0; columns.len()],
            iterations: 0,
            relative_residual: 0.0,
        });
    }
    let product = |input: &[f64]| {
        numeric_rows
            .par_iter()
            .map(|row| {
                row.iter()
                    .map(|&(column, value)| value * input[column])
                    .sum::<f64>()
            })
            .collect::<Vec<_>>()
    };
    let transpose_product = |input: &[f64]| {
        numeric_columns
            .par_iter()
            .map(|column| {
                column
                    .iter()
                    .map(|&(row, value)| value * input[row])
                    .sum::<f64>()
            })
            .collect::<Vec<_>>()
    };
    let norm = |values: &[f64]| {
        values
            .par_iter()
            .map(|value| value * value)
            .sum::<f64>()
            .sqrt()
    };
    let true_residual = |solution: &[f64]| {
        product(solution)
            .iter()
            .zip(&rhs)
            .map(|(actual, expected)| (actual - expected).powi(2))
            .sum::<f64>()
            .sqrt()
    };

    let mut left = rhs.iter().map(|value| value / rhs_norm).collect::<Vec<_>>();
    let mut right = transpose_product(&left);
    let mut alpha = norm(&right);
    if !alpha.is_finite() || alpha == 0.0 {
        return Err(SplitExactAuditError::Repair(
            "face correction LSQR has a zero or non-finite initial direction".into(),
        ));
    }
    right.par_iter_mut().for_each(|value| {
        *value /= alpha;
    });
    let mut direction = right.clone();
    let mut solution = vec![0.0; columns.len()];
    let mut best_solution = solution.clone();
    let mut conjugate_residual = alpha;
    let mut projected_residual = rhs_norm;
    let mut iterations = 0;
    let mut best_iterations = 0;
    let mut best_residual_norm = rhs_norm;
    let tolerance = rhs_norm * 1e-12;
    let maximum_iterations = rows.saturating_mul(8).clamp(100, 20_000);
    while iterations < maximum_iterations {
        let mut next_left = product(&right);
        for (value, previous) in next_left.iter_mut().zip(&left) {
            *value -= alpha * previous;
        }
        let beta = norm(&next_left);
        if !beta.is_finite() {
            return Err(SplitExactAuditError::Repair(
                "face correction LSQR produced a non-finite left direction".into(),
            ));
        }
        if beta != 0.0 {
            for value in &mut next_left {
                *value /= beta;
            }
        }
        left = next_left;

        let mut next_right = transpose_product(&left);
        next_right
            .par_iter_mut()
            .zip(right.par_iter())
            .for_each(|(value, previous)| *value -= beta * previous);
        alpha = norm(&next_right);
        if !alpha.is_finite() {
            return Err(SplitExactAuditError::Repair(
                "face correction LSQR produced a non-finite right direction".into(),
            ));
        }
        if alpha != 0.0 {
            next_right.par_iter_mut().for_each(|value| {
                *value /= alpha;
            });
        }
        right = next_right;

        let rotation = conjugate_residual.hypot(beta);
        if !rotation.is_finite() || rotation == 0.0 {
            return Err(SplitExactAuditError::Repair(
                "face correction LSQR produced a zero or non-finite rotation".into(),
            ));
        }
        let cosine = conjugate_residual / rotation;
        let sine = beta / rotation;
        let next_weight = sine * alpha;
        conjugate_residual = -cosine * alpha;
        let step = cosine * projected_residual;
        projected_residual *= sine;
        let solution_scale = step / rotation;
        let direction_scale = next_weight / rotation;
        solution
            .par_iter_mut()
            .zip(direction.par_iter_mut())
            .zip(right.par_iter())
            .for_each(|((solution, direction), &right)| {
                *solution += solution_scale * *direction;
                *direction = right - direction_scale * *direction;
            });
        iterations += 1;

        if iterations % 25 == 0 || projected_residual.abs() <= tolerance {
            let residual_norm = true_residual(&solution);
            if !residual_norm.is_finite() {
                return Err(SplitExactAuditError::Repair(
                    "face correction LSQR produced a non-finite residual".into(),
                ));
            }
            if residual_norm < best_residual_norm {
                best_residual_norm = residual_norm;
                best_solution.clone_from(&solution);
                best_iterations = iterations;
            }
            if residual_norm <= tolerance {
                break;
            }
        }
        if alpha == 0.0 && beta == 0.0 {
            break;
        }
    }
    let final_residual = true_residual(&solution);
    if final_residual < best_residual_norm {
        best_residual_norm = final_residual;
        best_solution = solution;
        best_iterations = iterations;
    }
    let relative_residual = best_residual_norm / rhs_norm;
    Ok(NumericalCorrection {
        values: best_solution,
        iterations: best_iterations,
        relative_residual,
    })
}

fn round_dyadic(value: f64, bits: u32) -> Result<BigQsqrt2, SplitExactAuditError> {
    if !value.is_finite() {
        return Err(SplitExactAuditError::Repair(
            "a numerical face correction is not finite".into(),
        ));
    }
    let denominator = 1_i128 << bits;
    let scaled = value * denominator as f64;
    if scaled.abs() > i128::MAX as f64 {
        return Err(SplitExactAuditError::Repair(
            "a numerical face correction is too large to round dyadically".into(),
        ));
    }
    Ok(BigQsqrt2::from_rational(BigRational::new(
        BigInt::from(scaled.round() as i128),
        BigInt::from(denominator),
    )))
}

fn apply_face_correction(
    variable: FaceRepairVariable,
    correction: &BigQsqrt2,
    multipliers: &mut [BigQsqrt2],
    normalization: &mut BigQsqrt2,
    faces: &mut [ParsedFaceBlock],
) {
    match variable {
        FaceRepairVariable::Equality(index) => {
            multipliers[index] = multipliers[index].add(correction);
        }
        FaceRepairVariable::Normalization => {
            *normalization = normalization.add(correction);
        }
        FaceRepairVariable::Coordinate { block, row, column } => {
            let repaired = faces[block].coordinates[row][column].add(correction);
            faces[block].coordinates[row][column] = repaired.clone();
            faces[block].coordinates[column][row] = repaired;
        }
    }
}

fn coordinate_psd_diagnostics(faces: &[ParsedFaceBlock]) -> (bool, Option<String>, f64) {
    let mut exact_psd = true;
    let mut exact_failure = None;
    for (block, face) in faces.iter().enumerate() {
        let rank = face.coordinates.len();
        if rank == 0 {
            continue;
        }
        let mut exact = ParsedGram::Quadratic(face.coordinates.clone());
        if let Err(error) = semidefinite_certificate(block, &mut exact) {
            exact_psd = false;
            if exact_failure.is_none() {
                exact_failure = Some(error.to_string());
            }
        }
    }
    (
        exact_psd,
        exact_failure,
        minimum_face_coordinate_eigenvalue(faces),
    )
}

fn minimum_face_coordinate_eigenvalue(faces: &[ParsedFaceBlock]) -> f64 {
    let minimum = faces
        .iter()
        .filter(|face| !face.coordinates.is_empty())
        .map(|face| {
            let rank = face.coordinates.len();
            nalgebra::DMatrix::from_fn(rank, rank, |row, column| {
                face.coordinates[row][column].to_f64().unwrap_or(f64::NAN)
            })
            .symmetric_eigen()
            .eigenvalues
            .min()
        })
        .fold(f64::INFINITY, f64::min);
    if minimum == f64::INFINITY {
        0.0
    } else {
        minimum
    }
}

/// Sparse finite-field elimination for wide face-coordinate operators. Unlike
/// the legacy dense selector below, this remains bounded when a restricted
/// face does not reach full row rank and therefore cannot take the early exit.
fn select_sparse_modular_column_basis(
    rows: usize,
    columns: &[BTreeMap<usize, BigQsqrt2>],
    stop_rank: usize,
) -> Result<Vec<(usize, usize)>, SplitExactAuditError> {
    const PRIME: u64 = 2_147_483_629;
    let mut selected = Vec::new();
    let mut basis_by_pivot = vec![None::<BTreeMap<usize, ModQsqrt2>>; rows];
    for (candidate, column) in columns.iter().enumerate() {
        let mut vector = column
            .iter()
            .map(|(&row, value)| quadratic_mod(value, PRIME).map(|value| (row, value)))
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        vector.retain(|_, value| *value != ModQsqrt2::ZERO);
        while let Some((&pivot, &pivot_value)) = vector.first_key_value() {
            if let Some(basis) = &basis_by_pivot[pivot] {
                for (&row, &basis_value) in basis {
                    let current = vector.get(&row).copied().unwrap_or(ModQsqrt2::ZERO);
                    let reduced = current.sub(pivot_value.mul(basis_value, PRIME), PRIME);
                    if reduced == ModQsqrt2::ZERO {
                        vector.remove(&row);
                    } else {
                        vector.insert(row, reduced);
                    }
                }
                continue;
            }
            let inverse = pivot_value.inverse(PRIME)?;
            for value in vector.values_mut() {
                *value = value.mul(inverse, PRIME);
            }
            basis_by_pivot[pivot] = Some(vector);
            selected.push((pivot, candidate));
            break;
        }
        if selected.len() == stop_rank {
            break;
        }
    }
    Ok(selected)
}

fn repair_split_exact_identity_inner(
    certificate: &mut SplitExactDualCertificate,
    allowed_grams: Option<&[bool]>,
) -> Result<(SplitExactRepairDiagnostics, Vec<usize>), SplitExactAuditError> {
    let assembled = assemble_split_repair(certificate, allowed_grams)?;
    finish_split_repair(certificate, assembled, None)
}

/// Everything the exact split identity repair assembles from a certificate
/// before any basis selection: parsed working values, the exact residual
/// (identity plus bound row), and the deduplicated repair-variable pool.
struct AssembledSplitRepair {
    layout: ValidatedLayout,
    multipliers: Vec<BigQsqrt2>,
    normalization: BigQsqrt2,
    target: BigQsqrt2,
    parsed_grams: Vec<ParsedGram>,
    parsed_kernels: Vec<ParsedRotatedKernelState>,
    residual: Vec<BigQsqrt2>,
    rows: usize,
    columns: Vec<RepairColumn>,
    block_margins: Vec<f64>,
    coefficient_count: usize,
    full_active_gram_coordinate_count: usize,
    unique_gram_signature_count: usize,
    available_affine_variable_count: usize,
    assembly_started: std::time::Instant,
    input_parse_and_residual_wall_seconds: f64,
    exact_gram_parse_wall_seconds: f64,
    initial_residual_reconstruction_wall_seconds: f64,
    gram_analysis_and_column_build_wall_seconds: f64,
    signature_deduplication_wall_seconds: f64,
}

fn assemble_split_repair(
    certificate: &SplitExactDualCertificate,
    allowed_grams: Option<&[bool]>,
) -> Result<AssembledSplitRepair, SplitExactAuditError> {
    assemble_split_repair_with_kernels(certificate, allowed_grams, &[])
}

fn assemble_split_repair_with_kernels(
    certificate: &SplitExactDualCertificate,
    allowed_grams: Option<&[bool]>,
    kernels: &[SplitRotatedKernelState],
) -> Result<AssembledSplitRepair, SplitExactAuditError> {
    let assembly_started = std::time::Instant::now();
    let input_started = std::time::Instant::now();
    let layout = validate_layout(certificate)?;
    let multipliers = flattened_multipliers(certificate)?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let gram_refs = flattened_grams(certificate);
    let gram_parse_started = std::time::Instant::now();
    let parsed_grams = parse_gram_refs(&gram_refs, &layout.dimensions)?;
    let parsed_kernels = parse_split_rotated_kernels(kernels, &layout.dimensions)?;
    let exact_gram_parse_wall_seconds = gram_parse_started.elapsed().as_secs_f64();
    let residual_started = std::time::Instant::now();
    let mut residual = reconstructed_identity_from_parsed(
        &layout.model,
        &multipliers,
        &normalization,
        &parsed_grams,
    );
    residual.push(reconstructed_bound(&layout.model, &multipliers, &normalization).sub(&target));
    residual.extend(exact_kernel_residuals(
        &parsed_grams,
        &parsed_kernels,
        &layout.dimensions,
    ));
    let initial_residual_reconstruction_wall_seconds = residual_started.elapsed().as_secs_f64();
    let input_parse_and_residual_wall_seconds = input_started.elapsed().as_secs_f64();
    let coefficient_count = layout.model.coefficient_count();
    let rows = residual.len();
    let gram_analysis_started = std::time::Instant::now();
    let mut active = active_parsed_gram_blocks(&parsed_grams);
    if let Some(allowed) = allowed_grams {
        for (is_active, &is_allowed) in active.iter_mut().zip(allowed) {
            *is_active &= is_allowed;
        }
    }
    let active_rows = active_parsed_gram_rows(&parsed_grams);
    let block_margins = parsed_grams
        .iter()
        .zip(&layout.dimensions)
        .zip(&active)
        .map(|((matrix, &dimension), &is_active)| {
            if is_active {
                reconstructed_parsed_matrix_minimum(matrix, dimension)
            } else {
                Ok(f64::NEG_INFINITY)
            }
        })
        .collect::<Result<Vec<_>, SplitExactAuditError>>()?;
    let (mut all_gram_columns, full_active_gram_coordinate_count) = all_gram_repair_columns(
        &layout.model,
        &layout.dimensions,
        &active,
        Some(&active_rows),
    );
    augment_gram_columns_with_kernel_equalities(
        &mut all_gram_columns,
        &parsed_kernels,
        &layout.dimensions,
        &active_rows,
        coefficient_count + 1,
    );
    let gram_analysis_and_column_build_wall_seconds = gram_analysis_started.elapsed().as_secs_f64();
    // Exact coefficient signatures can occur in many Gram blocks. Prefer the
    // representative with the largest reconstructed spectral margin, so the
    // advisory modular basis does not assign a necessary exact correction to
    // an avoidably singular block. The final solve and all acceptance checks
    // remain exact over Q(sqrt(2)).
    let signature_started = std::time::Instant::now();
    let mut signature_indices: HashMap<Vec<(usize, crate::Qsqrt2)>, usize> = HashMap::new();
    let mut gram_columns: Vec<RepairColumn> = Vec::new();
    for column in all_gram_columns {
        let RepairVariable::Gram { block, .. } = column.variable else {
            unreachable!("Gram column builder returned a non-Gram variable")
        };
        let signature = column
            .coefficients
            .iter()
            .map(|(&position, &value)| (position, value))
            .collect::<Vec<_>>();
        if let Some(&index) = signature_indices.get(&signature) {
            let RepairVariable::Gram {
                block: retained_block,
                ..
            } = gram_columns[index].variable
            else {
                unreachable!("Gram signature retained a non-Gram variable")
            };
            if block_margins[block] > block_margins[retained_block] {
                gram_columns[index] = column;
            }
        } else {
            signature_indices.insert(signature, gram_columns.len());
            gram_columns.push(column);
        }
    }
    // Preserve the established support-size basis order. Reordering the whole
    // system by margin can join thousands of otherwise independent exact
    // components and amplify tiny residuals; replacing a representative by an
    // identical, safer signature does not change that sparse coefficient map.
    gram_columns.sort_by_key(|column| column.coefficients.len());
    let unique_gram_signature_count = gram_columns.len();
    let affine = affine_repair_columns(&layout.model, coefficient_count);
    let available_affine_variable_count = affine.len();
    let mut columns = gram_columns;
    columns.extend(affine);
    let signature_deduplication_wall_seconds = signature_started.elapsed().as_secs_f64();
    Ok(AssembledSplitRepair {
        layout,
        multipliers,
        normalization,
        target,
        parsed_grams,
        parsed_kernels,
        residual,
        rows,
        columns,
        block_margins,
        coefficient_count,
        full_active_gram_coordinate_count,
        unique_gram_signature_count,
        available_affine_variable_count,
        assembly_started,
        input_parse_and_residual_wall_seconds,
        exact_gram_parse_wall_seconds,
        initial_residual_reconstruction_wall_seconds,
        gram_analysis_and_column_build_wall_seconds,
        signature_deduplication_wall_seconds,
    })
}

/// Order the repair-variable pool so preferred variables (for example an
/// LP-guided low-damage support) are offered to the advisory modular basis
/// selection first. Unlisted variables keep their established pool order as a
/// fallback, so an under-rank preference cannot fail closure outright.
fn repair_preference_order(
    pool: usize,
    preference: &[usize],
) -> Result<Vec<usize>, SplitExactAuditError> {
    let mut seen = vec![false; pool];
    let mut order = Vec::with_capacity(pool);
    for &index in preference {
        let Some(registered) = seen.get_mut(index) else {
            return Err(SplitExactAuditError::Repair(format!(
                "repair preference index {index} is outside the {pool}-variable pool"
            )));
        };
        if *registered {
            continue;
        }
        *registered = true;
        order.push(index);
    }
    order.extend((0..pool).filter(|&index| !seen[index]));
    Ok(order)
}

fn finish_split_repair(
    certificate: &mut SplitExactDualCertificate,
    assembled: AssembledSplitRepair,
    preference: Option<&[usize]>,
) -> Result<(SplitExactRepairDiagnostics, Vec<usize>), SplitExactAuditError> {
    let AssembledSplitRepair {
        layout,
        mut multipliers,
        mut normalization,
        target,
        mut parsed_grams,
        parsed_kernels,
        residual,
        rows,
        columns,
        block_margins,
        coefficient_count,
        full_active_gram_coordinate_count,
        unique_gram_signature_count,
        available_affine_variable_count,
        assembly_started: total_started,
        input_parse_and_residual_wall_seconds,
        exact_gram_parse_wall_seconds,
        initial_residual_reconstruction_wall_seconds,
        gram_analysis_and_column_build_wall_seconds,
        signature_deduplication_wall_seconds,
    } = assembled;
    // An LP-guided preference is honored by a direct finite-field scan in
    // preference order, so the selected basis stays inside the preferred
    // support whenever that support spans. The default path keeps the stable
    // component-local QR layer. Both selections are advisory only: the solve
    // and every acceptance check remain exact over Q(sqrt(2)).
    let basis_started = std::time::Instant::now();
    let selected = if let Some(preference) = preference {
        let order = repair_preference_order(columns.len(), preference)?;
        select_modular_column_basis_in_order(rows, &columns, &order)?
    } else {
        select_stable_modular_column_basis(rows, &columns)?
    };
    let modular_basis_selection_wall_seconds = basis_started.elapsed().as_secs_f64();
    let rank = selected.len();
    let selected_affine_variable_count = selected
        .iter()
        .filter(|&&(_, candidate)| {
            matches!(
                columns[candidate].variable,
                RepairVariable::Equality(_) | RepairVariable::Normalization
            )
        })
        .count();
    let selected_gram_variable_count = rank - selected_affine_variable_count;
    let selected_gram_blocks = selected
        .iter()
        .filter_map(|&(_, candidate)| match columns[candidate].variable {
            RepairVariable::Gram { block, .. } => Some(block),
            RepairVariable::Equality(_) | RepairVariable::Normalization => None,
        })
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let minimum_selected_gram_margin_before_repair = selected
        .iter()
        .filter_map(|&(_, candidate)| match columns[candidate].variable {
            RepairVariable::Gram { block, .. } => Some(block_margins[block]),
            RepairVariable::Equality(_) | RepairVariable::Normalization => None,
        })
        .min_by(f64::total_cmp);
    let solve_started = std::time::Instant::now();
    let ExactComponentSolution {
        corrections,
        component_count: exact_component_count,
        largest_component: largest_exact_component,
    } = solve_exact_components(&selected, &columns, &residual)?;
    let exact_component_solve_wall_seconds = solve_started.elapsed().as_secs_f64();
    let correction_started = std::time::Instant::now();
    let maximum_absolute_exact_correction = corrections
        .iter()
        .map(|(_, value)| finite(value, "exact correction").map(f64::abs))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .fold(0.0, f64::max);
    let gram_updates = apply_repair_corrections(
        &columns,
        corrections,
        &mut multipliers,
        &mut normalization,
        &mut parsed_grams,
    );
    let correction_apply_wall_seconds = correction_started.elapsed().as_secs_f64();
    let write_back_started = std::time::Instant::now();
    write_repair_updates(certificate, &multipliers, &normalization, gram_updates);
    let write_back_wall_seconds = write_back_started.elapsed().as_secs_f64();
    let post_check_started = std::time::Instant::now();
    let remaining = reconstructed_identity_from_parsed(
        &layout.model,
        &multipliers,
        &normalization,
        &parsed_grams,
    )
    .iter()
    .filter(|value| !value.is_zero())
    .count();
    let repaired_bound = reconstructed_bound(&layout.model, &multipliers, &normalization);
    let kernel_remaining =
        exact_kernel_residuals(&parsed_grams, &parsed_kernels, &layout.dimensions)
            .iter()
            .filter(|value| !value.is_zero())
            .count();
    if remaining != 0 || repaired_bound != target || kernel_remaining != 0 {
        return Err(SplitExactAuditError::Repair(format!(
            "post-repair check has {remaining} nonzero coefficients, {kernel_remaining} nonzero rotated-kernel residuals, and bound {repaired_bound} instead of target {target}"
        )));
    }
    let post_repair_exact_check_wall_seconds = post_check_started.elapsed().as_secs_f64();
    Ok((
        SplitExactRepairDiagnostics {
            coefficient_count,
            equation_count_with_bound: rows,
            full_active_gram_coordinate_count,
            unique_gram_signature_count,
            available_affine_variable_count,
            selected_exact_rank: rank,
            selected_affine_variable_count,
            selected_gram_variable_count,
            minimum_selected_gram_margin_before_repair,
            exact_component_count,
            largest_exact_component,
            maximum_absolute_exact_correction,
            timings: SplitExactRepairTimings {
                input_parse_and_residual_wall_seconds,
                exact_gram_parse_wall_seconds,
                initial_residual_reconstruction_wall_seconds,
                gram_analysis_and_column_build_wall_seconds,
                signature_deduplication_wall_seconds,
                modular_basis_selection_wall_seconds,
                exact_component_solve_wall_seconds,
                correction_apply_wall_seconds,
                write_back_wall_seconds,
                post_repair_exact_check_wall_seconds,
                total_wall_seconds: total_started.elapsed().as_secs_f64(),
            },
        },
        selected_gram_blocks,
    ))
}

/// Reconstruct every exact Gram as `f64` and report the smallest numerical
/// eigenvalue. This is a conditioning diagnostic only; exact PSD still requires
/// the native LDL audit.
pub fn minimum_reconstructed_split_gram_eigenvalue(
    certificate: &SplitExactDualCertificate,
) -> Result<f64, SplitExactAuditError> {
    let layout = validate_layout(certificate)?;
    let grams = flattened_grams(certificate);
    let parsed = parse_gram_refs(&grams, &layout.dimensions)?;
    parsed
        .par_iter()
        .zip(&layout.dimensions)
        .map(|(matrix, &dimension)| reconstructed_parsed_matrix_minimum(matrix, dimension))
        .try_reduce(|| f64::INFINITY, |left, right| Ok(left.min(right)))
}

/// Floating diagnostic for distinguishing coordinate-axis near-null modes from
/// modes that require a rotated face. It is never an acceptance gate.
pub fn split_near_null_eigen_diagnostics(
    certificate: &SplitExactDualCertificate,
    eigenvalue_threshold: f64,
) -> Result<SplitNearNullEigenDiagnostics, SplitExactAuditError> {
    if !eigenvalue_threshold.is_finite() || eigenvalue_threshold <= 0.0 {
        return Err(SplitExactAuditError::Repair(
            "near-null diagnostic threshold must be finite and positive".into(),
        ));
    }
    let layout = validate_layout(certificate)?;
    let grams = flattened_grams(certificate);
    let parsed = parse_gram_refs(&grams, &layout.dimensions)?;
    let mut active_gram_count = 0;
    let mut gram_count_with_subthreshold_eigenvalues = 0;
    let mut subthreshold_eigenvalue_count = 0;
    let mut axis_aligned_eigenvalue_count = 0;
    let mut rotated_eigenvalue_count = 0;
    let mut minimum_eigenvalue = f64::INFINITY;
    let mut maximum_subthreshold_eigenvalue = f64::NEG_INFINITY;
    for (matrix, &dimension) in parsed.iter().zip(&layout.dimensions) {
        if matrix.is_zero_matrix() {
            continue;
        }
        active_gram_count += 1;
        let live_rows = (0..dimension)
            .filter(|&row| !matrix.entry_is_zero(row, row))
            .collect::<Vec<_>>();
        if live_rows.is_empty() {
            continue;
        }
        let numeric = DMatrix::from_fn(live_rows.len(), live_rows.len(), |row, column| {
            parsed_gram_entry(matrix, live_rows[row], live_rows[column])
                .to_f64()
                .unwrap_or(f64::NAN)
        });
        let eigen = numeric.symmetric_eigen();
        if eigen.eigenvalues.iter().any(|value| !value.is_finite()) {
            return Err(SplitExactAuditError::Repair(
                "near-null diagnostic encountered a non-finite eigenvalue".into(),
            ));
        }
        let mut block_has_subthreshold = false;
        for (index, &value) in eigen.eigenvalues.iter().enumerate() {
            minimum_eigenvalue = minimum_eigenvalue.min(value);
            if value >= eigenvalue_threshold {
                continue;
            }
            block_has_subthreshold = true;
            subthreshold_eigenvalue_count += 1;
            maximum_subthreshold_eigenvalue = maximum_subthreshold_eigenvalue.max(value);
            let maximum_axis_weight = eigen
                .eigenvectors
                .column(index)
                .iter()
                .map(|entry| entry * entry)
                .fold(0.0, f64::max);
            if maximum_axis_weight >= AXIS_ALIGNMENT_SQUARED_THRESHOLD {
                axis_aligned_eigenvalue_count += 1;
            } else {
                rotated_eigenvalue_count += 1;
            }
        }
        gram_count_with_subthreshold_eigenvalues += usize::from(block_has_subthreshold);
    }
    if minimum_eigenvalue == f64::INFINITY {
        minimum_eigenvalue = 0.0;
    }
    if maximum_subthreshold_eigenvalue == f64::NEG_INFINITY {
        maximum_subthreshold_eigenvalue = 0.0;
    }
    Ok(SplitNearNullEigenDiagnostics {
        eigenvalue_threshold,
        axis_alignment_squared_threshold: AXIS_ALIGNMENT_SQUARED_THRESHOLD,
        active_gram_count,
        gram_count_with_subthreshold_eigenvalues,
        subthreshold_eigenvalue_count,
        axis_aligned_eigenvalue_count,
        rotated_eigenvalue_count,
        minimum_eigenvalue,
        maximum_subthreshold_eigenvalue,
    })
}

fn apply_repair_corrections(
    columns: &[RepairColumn],
    corrections: Vec<(usize, BigQsqrt2)>,
    multipliers: &mut [BigQsqrt2],
    normalization: &mut BigQsqrt2,
    parsed_grams: &mut [ParsedGram],
) -> Vec<(usize, usize, usize, String)> {
    let mut gram_updates = Vec::new();
    for (candidate, correction) in corrections {
        match columns[candidate].variable {
            RepairVariable::Equality(index) => {
                multipliers[index] = multipliers[index].add(&correction);
            }
            RepairVariable::Normalization => *normalization = normalization.add(&correction),
            RepairVariable::Gram { block, row, column } => {
                let current = parsed_gram_entry(&parsed_grams[block], row, column);
                let repaired = current.add(&correction);
                set_parsed_gram_entry(&mut parsed_grams[block], row, column, repaired.clone());
                gram_updates.push((block, row, column, repaired.to_string()));
            }
        }
    }
    gram_updates
}

/// Order candidate columns by component-local floating column-pivoted QR, then
/// select a basis over a large finite field. The floating pass only improves
/// conditioning: modular rank selection, the solve, and the full post-check
/// remain exact in `Q(sqrt(2))`.
fn select_stable_modular_column_basis(
    rows: usize,
    columns: &[RepairColumn],
) -> Result<Vec<(usize, usize)>, SplitExactAuditError> {
    let original_order = (0..columns.len()).collect::<Vec<_>>();
    let baseline = select_modular_column_basis_in_order(rows, columns, &original_order)?;
    let pivot_lookup = baseline
        .iter()
        .enumerate()
        .map(|(local, &(row, _))| (row, local))
        .collect::<HashMap<_, _>>();
    let mut components = DisjointSet::new(baseline.len());
    for &(_, candidate) in &baseline {
        let mut support = columns[candidate]
            .coefficients
            .keys()
            .filter_map(|row| pivot_lookup.get(row).copied());
        if let Some(first) = support.next() {
            for row in support {
                components.join(first, row);
            }
        }
    }
    let root_by_pivot = baseline
        .iter()
        .enumerate()
        .map(|(local, &(row, _))| (row, components.root(local)))
        .collect::<HashMap<_, _>>();
    let mut grouped_rows = BTreeMap::<usize, Vec<usize>>::new();
    for &(row, _) in &baseline {
        grouped_rows
            .entry(root_by_pivot[&row])
            .or_default()
            .push(row);
    }
    let mut grouped_candidates = BTreeMap::<usize, Vec<usize>>::new();
    for (candidate, column) in columns.iter().enumerate() {
        let mut roots = column
            .coefficients
            .keys()
            .filter_map(|row| root_by_pivot.get(row).copied());
        let Some(root) = roots.next() else {
            continue;
        };
        // Keep the baseline direct-sum structure sparse. Cross-component
        // alternatives are unnecessary because every baseline column remains
        // available in its component. The final full exact identity check
        // still rejects any bad advisory choice.
        if roots.all(|other| other == root) {
            grouped_candidates.entry(root).or_default().push(candidate);
        }
    }

    let mut selected = Vec::with_capacity(baseline.len());
    for (component, component_rows) in grouped_rows {
        let candidates = &grouped_candidates[&component];
        let row_lookup = component_rows
            .iter()
            .enumerate()
            .map(|(local, &row)| (row, local))
            .collect::<HashMap<_, _>>();
        let mut matrix = DMatrix::zeros(component_rows.len(), candidates.len());
        for (local_column, &candidate) in candidates.iter().enumerate() {
            for (&row, &value) in &columns[candidate].coefficients {
                if let Some(&local_row) = row_lookup.get(&row) {
                    matrix[(local_row, local_column)] = value.to_f64();
                }
            }
        }
        let qr = matrix.col_piv_qr();
        let mut permuted = DMatrix::from_row_iterator(1, candidates.len(), 0..candidates.len());
        qr.p().permute_columns(&mut permuted);
        let projected = candidates
            .iter()
            .map(|&candidate| RepairColumn {
                variable: columns[candidate].variable,
                coefficients: columns[candidate]
                    .coefficients
                    .iter()
                    .filter_map(|(&row, &value)| row_lookup.get(&row).map(|&local| (local, value)))
                    .collect(),
            })
            .collect::<Vec<_>>();
        let order = permuted.row(0).iter().copied().collect::<Vec<_>>();
        let local = select_modular_column_basis_in_order(component_rows.len(), &projected, &order)?;
        if local.len() != component_rows.len() {
            return Err(SplitExactAuditError::Repair(format!(
                "stable exact basis lost rank in component {component}: selected {} of {} rows",
                local.len(),
                component_rows.len()
            )));
        }
        selected.extend(
            local
                .into_iter()
                .map(|(row, candidate)| (component_rows[row], candidates[candidate])),
        );
    }
    Ok(selected)
}

/// Select a column basis over a large finite field in the supplied advisory
/// order. This avoids dropping exact split-operator directions through
/// floating cancellation. An unlucky modular specialization cannot certify
/// anything because the solve and full post-check remain exact.
fn select_modular_column_basis_in_order(
    rows: usize,
    columns: &[RepairColumn],
    order: &[usize],
) -> Result<Vec<(usize, usize)>, SplitExactAuditError> {
    // 2 is a quadratic nonresidue modulo this prime, so adjoining t^2=2
    // yields a field and preserves separate rational/surd directions.
    const PRIME: u64 = 2_147_483_629;
    let mut selected: Vec<(usize, usize)> = Vec::new();
    let mut modular_basis: Vec<BTreeMap<usize, ModQsqrt2>> = Vec::new();
    for &candidate in order {
        let column = &columns[candidate];
        let mut vector = BTreeMap::new();
        for (&row, &value) in &column.coefficients {
            debug_assert!(row < rows);
            let value = quadratic_mod(&BigQsqrt2::from_small(value), PRIME)?;
            if value != ModQsqrt2::ZERO {
                vector.insert(row, value);
            }
        }
        for (&(pivot, _), basis) in selected.iter().zip(&modular_basis) {
            let Some(factor) = vector.get(&pivot).copied() else {
                continue;
            };
            for (&row, &basis_value) in basis {
                let current = vector.get(&row).copied().unwrap_or(ModQsqrt2::ZERO);
                let updated = current.sub(factor.mul(basis_value, PRIME), PRIME);
                if updated == ModQsqrt2::ZERO {
                    vector.remove(&row);
                } else {
                    vector.insert(row, updated);
                }
            }
        }
        let Some((&pivot, &pivot_value)) = vector.first_key_value() else {
            continue;
        };
        let inverse = pivot_value.inverse(PRIME)?;
        for value in &mut vector {
            *value.1 = value.1.mul(inverse, PRIME);
        }
        selected.push((pivot, candidate));
        modular_basis.push(vector);
        if selected.len() == rows {
            break;
        }
    }
    Ok(selected)
}

fn select_face_modular_column_basis_until(
    rows: usize,
    columns: &[BTreeMap<usize, BigQsqrt2>],
    stop_rank: usize,
) -> Result<Vec<(usize, usize)>, SplitExactAuditError> {
    // 2 is a quadratic nonresidue modulo this prime, so adjoining t^2=2
    // yields a field and preserves separate rational/surd directions.
    const PRIME: u64 = 2_147_483_629;
    let mut selected: Vec<(usize, usize)> = Vec::new();
    let mut modular_basis: Vec<Vec<ModQsqrt2>> = Vec::new();
    for (candidate, column) in columns.iter().enumerate() {
        let mut vector = vec![ModQsqrt2::ZERO; rows];
        for (&row, value) in column {
            vector[row] = quadratic_mod(value, PRIME)?;
        }
        for (&(pivot, _), basis) in selected.iter().zip(&modular_basis) {
            let factor = vector[pivot];
            if factor != ModQsqrt2::ZERO {
                for row in 0..rows {
                    vector[row] = vector[row].sub(factor.mul(basis[row], PRIME), PRIME);
                }
            }
        }
        let Some(pivot) = vector.iter().position(|&value| value != ModQsqrt2::ZERO) else {
            continue;
        };
        let inverse = vector[pivot].inverse(PRIME)?;
        for value in &mut vector {
            *value = value.mul(inverse, PRIME);
        }
        selected.push((pivot, candidate));
        modular_basis.push(vector);
        if selected.len() == stop_rank {
            break;
        }
    }
    Ok(selected)
}

struct DisjointSet {
    parents: Vec<usize>,
    sizes: Vec<usize>,
}

impl DisjointSet {
    fn new(size: usize) -> Self {
        Self {
            parents: (0..size).collect(),
            sizes: vec![1; size],
        }
    }

    fn root(&mut self, value: usize) -> usize {
        if self.parents[value] != value {
            self.parents[value] = self.root(self.parents[value]);
        }
        self.parents[value]
    }

    fn join(&mut self, left: usize, right: usize) {
        let mut left = self.root(left);
        let mut right = self.root(right);
        if left == right {
            return;
        }
        if self.sizes[left] < self.sizes[right] {
            std::mem::swap(&mut left, &mut right);
        }
        self.parents[right] = left;
        self.sizes[left] += self.sizes[right];
    }
}

struct ExactComponentSolution {
    corrections: Vec<(usize, BigQsqrt2)>,
    component_count: usize,
    largest_component: usize,
}

fn solve_exact_components(
    selected: &[(usize, usize)],
    columns: &[RepairColumn],
    residual: &[BigQsqrt2],
) -> Result<ExactComponentSolution, SplitExactAuditError> {
    let pivot_lookup = selected
        .iter()
        .enumerate()
        .map(|(local, &(pivot, _))| (pivot, local))
        .collect::<HashMap<_, _>>();
    let mut components = DisjointSet::new(selected.len());
    for &(_, candidate) in selected {
        let mut support = columns[candidate]
            .coefficients
            .keys()
            .filter_map(|row| pivot_lookup.get(row).copied());
        if let Some(first) = support.next() {
            for row in support {
                components.join(first, row);
            }
        }
    }
    let mut grouped = BTreeMap::<usize, Vec<(usize, usize)>>::new();
    for &(pivot, candidate) in selected {
        let local = pivot_lookup[&pivot];
        grouped
            .entry(components.root(local))
            .or_default()
            .push((pivot, candidate));
    }
    let largest = grouped.values().map(Vec::len).max().unwrap_or(0);
    let count = grouped.len();
    let solved = grouped
        .into_values()
        .collect::<Vec<_>>()
        .into_par_iter()
        .map(|component| solve_sparse_exact_component(&component, columns, residual))
        .collect::<Result<Vec<_>, _>>()?;
    let corrections = solved.into_iter().flatten().collect();
    Ok(ExactComponentSolution {
        corrections,
        component_count: count,
        largest_component: largest,
    })
}

fn solve_sparse_exact_component(
    selected: &[(usize, usize)],
    columns: &[RepairColumn],
    residual: &[BigQsqrt2],
) -> Result<Vec<(usize, BigQsqrt2)>, SplitExactAuditError> {
    let rank = selected.len();
    let row_lookup = selected
        .iter()
        .enumerate()
        .map(|(local, &(row, _))| (row, local))
        .collect::<HashMap<_, _>>();
    let mut matrix = vec![BTreeMap::<usize, BigQsqrt2>::new(); rank];
    for (column, &(_, candidate)) in selected.iter().enumerate() {
        for (&row, &value) in &columns[candidate].coefficients {
            if let Some(&local_row) = row_lookup.get(&row) {
                matrix[local_row].insert(column, BigQsqrt2::from_small(value));
            }
        }
    }
    let mut rhs = selected
        .iter()
        .map(|&(row, _)| residual[row].neg())
        .collect::<Vec<_>>();
    for column in 0..rank {
        let found = (column..rank)
            .find(|&row| matrix[row].get(&column).is_some_and(|value| !value.is_zero()))
            .ok_or_else(|| {
                SplitExactAuditError::Repair(format!(
                    "finite-field-selected sparse basis is exactly singular at component column {column}"
                ))
            })?;
        matrix.swap(column, found);
        rhs.swap(column, found);
        let pivot = matrix[column][&column].clone();
        let pivot_row = matrix[column]
            .range(column..)
            .map(|(&entry, value)| (entry, value.clone()))
            .collect::<Vec<_>>();
        let pivot_rhs = rhs[column].clone();
        for row in column + 1..rank {
            let Some(value) = matrix[row].get(&column).cloned() else {
                continue;
            };
            if value.is_zero() {
                matrix[row].remove(&column);
                continue;
            }
            let factor = value.div(&pivot)?;
            for (entry, pivot_value) in &pivot_row {
                let current = matrix[row]
                    .get(entry)
                    .cloned()
                    .unwrap_or_else(BigQsqrt2::zero);
                let updated = current.sub(&factor.mul(pivot_value));
                if updated.is_zero() {
                    matrix[row].remove(entry);
                } else {
                    matrix[row].insert(*entry, updated);
                }
            }
            rhs[row] = rhs[row].sub(&factor.mul(&pivot_rhs));
        }
    }
    let mut solution = vec![BigQsqrt2::zero(); rank];
    for row in (0..rank).rev() {
        let pivot = matrix[row].get(&row).ok_or_else(|| {
            SplitExactAuditError::Repair(format!(
                "sparse exact back substitution has no pivot at row {row}"
            ))
        })?;
        let mut value = rhs[row].clone();
        for (&column, coefficient) in matrix[row].range(row + 1..) {
            value = value.sub(&coefficient.mul(&solution[column]));
        }
        solution[row] = value.div(pivot)?;
    }
    Ok(selected
        .iter()
        .zip(solution)
        .map(|(&(_, candidate), correction)| (candidate, correction))
        .collect())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ModQsqrt2 {
    rational: u64,
    sqrt2: u64,
}

impl ModQsqrt2 {
    const ZERO: Self = Self {
        rational: 0,
        sqrt2: 0,
    };

    fn sub(self, rhs: Self, prime: u64) -> Self {
        Self {
            rational: (self.rational + prime - rhs.rational) % prime,
            sqrt2: (self.sqrt2 + prime - rhs.sqrt2) % prime,
        }
    }

    fn mul(self, rhs: Self, prime: u64) -> Self {
        let modulus = u128::from(prime);
        let rational = (u128::from(self.rational) * u128::from(rhs.rational)
            + 2 * u128::from(self.sqrt2) * u128::from(rhs.sqrt2))
            % modulus;
        let sqrt2 = (u128::from(self.rational) * u128::from(rhs.sqrt2)
            + u128::from(self.sqrt2) * u128::from(rhs.rational))
            % modulus;
        Self {
            rational: rational as u64,
            sqrt2: sqrt2 as u64,
        }
    }

    fn inverse(self, prime: u64) -> Result<Self, SplitExactAuditError> {
        let modulus = u128::from(prime);
        let norm = (u128::from(self.rational) * u128::from(self.rational) + modulus
            - (2 * u128::from(self.sqrt2) * u128::from(self.sqrt2)) % modulus)
            % modulus;
        if norm == 0 {
            return Err(SplitExactAuditError::Repair(
                "finite-field rank selection encountered a zero norm".into(),
            ));
        }
        let inverse_norm = modular_power(norm as u64, prime - 2, prime);
        Ok(Self {
            rational: ((u128::from(self.rational) * u128::from(inverse_norm)) % modulus) as u64,
            sqrt2: ((u128::from(prime - self.sqrt2) * u128::from(inverse_norm)) % modulus) as u64,
        })
    }
}

fn quadratic_mod(value: &BigQsqrt2, prime: u64) -> Result<ModQsqrt2, SplitExactAuditError> {
    Ok(ModQsqrt2 {
        rational: rational_mod(&value.rational, prime)?,
        sqrt2: rational_mod(&value.sqrt2, prime)?,
    })
}

fn rational_mod(value: &BigRational, prime: u64) -> Result<u64, SplitExactAuditError> {
    let modulus = BigInt::from(prime);
    let numerator = value.numer().mod_floor(&modulus).to_u64_digits();
    let denominator = value.denom().mod_floor(&modulus).to_u64_digits();
    let numerator = numerator.1.first().copied().unwrap_or(0);
    let denominator = denominator.1.first().copied().unwrap_or(0);
    if denominator == 0 {
        return Err(SplitExactAuditError::Repair(
            "modular rank prime divides an exact denominator".into(),
        ));
    }
    let inverse = modular_power(denominator, prime - 2, prime);
    Ok(((u128::from(numerator) * u128::from(inverse)) % u128::from(prime)) as u64)
}

fn modular_power(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1_u64;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result = ((u128::from(result) * u128::from(base)) % u128::from(modulus)) as u64;
        }
        base = ((u128::from(base) * u128::from(base)) % u128::from(modulus)) as u64;
        exponent >>= 1;
    }
    result
}

#[allow(clippy::needless_range_loop)]
fn exact_gaussian_elimination(system: &mut [Vec<BigQsqrt2>]) -> Result<(), SplitExactAuditError> {
    let rank = system.len();
    for column in 0..rank {
        let found = (column..rank)
            .find(|&row| !system[row][column].is_zero())
            .ok_or_else(|| {
                SplitExactAuditError::Repair(format!(
                    "finite-field-selected basis is exactly singular at column {column}"
                ))
            })?;
        system.swap(column, found);
        let pivot = system[column][column].clone();
        let pivot_row = system[column][column + 1..=rank].to_vec();
        for row in column + 1..rank {
            if system[row][column].is_zero() {
                continue;
            }
            let factor = system[row][column].div(&pivot)?;
            system[row][column] = BigQsqrt2::zero();
            for (value, pivot_value) in system[row][column + 1..=rank].iter_mut().zip(&pivot_row) {
                *value = value.sub(&factor.mul(pivot_value));
            }
        }
    }
    let mut solution = vec![BigQsqrt2::zero(); rank];
    for row in (0..rank).rev() {
        let mut value = system[row][rank].clone();
        for (coefficient, solved) in system[row][row + 1..rank].iter().zip(&solution[row + 1..]) {
            value = value.sub(&coefficient.mul(solved));
        }
        solution[row] = value.div(&system[row][row])?;
    }
    for (row, value) in solution.into_iter().enumerate() {
        system[row][rank] = value;
    }
    Ok(())
}

fn write_repair_updates(
    certificate: &mut SplitExactDualCertificate,
    multipliers: &[BigQsqrt2],
    normalization: &BigQsqrt2,
    updates: Vec<(usize, usize, usize, String)>,
) {
    for (target, value) in certificate
        .liouville_multipliers_by_cell
        .iter_mut()
        .flatten()
        .zip(multipliers)
    {
        *target = value.to_string();
    }
    certificate.normalization = normalization.to_string();
    let mut updates_by_block = BTreeMap::<usize, Vec<(usize, usize, String)>>::new();
    for (block, row, column, value) in updates {
        updates_by_block
            .entry(block)
            .or_default()
            .push((row, column, value));
    }
    for (block, matrix) in certificate
        .occupation_grams_by_cell
        .iter_mut()
        .flatten()
        .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
        .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
        .enumerate()
    {
        let Some(updates) = updates_by_block.remove(&block) else {
            continue;
        };
        for (row, column, value) in updates {
            matrix[row][column] = value.clone();
            matrix[column][row] = value;
        }
    }
    debug_assert!(updates_by_block.is_empty());
}

fn write_back(
    certificate: &mut SplitExactDualCertificate,
    model: &ExactSplitModel,
    multipliers: &[BigQsqrt2],
    normalization: &BigQsqrt2,
    grams: Vec<EncodedMatrix>,
) {
    for (target, value) in certificate
        .liouville_multipliers_by_cell
        .iter_mut()
        .flatten()
        .zip(multipliers)
    {
        *target = value.to_string();
    }
    certificate.normalization = normalization.to_string();
    let occupation_count = model.cell_count() * model.occupation_gram_count_per_cell();
    let interface_count =
        model.cell_count().saturating_sub(1) * model.interface_gram_count_per_interface();
    let mut grams = grams.into_iter();
    for group in &mut certificate.occupation_grams_by_cell {
        for target in group {
            *target = grams.next().expect("validated occupation Gram count");
        }
    }
    debug_assert_eq!(
        certificate
            .occupation_grams_by_cell
            .iter()
            .map(Vec::len)
            .sum::<usize>(),
        occupation_count
    );
    for group in &mut certificate.interface_grams_by_knot {
        for target in group {
            *target = grams.next().expect("validated interface Gram count");
        }
    }
    debug_assert_eq!(
        certificate
            .interface_grams_by_knot
            .iter()
            .map(Vec::len)
            .sum::<usize>(),
        interface_count
    );
    for group in &mut certificate.terminal_grams_by_cell {
        for target in group {
            *target = grams.next().expect("validated terminal Gram count");
        }
    }
    debug_assert!(grams.next().is_none());
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    fn zero_matrix(side: usize) -> EncodedMatrix {
        vec![vec!["0".into(); side]; side]
    }

    fn structural_certificate() -> SplitExactDualCertificate {
        let order = 2;
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let model = ExactSplitModel::create(order, &grid).unwrap();
        let structure = structure(order, &grid).unwrap();
        let dimensions = model.gram_dimensions();
        let mut position = 0;
        let occupation_grams_by_cell = (0..model.cell_count())
            .map(|_| {
                (0..model.occupation_gram_count_per_cell())
                    .map(|_| {
                        let side = dimensions[position];
                        position += 1;
                        zero_matrix(side)
                    })
                    .collect()
            })
            .collect();
        let interface_grams_by_knot = (0..model.cell_count() - 1)
            .map(|_| {
                (0..model.interface_gram_count_per_interface())
                    .map(|_| {
                        let side = dimensions[position];
                        position += 1;
                        zero_matrix(side)
                    })
                    .collect()
            })
            .collect();
        let terminal_grams_by_cell = (0..model.cell_count())
            .map(|_| {
                (0..2)
                    .map(|_| {
                        let side = dimensions[position];
                        position += 1;
                        zero_matrix(side)
                    })
                    .collect()
            })
            .collect();
        SplitExactDualCertificate {
            schema: SPLIT_EXACT_SCHEMA_V1.into(),
            order,
            knots: grid.canonical_knots(),
            split_grid_hash: grid.canonical_hash(),
            formulation_hash: structure.formulation_hash,
            exposure_upper: EXPOSURE_UPPER.to_string(),
            bound_target: "-1".into(),
            equality_order: EQUALITY_ORDER_V1.into(),
            liouville_multipliers_by_cell: vec![
                vec!["0".into(); model.equality_count_per_cell()];
                model.cell_count()
            ],
            normalization: "0".into(),
            gram_order: GRAM_ORDER_V1.into(),
            occupation_grams_by_cell,
            interface_grams_by_knot,
            terminal_grams_by_cell,
            provenance: None,
        }
    }

    fn weak_exact_certificate() -> SplitExactDualCertificate {
        let mut certificate = structural_certificate();
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let model = ExactSplitModel::create(certificate.order, &grid).unwrap();
        let dimensions = model.gram_dimensions();
        let mut cost = Vec::new();
        model.for_each_cost_coefficient(|position, coefficient| cost.push((position, coefficient)));
        let mut grams = flattened_grams(&certificate)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        for (cost_position, cost_coefficient) in cost {
            let (block, gram_coefficient) = dimensions
                .iter()
                .enumerate()
                .filter(|(_, side)| **side == 1)
                .find_map(|(block, _)| {
                    let mut coefficients = Vec::new();
                    model.for_each_gram_entry_coefficient(block, 0, 0, |position, coefficient| {
                        coefficients.push((position, coefficient))
                    });
                    (coefficients.len() == 1 && coefficients[0].0 == cost_position)
                        .then_some((block, coefficients[0].1))
                })
                .expect("every running-cost coordinate has a one-dimensional SOS block");
            grams[block][0][0] = BigQsqrt2::from_small(cost_coefficient)
                .div(&BigQsqrt2::from_small(gram_coefficient))
                .unwrap()
                .to_string();
        }
        let multipliers = certificate
            .liouville_multipliers_by_cell
            .iter()
            .flatten()
            .map(|value| ScalarParser::parse(value).unwrap())
            .collect::<Vec<_>>();
        write_back(
            &mut certificate,
            &model,
            &multipliers,
            &BigQsqrt2::zero(),
            grams,
        );
        certificate.bound_target = "0".into();
        certificate
    }

    fn full_coordinate_faces(certificate: &SplitExactDualCertificate) -> Vec<SplitFaceBlock> {
        flattened_grams(certificate)
            .into_iter()
            .map(|coordinates| {
                let side = coordinates.len();
                let mut basis = vec![vec!["0".into(); side]; side];
                for (index, row) in basis.iter_mut().enumerate() {
                    row[index] = "1".into();
                }
                SplitFaceBlock {
                    basis,
                    coordinates: coordinates.clone(),
                }
            })
            .collect()
    }

    #[test]
    fn audits_a_split_certificate_identically_in_serial_and_parallel() {
        let certificate = weak_exact_certificate();
        let serial = audit_split_exact_certificate_with_jobs(&certificate, 1).unwrap();
        let parallel = audit_split_exact_certificate_with_jobs(&certificate, 2).unwrap();
        assert_eq!(serial, parallel);
        assert_eq!(serial.certified_bound, "0");
        assert_eq!(serial.nonzero_exact_residual_count, 0);
        assert!(serial.all_gram_matrices_exactly_positive_semidefinite);

        let mut target_tamper = certificate;
        target_tamper.bound_target = "1".into();
        assert!(matches!(
            audit_split_exact_certificate(&target_tamper),
            Err(SplitExactAuditError::Exact(ExactAuditError::Bound { .. }))
        ));
    }

    #[test]
    fn split_schema_rejects_metadata_and_family_tampering() {
        let certificate = structural_certificate();
        let mut tampered = certificate.clone();
        tampered.knots[1] = "2/4".into();
        assert!(matches!(
            validate_layout(&tampered),
            Err(SplitExactAuditError::NoncanonicalKnots)
        ));
        let mut tampered = certificate.clone();
        tampered.split_grid_hash.push('0');
        assert!(matches!(
            validate_layout(&tampered),
            Err(SplitExactAuditError::SplitGridHash { .. })
        ));
        let mut tampered = certificate.clone();
        tampered.formulation_hash.push('0');
        assert!(matches!(
            validate_layout(&tampered),
            Err(SplitExactAuditError::FormulationHash { .. })
        ));
        let mut tampered = certificate.clone();
        tampered.equality_order = "interface_major".into();
        assert!(matches!(
            validate_layout(&tampered),
            Err(SplitExactAuditError::EqualityOrder(_))
        ));
        let mut tampered = certificate.clone();
        tampered.gram_order = "unspecified".into();
        assert!(matches!(
            validate_layout(&tampered),
            Err(SplitExactAuditError::GramOrder(_))
        ));
        let mut tampered = certificate;
        tampered.interface_grams_by_knot[0].pop();
        assert!(matches!(
            validate_layout(&tampered),
            Err(SplitExactAuditError::GroupCount {
                family: "interface Gram",
                ..
            })
        ));
    }

    #[test]
    fn split_schema_checks_every_gram_family_before_identity() {
        let certificate = structural_certificate();
        for family in 0..3 {
            let mut tampered = certificate.clone();
            let matrix = match family {
                0 => &mut tampered.occupation_grams_by_cell[0][0],
                1 => &mut tampered.interface_grams_by_knot[0][0],
                _ => &mut tampered.terminal_grams_by_cell[0][0],
            };
            matrix[0][0] = "-1".into();
            assert!(matches!(
                audit_split_exact_certificate_with_jobs(&tampered, 1),
                Err(SplitExactAuditError::Exact(
                    ExactAuditError::GramPivot { .. }
                ))
            ));
        }
    }

    #[test]
    fn split_schema_checks_symmetry_and_equality_identity() {
        let certificate = structural_certificate();
        let mut tampered = certificate.clone();
        let matrix = &mut tampered.occupation_grams_by_cell[0][0];
        if matrix.len() > 1 {
            matrix[0][1] = "1".into();
            assert!(matches!(
                audit_split_exact_certificate(&tampered),
                Err(SplitExactAuditError::Exact(
                    ExactAuditError::GramSymmetry { .. }
                ))
            ));
        }
        let mut tampered = certificate;
        tampered.liouville_multipliers_by_cell[0][0] = "1".into();
        assert!(matches!(
            audit_split_exact_certificate(&tampered),
            Err(SplitExactAuditError::Exact(
                ExactAuditError::Identity { .. }
            ))
        ));
    }

    #[test]
    fn exact_ldl_accepts_rank_deficiency_but_rejects_zero_pivot_coupling() {
        let mut semidefinite = parse_matrix(
            0,
            &[vec!["1".into(), "0".into()], vec!["0".into(), "0".into()]],
            2,
        )
        .unwrap();
        assert_eq!(
            semidefinite_ldl_minimum(0, &mut semidefinite).unwrap(),
            (Some(BigQsqrt2::from_rational(BigRational::one())), false)
        );

        let mut indefinite = parse_matrix(
            0,
            &[vec!["0".into(), "1".into()], vec!["1".into(), "0".into()]],
            2,
        )
        .unwrap();
        assert!(matches!(
            semidefinite_ldl_minimum(0, &mut indefinite),
            Err(ExactAuditError::GramPivot { .. })
        ));

        let mut quadratic_indefinite = parse_matrix(
            0,
            &[
                vec!["0".into(), "sqrt(2)".into()],
                vec!["sqrt(2)".into(), "0".into()],
            ],
            2,
        )
        .unwrap();
        let error = semidefinite_ldl_minimum(0, &mut quadratic_indefinite).unwrap_err();
        assert!(matches!(&error, ExactAuditError::GramPivot { .. }));
        assert!(
            error
                .to_string()
                .contains("zero pivot with nonzero Schur coupling")
        );
    }

    #[test]
    fn fraction_free_ldl_matches_rational_fallback_across_zero_pivots() {
        let rational = parse_matrix(
            0,
            &[
                vec!["1/3".into(), "1/3".into()],
                vec!["1/3".into(), "1/3".into()],
            ],
            2,
        )
        .unwrap();
        let expected = match rational.clone() {
            ParsedGram::Rational(mut values) => {
                let (minimum, positive) = semidefinite_rational_ldl(0, &mut values).unwrap();
                (minimum.map(BigQsqrt2::from_rational), positive)
            }
            ParsedGram::Quadratic(_) => unreachable!(),
        };
        assert_eq!(
            fraction_free_semidefinite_ldl_minimum(0, &rational)
                .unwrap()
                .unwrap(),
            expected
        );

        let quadratic = parse_matrix(
            0,
            &[
                vec!["1".into(), "sqrt(2)".into(), "1".into()],
                vec!["sqrt(2)".into(), "2".into(), "sqrt(2)".into()],
                vec!["1".into(), "sqrt(2)".into(), "2".into()],
            ],
            3,
        )
        .unwrap();
        let expected = match quadratic.clone() {
            ParsedGram::Quadratic(mut values) => {
                semidefinite_quadratic_ldl(0, &mut values).unwrap()
            }
            ParsedGram::Rational(_) => unreachable!(),
        };
        assert_eq!(
            fraction_free_semidefinite_ldl_minimum(0, &quadratic)
                .unwrap()
                .unwrap(),
            expected
        );
    }

    #[test]
    fn residual_certificate_uses_tight_sqrt2_enclosure_and_zero_row_compression() {
        let quadratic = parse_matrix(0, &[vec!["3 - 2*sqrt(2)".into()]], 1).unwrap();
        let certificate = residual_gram_certificate(&quadratic)
            .expect("the tight sqrt(2) enclosure should certify cancellation");
        assert!(certificate.minimum_eigenvalue_lower_bound.is_positive());
        assert_eq!(certificate.removed_zero_rows, 0);

        let non_dyadic = parse_matrix(
            0,
            &[
                vec!["1/3".into(), "0".into()],
                vec!["0".into(), "2/3".into()],
            ],
            2,
        )
        .unwrap();
        assert!(residual_gram_certificate(&non_dyadic).is_some());

        let mut zero_row = parse_matrix(
            0,
            &[vec!["2".into(), "0".into()], vec!["0".into(), "0".into()]],
            2,
        )
        .unwrap();
        let SemidefiniteGramCertificate::Residual(certificate) =
            semidefinite_certificate(0, &mut zero_row).unwrap()
        else {
            panic!("the compressed positive block should use residual certification");
        };
        assert_eq!(certificate.removed_zero_rows, 1);
    }

    #[test]
    fn residual_certificate_falls_back_at_the_floating_boundary() {
        const TWO_POW_100: &str = "1267650600228229401496703205376";
        let matrix = |last: String| {
            parse_matrix(
                0,
                &[vec!["1".into(), "1".into()], vec!["1".into(), last]],
                2,
            )
            .unwrap()
        };

        let mut positive = matrix(format!("1 + 1/{TWO_POW_100}"));
        assert!(matches!(
            semidefinite_certificate(0, &mut positive).unwrap(),
            SemidefiniteGramCertificate::ExactLdl {
                positive_definite: true,
                ..
            }
        ));

        let mut singular = matrix("1".into());
        assert!(matches!(
            semidefinite_certificate(0, &mut singular).unwrap(),
            SemidefiniteGramCertificate::ExactLdl {
                positive_definite: false,
                ..
            }
        ));

        let mut tiny_indefinite = matrix(format!("1 - 1/{TWO_POW_100}"));
        assert!(matches!(
            semidefinite_certificate(0, &mut tiny_indefinite),
            Err(ExactAuditError::GramPivot { .. })
        ));

        let mut indefinite = matrix("-1".into());
        assert!(matches!(
            semidefinite_certificate(0, &mut indefinite),
            Err(ExactAuditError::GramPivot { .. })
        ));
    }

    #[test]
    fn finite_field_inverse_and_exact_repair_preserve_split_identity() {
        const PRIME: u64 = 2_147_483_629;
        let value = ModQsqrt2 {
            rational: 17,
            sqrt2: 23,
        };
        assert_eq!(
            value.mul(value.inverse(PRIME).unwrap(), PRIME),
            ModQsqrt2 {
                rational: 1,
                sqrt2: 0
            }
        );

        let mut certificate = weak_exact_certificate();
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let model = ExactSplitModel::create(certificate.order, &grid).unwrap();
        let equality = model
            .rows
            .iter()
            .position(|row| {
                let mut positions = BTreeMap::new();
                row.coefficients
                    .iter()
                    .any(|(position, _)| positions.insert(*position, ()).is_some())
            })
            .expect("the split operator has an equality with duplicate positions");
        let per_cell = model.equality_count_per_cell();
        certificate.liouville_multipliers_by_cell[equality / per_cell][equality % per_cell] =
            "1".into();
        let diagnostics = repair_split_exact_identity_componentwise(&mut certificate).unwrap();
        assert!(diagnostics.selected_exact_rank > 0);
        assert!(diagnostics.exact_component_count > 0);
        assert!(diagnostics.largest_exact_component <= diagnostics.selected_exact_rank);

        let multipliers = flattened_multipliers(&certificate).unwrap();
        let normalization = ScalarParser::parse(&certificate.normalization).unwrap();
        let grams = flattened_grams(&certificate);
        assert!(
            reconstructed_identity(
                &model,
                &multipliers,
                &normalization,
                &grams,
                &model.gram_dimensions(),
            )
            .unwrap()
            .iter()
            .all(BigQsqrt2::is_zero)
        );
        assert!(
            minimum_reconstructed_split_gram_eigenvalue(&certificate)
                .unwrap()
                .is_finite()
        );
    }

    #[test]
    fn componentwise_qr_order_avoids_an_ill_conditioned_exact_basis() {
        fn rational(numerator: i128, denominator: i128) -> crate::Qsqrt2 {
            crate::Qsqrt2::new(Rational::new(numerator, denominator), Rational::ZERO)
        }
        fn column(entries: &[(usize, crate::Qsqrt2)]) -> RepairColumn {
            RepairColumn {
                variable: RepairVariable::Normalization,
                coefficients: entries.iter().copied().collect(),
            }
        }

        let columns = vec![
            column(&[(0, rational(10, 1)), (1, rational(10, 1))]),
            column(&[(0, rational(10, 1)), (1, rational(10_000_001, 1_000_000))]),
            column(&[(1, rational(9, 1))]),
        ];
        let legacy = select_modular_column_basis_in_order(2, &columns, &[0, 1, 2]).unwrap();
        let stable = select_stable_modular_column_basis(2, &columns).unwrap();
        assert_eq!(
            legacy
                .iter()
                .map(|&(_, candidate)| candidate)
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
        assert!(stable.iter().any(|&(_, candidate)| candidate == 2));

        let residual = vec![BigQsqrt2::zero(), BigQsqrt2::from_small(1.into())];
        let legacy_correction = solve_exact_components(&legacy, &columns, &residual)
            .unwrap()
            .corrections;
        let stable_correction = solve_exact_components(&stable, &columns, &residual)
            .unwrap()
            .corrections;
        let maximum = |corrections: &[(usize, BigQsqrt2)]| {
            corrections
                .iter()
                .map(|(_, value)| finite(value, "test correction").unwrap().abs())
                .fold(0.0, f64::max)
        };
        assert!(maximum(&legacy_correction) > 100_000.0);
        assert!(maximum(&stable_correction) < 1.0);
    }

    #[test]
    fn restricted_cone_repair_problem_preserves_zero_correction_semantics() {
        let mut certificate = weak_exact_certificate();
        let (problem, plan, diagnostics) =
            build_split_cone_repair_problem(&certificate, 1e-7, 1e-4).unwrap();
        problem.validate().unwrap();
        assert!(diagnostics.active_gram_count > 0);
        assert_eq!(
            diagnostics.constrained_gram_count + diagnostics.fixed_gram_count,
            diagnostics.active_gram_count
        );
        assert_eq!(
            problem
                .cones
                .iter()
                .filter(|cone| matches!(cone, Cone::PsdTriangle(_)))
                .count(),
            diagnostics.constrained_gram_count
        );
        assert!(
            diagnostics.restricted_gram_coordinate_count
                <= diagnostics.full_active_gram_coordinate_count
        );
        assert_eq!(
            diagnostics.restricted_gram_coordinate_count,
            diagnostics.signature_basis_coordinate_count
                + diagnostics.expanded_neighbor_coordinate_count
        );
        assert_eq!(problem.q.len(), diagnostics.correction_variable_count + 1);
        assert!((diagnostics.gram_constraint_scale - 1e3).abs() < 1e-9);
        assert_eq!(diagnostics.margin_variable_scale, 1e-4);
        let zero = vec!["0".to_string(); problem.q.len()];
        assert_eq!(
            apply_split_cone_repair(&mut certificate, &plan, &zero).unwrap(),
            0.0
        );
        audit_split_exact_certificate(&certificate).unwrap();
    }

    #[test]
    fn cone_repair_omits_only_fixed_nonnegative_blocks() {
        let active = vec![true, true, false, true];
        let repaired_margin = vec![false, false, false, true];
        let variable_blocks = HashSet::from([0]);
        assert_eq!(
            cone_constrained_gram_blocks(&active, &repaired_margin, &variable_blocks),
            vec![true, false, false, true]
        );
    }

    #[test]
    fn restricted_bar_repair_freezes_unselected_gram_blocks() {
        let certificate = weak_exact_certificate();
        let layout = validate_layout(&certificate).unwrap();
        let grams = flattened_grams(&certificate);
        let parsed = parse_gram_refs(&grams, &layout.dimensions).unwrap();
        let selected = active_parsed_gram_blocks(&parsed)
            .iter()
            .position(|&active| active)
            .unwrap();
        let (_, _, full) =
            build_split_bar_cone_repair_problem_scaled(&certificate, 1e-7, 1e-4, 1e-3).unwrap();
        let (problem, _, restricted) = build_split_bar_cone_repair_problem_scaled_restricted(
            &certificate,
            1e-7,
            1e-4,
            1e-3,
            &[selected],
        )
        .unwrap();
        problem.validate().unwrap();
        assert!(restricted.repair_gram_count <= full.repair_gram_count);
        assert!(restricted.constrained_gram_count <= full.constrained_gram_count);
        assert_eq!(
            restricted.constrained_gram_count + restricted.fixed_gram_count,
            restricted.active_gram_count
        );
    }

    #[test]
    fn bar_cone_repair_uses_only_zero_and_psd_cones() {
        let mut certificate = weak_exact_certificate();
        let (problem, plan, diagnostics) =
            build_split_bar_cone_repair_problem(&certificate, 1e-7, 1e-4).unwrap();
        problem.validate().unwrap();
        assert!(!diagnostics.correction_bounds_enforced);
        assert_eq!(diagnostics.fixed_common_margin, Some(1e-7));
        let serialized_diagnostics = serde_json::to_value(&diagnostics).unwrap();
        assert!(
            serialized_diagnostics
                .get("rotated_kernel_gram_count")
                .is_none()
        );
        assert!(
            serialized_diagnostics
                .get("rotated_kernel_equation_count")
                .is_none()
        );
        assert!(problem.q.iter().all(|&coefficient| coefficient == 0.0));
        assert!(matches!(problem.cones.last(), Some(Cone::Zero(1))));
        assert!(
            problem
                .cones
                .iter()
                .all(|cone| matches!(cone, Cone::Zero(_) | Cone::PsdTriangle(_)))
        );
        let mut zero = vec!["0".to_string(); problem.q.len()];
        zero[plan.margin_variable] = "1/1000".into();
        let applied_margin = apply_split_cone_repair(&mut certificate, &plan, &zero).unwrap();
        assert!((applied_margin - 1e-7).abs() < 1e-20);
        audit_split_exact_certificate(&certificate).unwrap();

        let (_, _, scaled_diagnostics) =
            build_split_bar_cone_repair_problem_scaled(&certificate, 1e-7, 1e-4, 1e-3).unwrap();
        assert!((scaled_diagnostics.gram_constraint_scale - 1e4).abs() < 1e-8);
    }

    #[test]
    fn cone_repair_does_not_reopen_an_exact_zero_gram_row() {
        let mut certificate = weak_exact_certificate();
        let matrix = &mut certificate.occupation_grams_by_cell[0][0];
        assert!(matrix.len() > 1);
        for entry in &mut matrix[0] {
            *entry = "0".into();
        }
        for matrix_row in matrix {
            matrix_row[0] = "0".into();
        }
        let (_, plan, _) = build_split_cone_repair_problem(&certificate, 1e-7, 1e-4).unwrap();
        assert!(!plan.variables.iter().any(|variable| matches!(
            variable,
            RepairVariable::Gram {
                block: 0,
                row: 0,
                ..
            } | RepairVariable::Gram {
                block: 0,
                column: 0,
                ..
            }
        )));
    }

    #[test]
    fn restricted_cone_repair_classifies_materially_negative_block() {
        let mut certificate = weak_exact_certificate();
        let matrix = certificate
            .occupation_grams_by_cell
            .last_mut()
            .expect("weak certificate has occupation cells")
            .iter_mut()
            .find(|matrix| matrix.len() > 1)
            .expect("weak certificate has a nonscalar occupation Gram");
        matrix[0][0] = "-1/1048576".into();
        let (_, _, diagnostics) =
            build_split_cone_repair_problem(&certificate, 1e-7, 1e-4).unwrap();
        assert!(diagnostics.vulnerable_gram_count > 0);
        assert!(diagnostics.repaired_margin_gram_count > 0);
        assert!(diagnostics.vulnerable_coefficient_count > 0);
        assert_eq!(
            diagnostics.restricted_gram_coordinate_count,
            diagnostics.signature_basis_coordinate_count
                + diagnostics.expanded_neighbor_coordinate_count
        );
    }

    #[test]
    fn facial_reduction_zeros_small_gram_rows() {
        let mut certificate = weak_exact_certificate();
        let matrix = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .find(|matrix| {
                matrix.len() == 1
                    && ScalarParser::parse(&matrix[0][0]).is_ok_and(|value| !value.is_zero())
            })
            .expect("weak certificate has an active scalar occupation Gram");
        matrix[0][0] = "-19/2251799813685248".into();
        assert_eq!(
            zero_small_split_gram_rows(&mut certificate, 1e-7).unwrap(),
            1
        );
        assert!(
            certificate
                .occupation_grams_by_cell
                .iter()
                .flatten()
                .filter(|matrix| matrix.len() == 1)
                .any(|matrix| matrix[0][0] == "0")
        );
    }

    #[test]
    fn facial_reduction_zeros_a_small_diagonal_row_in_a_larger_gram() {
        let mut certificate = weak_exact_certificate();
        let matrix = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .find(|matrix| matrix.len() > 1)
            .expect("weak certificate has a non-scalar occupation Gram");
        matrix[0][0] = "-237/4503599627370496".into();
        matrix[0][1] = "1/1024".into();
        matrix[1][0] = "1/1024".into();
        assert_eq!(
            zero_small_split_gram_rows(&mut certificate, 1e-7).unwrap(),
            1
        );
        let matrix = &certificate.occupation_grams_by_cell[0][0];
        assert!(matrix[0].iter().all(|value| value == "0"));
        assert!(matrix.iter().all(|row| row[0] == "0"));
    }

    #[test]
    fn face_parameterized_zero_correction_preserves_exact_psd_coordinates() {
        let mut certificate = weak_exact_certificate();
        certificate.liouville_multipliers_by_cell[0][0] = "1".into();
        let faces = full_coordinate_faces(&certificate);
        let mut stopped_certificate = certificate.clone();

        let zero_report =
            repair_split_exact_identity_on_faces(&mut certificate, &faces, 30, true, None).unwrap();
        assert!(zero_report.identity_span < zero_report.coefficient_count);
        assert!(zero_report.identity_span_scan_complete);
        assert!(zero_report.nonzero_exact_residual_count_after_repair > 0);
        assert!(zero_report.coordinate_matrices_exactly_positive_semidefinite);

        let stopped_report = repair_split_exact_identity_on_faces(
            &mut stopped_certificate,
            &faces,
            30,
            true,
            Some(1),
        )
        .unwrap();
        assert_eq!(stopped_report.identity_span, 1);
        assert!(!stopped_report.identity_span_scan_complete);
    }

    #[test]
    fn rank_deficient_exact_face_reconstruction_is_ldl_positive_semidefinite() {
        let exact =
            |value: i64| BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(value)));
        let face = ParsedFaceBlock {
            basis: vec![
                vec![exact(1), exact(0)],
                vec![exact(1), exact(1)],
                vec![exact(0), exact(1)],
            ],
            coordinates: vec![vec![exact(2), exact(1)], vec![exact(1), exact(2)]],
        };
        let reconstructed = reconstruct_face_gram(&face)
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|value| ScalarParser::parse(&value).unwrap())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut exact = ParsedGram::Quadratic(reconstructed);
        let (minimum, positive_definite) = semidefinite_ldl_minimum(0, &mut exact).unwrap();
        assert!(minimum.is_some());
        assert!(!positive_definite);
    }

    #[test]
    fn rotated_face_reconstructs_exactly_as_f_h_f_transpose() {
        let exact =
            |value: i64| BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(value)));
        let face = ParsedFaceBlock {
            basis: vec![
                vec![exact(1), exact(0)],
                vec![exact(1), exact(1)],
                vec![exact(0), exact(1)],
            ],
            coordinates: vec![vec![exact(2), exact(1)], vec![exact(1), exact(3)]],
        };
        assert_eq!(
            reconstruct_face_gram(&face),
            vec![
                vec![String::from("2"), String::from("3"), String::from("1")],
                vec![String::from("3"), String::from("7"), String::from("4")],
                vec![String::from("1"), String::from("4"), String::from("3")],
            ]
        );
    }

    #[test]
    fn rotated_face_coordinate_preserves_split_identity_coefficients() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let model = ExactSplitModel::create(2, &grid).unwrap();
        let dimensions = model.gram_dimensions();
        let block = dimensions
            .iter()
            .position(|&dimension| dimension >= 2)
            .expect("test model has a nonscalar Gram");
        let dimension = dimensions[block];
        let exact =
            |value: i64| BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(value)));
        let mut basis = vec![vec![exact(0); 2]; dimension];
        basis[0] = vec![exact(1), exact(1)];
        basis[1] = vec![exact(1), exact(-1)];
        let zero_face = ParsedFaceBlock {
            basis: basis.clone(),
            coordinates: vec![vec![exact(0); 2]; 2],
        };
        let changed_face = ParsedFaceBlock {
            basis: basis.clone(),
            coordinates: vec![vec![exact(0), exact(1)], vec![exact(1), exact(0)]],
        };
        let mut zero_grams = dimensions
            .iter()
            .map(|&side| zero_matrix(side))
            .collect::<Vec<_>>();
        zero_grams[block] = reconstruct_face_gram(&zero_face);
        let zero_refs = zero_grams.iter().collect::<Vec<_>>();
        let multipliers = vec![BigQsqrt2::zero(); model.rows.len()];
        let before = reconstructed_identity(
            &model,
            &multipliers,
            &BigQsqrt2::zero(),
            &zero_refs,
            &dimensions,
        )
        .unwrap();
        zero_grams[block] = reconstruct_face_gram(&changed_face);
        let changed_refs = zero_grams.iter().collect::<Vec<_>>();
        let after = reconstructed_identity(
            &model,
            &multipliers,
            &BigQsqrt2::zero(),
            &changed_refs,
            &dimensions,
        )
        .unwrap();
        let transformed_column = face_coordinate_column(&model, block, &basis, 0, 1);
        for position in 0..model.coefficient_count() {
            let expected = transformed_column
                .get(&position)
                .cloned()
                .unwrap_or_else(BigQsqrt2::zero);
            assert_eq!(after[position].sub(&before[position]), expected);
        }
    }

    #[test]
    fn exact_psd_inner_coordinates_imply_exact_psd_reconstructed_gram() {
        let exact =
            |value: i64| BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(value)));
        let face = ParsedFaceBlock {
            basis: vec![
                vec![exact(1), exact(0)],
                vec![exact(1), exact(1)],
                vec![exact(0), exact(1)],
            ],
            coordinates: vec![vec![exact(2), exact(1)], vec![exact(1), exact(2)]],
        };
        let mut inner = ParsedGram::Quadratic(face.coordinates.clone());
        let (inner_minimum, inner_positive_definite) =
            semidefinite_ldl_minimum(0, &mut inner).unwrap();
        assert!(inner_minimum.is_some());
        assert!(inner_positive_definite);

        let reconstructed = reconstruct_face_gram(&face)
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|value| ScalarParser::parse(&value).unwrap())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut reconstructed = ParsedGram::Quadratic(reconstructed);
        let (minimum, positive_definite) = semidefinite_ldl_minimum(0, &mut reconstructed).unwrap();
        assert!(minimum.is_some());
        assert!(!positive_definite);
    }

    #[test]
    fn exact_rotated_kernel_projector_annihilates_kernel_and_is_psd() {
        let kernel = vec![vec![BigRational::one()], vec![BigRational::one()]];
        let projector = exact_kernel_projector(&kernel).unwrap();
        assert_eq!(
            projector,
            vec![
                vec![
                    BigRational::new(BigInt::from(1), BigInt::from(2)),
                    BigRational::new(BigInt::from(-1), BigInt::from(2))
                ],
                vec![
                    BigRational::new(BigInt::from(-1), BigInt::from(2)),
                    BigRational::new(BigInt::from(1), BigInt::from(2))
                ],
            ]
        );
        for row in &projector {
            assert!(
                (0..2)
                    .map(|column| &row[column] * &kernel[column][0])
                    .sum::<BigRational>()
                    .is_zero()
            );
        }
        for row in 0..2 {
            for column in 0..2 {
                assert_eq!(
                    (0..2)
                        .map(|inner| &projector[row][inner] * &projector[inner][column])
                        .sum::<BigRational>(),
                    projector[row][column]
                );
            }
        }
        let mut gram = ParsedGram::Rational(
            projector
                .iter()
                .map(|row| row.iter().map(|value| value * BigInt::from(2)).collect())
                .collect(),
        );
        let (minimum, positive_definite) = semidefinite_ldl_minimum(0, &mut gram).unwrap();
        assert!(minimum.is_some());
        assert!(!positive_definite);
    }

    #[test]
    fn native_bar_face_plan_uses_exact_range_projectors() {
        let mut certificate = structural_certificate();
        let (block, matrix) = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find(|(_, matrix)| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![vec!["2".into(), "0".into()], vec!["0".into(), "3".into()]];
        let states = vec![SplitRotatedKernelState {
            block,
            kernel: vec![vec!["1".into()], vec!["1".into()]],
        }];
        let plan = build_split_native_bar_face_plan(&certificate, &states).unwrap();
        let face = plan
            .blocks
            .iter()
            .find(|face| face.block == block)
            .expect("selected block has a direct native-bar face");
        assert!(face.rotated);
        assert_eq!(face.kernel_rank, 1);
        for row in 0..2 {
            assert!((face.range_projector[row][0] + face.range_projector[row][1]).abs() < 1e-15);
        }
        let q = nalgebra::DMatrix::identity(2, 2)
            - nalgebra::DMatrix::from_fn(2, 2, |row, column| face.range_projector[row][column]);
        assert!(q.symmetric_eigen().eigenvalues.min() >= -1e-15);
    }

    #[test]
    fn graph_face_projection_closes_the_exact_kernel_and_stays_psd() {
        let mut certificate = structural_certificate();
        let (block, matrix) = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find(|(_, matrix)| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![vec!["2".into(), "0".into()], vec!["0".into(), "3".into()]];
        let states = vec![SplitRotatedKernelState {
            block,
            kernel: vec![vec!["1".into()], vec!["1".into()]],
        }];
        project_split_grams_to_rotated_kernels(&mut certificate, &states).unwrap();
        assert_eq!(
            flattened_grams(&certificate)[block],
            &vec![
                vec![String::from("3"), String::from("-3")],
                vec![String::from("-3"), String::from("3")],
            ]
        );
        check_split_exact_kernel_closure(&certificate, &states).unwrap();
        let layout = validate_layout(&certificate).unwrap();
        let grams = flattened_grams(&certificate);
        let mut parsed = parse_matrix(block, grams[block], layout.dimensions[block]).unwrap();
        let (minimum, positive_definite) = semidefinite_ldl_minimum(block, &mut parsed).unwrap();
        assert!(minimum.is_some());
        assert!(!positive_definite);
    }

    #[test]
    fn rotated_face_closure_uses_only_unselected_gram_signatures() {
        let mut certificate = weak_exact_certificate();
        let layout = validate_layout(&certificate).unwrap();
        let block = layout
            .dimensions
            .iter()
            .position(|&dimension| dimension == 2)
            .expect("test certificate has a two-dimensional Gram");
        let states = vec![SplitRotatedKernelState {
            block,
            kernel: vec![vec!["1".into()], vec!["1".into()]],
        }];
        project_split_grams_to_rotated_kernels(&mut certificate, &states).unwrap();
        let frozen = flattened_grams(&certificate)[block].clone();
        let unselected = (0..layout.dimensions.len())
            .filter(|&candidate| candidate != block)
            .collect::<Vec<_>>();
        let diagnostics =
            repair_split_exact_identity_restricted(&mut certificate, &unselected).unwrap();
        assert!(diagnostics.selected_gram_variable_count > 0);
        assert_eq!(flattened_grams(&certificate)[block], &frozen);
        check_split_exact_affine_closure(&certificate).unwrap();
        check_split_exact_kernel_closure(&certificate, &states).unwrap();
        audit_split_exact_certificate(&certificate).unwrap();
    }

    #[test]
    fn kernel_rows_preserve_the_exact_split_identity_operator() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let model = ExactSplitModel::create(2, &grid).unwrap();
        let dimensions = model.gram_dimensions();
        let block = dimensions
            .iter()
            .position(|&dimension| dimension >= 2)
            .expect("test model has a nonscalar Gram");
        let dimension = dimensions[block];
        let small_kernel = (0..dimension)
            .map(|row| {
                vec![crate::Qsqrt2::new(
                    if row < 2 {
                        Rational::ONE
                    } else {
                        Rational::ZERO
                    },
                    Rational::ZERO,
                )]
            })
            .collect::<Vec<_>>();
        let kernel = small_kernel
            .iter()
            .map(|row| {
                row.iter()
                    .map(|value| {
                        BigRational::new(
                            BigInt::from(value.rational.numerator),
                            BigInt::from(value.rational.denominator),
                        )
                    })
                    .collect()
            })
            .collect::<Vec<_>>();
        let state = ParsedRotatedKernelState {
            block,
            projector: exact_kernel_projector(&kernel).unwrap(),
            kernel,
            small_kernel,
        };
        let mut active = vec![false; dimensions.len()];
        active[block] = true;
        let active_rows = dimensions
            .iter()
            .map(|&side| vec![true; side])
            .collect::<Vec<_>>();
        let (mut columns, _) =
            all_gram_repair_columns(&model, &dimensions, &active, Some(&active_rows));
        augment_gram_columns_with_kernel_equalities(
            &mut columns,
            std::slice::from_ref(&state),
            &dimensions,
            &active_rows,
            model.coefficient_count(),
        );
        let column = columns
            .iter()
            .find(|column| {
                matches!(
                    column.variable,
                    RepairVariable::Gram {
                        block: selected,
                        row: 0,
                        column: 1,
                    } if selected == block
                )
            })
            .expect("kernel augmentation retains the off-diagonal coordinate");

        let mut zero_grams = dimensions
            .iter()
            .map(|&side| zero_matrix(side))
            .collect::<Vec<_>>();
        let zero_refs = zero_grams.iter().collect::<Vec<_>>();
        let multipliers = vec![BigQsqrt2::zero(); model.rows.len()];
        let before = reconstructed_identity(
            &model,
            &multipliers,
            &BigQsqrt2::zero(),
            &zero_refs,
            &dimensions,
        )
        .unwrap();
        zero_grams[block][0][1] = "1".into();
        zero_grams[block][1][0] = "1".into();
        let changed_refs = zero_grams.iter().collect::<Vec<_>>();
        let after = reconstructed_identity(
            &model,
            &multipliers,
            &BigQsqrt2::zero(),
            &changed_refs,
            &dimensions,
        )
        .unwrap();
        for position in 0..model.coefficient_count() {
            assert_eq!(
                after[position].sub(&before[position]),
                column
                    .coefficients
                    .get(&position)
                    .copied()
                    .map(BigQsqrt2::from_small)
                    .unwrap_or_else(BigQsqrt2::zero)
            );
        }
        let parsed = parse_gram_refs(&changed_refs, &dimensions).unwrap();
        let residuals = exact_kernel_residuals(&parsed, &[state], &dimensions);
        for (row, residual) in residuals.iter().enumerate() {
            assert_eq!(
                residual,
                &column
                    .coefficients
                    .get(&(model.coefficient_count() + row))
                    .copied()
                    .map(BigQsqrt2::from_small)
                    .unwrap_or_else(BigQsqrt2::zero)
            );
        }
    }

    #[test]
    fn rotated_kernel_selection_handles_no_rotation_and_all_zero_edges() {
        let zero = structural_certificate();
        let (states, report) = select_split_rotated_gram_kernels(&zero, 0.5, 0.01, 20).unwrap();
        assert!(states.is_empty());
        assert_eq!(report.active_gram_count, 0);

        let mut interior = structural_certificate();
        let matrix = interior
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(interior.interface_grams_by_knot.iter_mut().flatten())
            .chain(interior.terminal_grams_by_cell.iter_mut().flatten())
            .find(|matrix| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![vec!["1".into(), "0".into()], vec!["0".into(), "1".into()]];
        let (states, report) = select_split_rotated_gram_kernels(&interior, 0.5, 0.01, 20).unwrap();
        assert!(states.is_empty());
        assert_eq!(report.active_gram_count, 1);
        assert_eq!(report.rotated_kernel_gram_count, 0);

        let matrix = interior
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(interior.interface_grams_by_knot.iter_mut().flatten())
            .chain(interior.terminal_grams_by_cell.iter_mut().flatten())
            .find(|matrix| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![vec!["1".into(), "1".into()], vec!["1".into(), "1".into()]];
        let (states, report) = select_split_rotated_gram_kernels(&interior, 0.5, 0.01, 20).unwrap();
        assert!(states.is_empty());
        assert_eq!(report.active_gram_count, 1);
        assert_eq!(report.rotated_kernel_gram_count, 0);
    }

    #[test]
    fn rotated_kernel_selection_captures_a_non_axis_aligned_null_mode() {
        let mut certificate = structural_certificate();
        let (block, matrix) = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find(|(_, matrix)| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![
            vec!["1".into(), "1000001/1000000".into()],
            vec!["1000001/1000000".into(), "1".into()],
        ];
        let (states, report) =
            select_split_rotated_gram_kernels(&certificate, 0.5, 0.01, 20).unwrap();
        assert_eq!(states.len(), 1);
        assert_eq!(states[0].block, block);
        assert_eq!(states[0].kernel.len(), 2);
        assert_eq!(states[0].kernel[0].len(), 1);
        assert_eq!(report.rotated_kernel_gram_count, 1);
        assert_eq!(report.spectral_kernel_direction_count, 1);
        assert_eq!(report.non_axis_aligned_kernel_direction_count, 1);
        validate_split_rotated_gram_kernels(&certificate, &states).unwrap();
    }

    #[test]
    fn kernel_cone_model_adds_sparse_equalities_and_range_projector_margin() {
        let mut certificate = structural_certificate();
        let (block, matrix) = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find(|(_, matrix)| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![
            vec!["1".into(), "1000001/1000000".into()],
            vec!["1000001/1000000".into(), "1".into()],
        ];
        let (states, _) = select_split_rotated_gram_kernels(&certificate, 0.5, 0.01, 20).unwrap();
        let (problem, plan, diagnostics) =
            build_split_kernel_bar_cone_repair_problem_scaled_restricted(
                &certificate,
                &states,
                0.01,
                1.0,
                0.01,
                &[block],
            )
            .unwrap();
        problem.validate().unwrap();
        let zero_rows = match problem.cones[0] {
            Cone::Zero(rows) => rows,
            _ => panic!("kernel cone model must begin with exact linear rows"),
        };
        let coefficient_count = ExactSplitModel::create(
            certificate.order,
            &certificate.knots.join(",").parse::<SplitGrid>().unwrap(),
        )
        .unwrap()
        .coefficient_count();
        assert_eq!(zero_rows, coefficient_count + 1 + 2);
        assert_eq!(diagnostics.repair_gram_count, 1);
        assert!(problem.a.entries.iter().any(|&(row, _, value)| {
            row > coefficient_count && row < zero_rows && value != 0.0
        }));
        let off_diagonal_psd_row = zero_rows + 1;
        assert!(problem.a.entries.iter().any(|&(row, column, value)| {
            row == off_diagonal_psd_row && column == plan.margin_variable && value != 0.0
        }));
    }

    #[test]
    fn rotated_face_selection_keeps_a_block_with_no_subthreshold_direction() {
        let mut certificate = structural_certificate();
        let (block, dimension) = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find_map(|(block, matrix)| {
                (matrix.len() >= 2).then(|| {
                    for (index, row) in matrix.iter_mut().enumerate() {
                        row[index] = "1".into();
                    }
                    (block, matrix.len())
                })
            })
            .expect("test certificate has a nonscalar Gram");
        let (faces, states, report) =
            select_split_rotated_gram_faces(&mut certificate, 0.5, 20).unwrap();
        assert_eq!(faces[block].coordinates.len(), dimension);
        assert!(face_is_coordinate_selector(&faces[block]));
        assert!(states.is_empty());
        assert_eq!(report.active_gram_count, 1);
        assert_eq!(report.unchanged_full_face_block_count, 1);
        assert_eq!(report.rotated_reduced_block_count, 0);
    }

    #[test]
    fn rotated_face_selection_reduces_and_restores_a_non_axis_aligned_face() {
        let mut certificate = structural_certificate();
        let block = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find_map(|(block, matrix)| {
                (matrix.len() == 2).then(|| {
                    *matrix = vec![vec!["1".into(), "1".into()], vec!["1".into(), "1".into()]];
                    block
                })
            })
            .expect("test certificate has a two-dimensional Gram");
        let (faces, states, report) =
            select_split_rotated_gram_faces(&mut certificate, 0.5, 20).unwrap();
        assert_eq!(faces[block].coordinates, vec![vec![String::from("3/2")]]);
        assert!(!face_is_coordinate_selector(&faces[block]));
        assert_eq!(states.len(), 1);
        assert_eq!(states[0].block, block);
        assert_eq!(report.rotated_reduced_block_count, 1);
        assert_eq!(report.retained_direction_count, 1);
        assert_eq!(
            restore_split_rotated_gram_faces(&certificate, &states).unwrap()[block].basis,
            faces[block].basis
        );
    }

    #[test]
    fn rotated_face_selection_handles_an_all_zero_certificate() {
        let mut certificate = structural_certificate();
        let block_count = flattened_grams(&certificate).len();
        let (faces, states, report) =
            select_split_rotated_gram_faces(&mut certificate, 1e-6, 20).unwrap();
        assert_eq!(faces.len(), block_count);
        assert!(faces.iter().all(|face| face.coordinates.is_empty()));
        assert!(states.is_empty());
        assert_eq!(report.active_gram_count, 0);
        assert_eq!(report.zero_face_block_count, block_count);
        assert!(
            flattened_grams(&certificate)
                .iter()
                .all(|matrix| matrix.iter().flatten().all(|value| value == "0"))
        );
    }

    #[test]
    fn face_numerical_repair_uses_the_wide_system_minimum_norm_solution() {
        let exact =
            |value: i64| BigQsqrt2::from_rational(BigRational::from_integer(BigInt::from(value)));
        let identity = vec![exact(-1), exact(-2)];
        let columns = vec![
            BTreeMap::from([(0, exact(1))]),
            BTreeMap::from([(1, exact(1))]),
            BTreeMap::from([(0, exact(1)), (1, exact(1))]),
        ];

        let correction = numerical_minimum_norm_correction(&identity, &columns, &[0, 1]).unwrap();
        assert!(correction.relative_residual < 1e-12);
        for (actual, expected) in correction.values.iter().zip([0.0, 1.0, 1.0]) {
            assert!((actual - expected).abs() < 1e-12);
        }
    }

    #[test]
    fn restricted_repair_rejects_invalid_gram_scopes() {
        let mut certificate = weak_exact_certificate();
        assert!(matches!(
            repair_split_exact_identity_restricted(&mut certificate, &[]),
            Err(SplitExactAuditError::Repair(_))
        ));
        assert!(matches!(
            repair_split_exact_identity_restricted(&mut certificate, &[0, 0]),
            Err(SplitExactAuditError::Repair(_))
        ));
        assert!(matches!(
            repair_split_exact_identity_restricted(&mut certificate, &[usize::MAX]),
            Err(SplitExactAuditError::Repair(_))
        ));
    }
}
