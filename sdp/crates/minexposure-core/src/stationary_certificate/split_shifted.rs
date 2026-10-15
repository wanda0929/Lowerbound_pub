use super::shifted::{
    ShiftedExactAuditError, ShiftedSalvageReason, ShiftedZeroCostCoordinate, add_diagonal_shift,
    exact_psd_result, exact_rational, exact_rational_gram_shift, floating_minimum_eigenvalue,
};
use super::split::{
    SplitExactAuditError, SplitExactDualCertificate, ValidatedLayout, flattened_grams,
    reconstructed_identity, validate_layout,
};
use super::{BigQsqrt2, ExactAuditError, ScalarParser, parse_matrix};
use crate::Rational;
use crate::stationary_hausdorff::{
    CostMonomial, ExactGramShiftMetadata, HausdorffGramFamily, HausdorffLocalizer,
    exact_certificate_model, interface_gram_bases, reflection_phase_is_i,
};
use crate::stationary_hausdorff_split::{ExactSplitModel, SplitGrid, structure};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const SPLIT_SHIFTED_EXACT_SCHEMA_V1: &str =
    "minexposure/jan22-cost-lifted-split-shifted-exact-dual-q-v1";
pub const SPLIT_SHIFTED_SALVAGE_FAILURE_SCHEMA_V1: &str =
    "minexposure/jan22-cost-lifted-split-shifted-salvage-failure-v1";
pub const SPLIT_SHIFTED_SALVAGE_ERROR_SCHEMA_V1: &str =
    "minexposure/jan22-cost-lifted-split-shifted-salvage-error-v1";
const SPLIT_SHIFTED_BLOCK_ORDER_V1: &str =
    "occupation_by_cell_then_interface_by_knot_then_terminal_pair_by_cell_v1";
const SPLIT_SHIFTED_TRANSFORM_ORIENTATION_V1: &str =
    "gram_coordinate_i=sum_j(transform_rows[i][j].coefficient*basis_phases[j]*basis[j])";

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SplitShiftedGramFamily {
    OccupationMoment,
    OccupationXiOneMinusXi,
    OccupationIntervalDiagonal,
    InterfaceMoment,
    TerminalMoment,
    TerminalXiOneMinusXi,
}

impl From<HausdorffGramFamily> for SplitShiftedGramFamily {
    fn from(value: HausdorffGramFamily) -> Self {
        match value {
            HausdorffGramFamily::OccupationMoment => Self::OccupationMoment,
            HausdorffGramFamily::OccupationXiOneMinusXi => Self::OccupationXiOneMinusXi,
            HausdorffGramFamily::OccupationIntervalDiagonal => Self::OccupationIntervalDiagonal,
            HausdorffGramFamily::TerminalMoment => Self::TerminalMoment,
            HausdorffGramFamily::TerminalXiOneMinusXi => Self::TerminalXiOneMinusXi,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "measure", rename_all = "snake_case")]
pub enum SplitShiftedBlockOwner {
    OccupationCell {
        cell_index: usize,
    },
    InterfaceKnot {
        interface_index: usize,
        knot_index: usize,
        knot: String,
    },
    TerminalCell {
        cell_index: usize,
    },
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SplitShiftedBasisBound {
    RydbergCostRelativeOccupationMonomials,
    UnitStateInterfaceMonomials,
    UnitIntervalTerminalMonomials,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SplitShiftedBasisPhase {
    One,
    I,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "basis_kind", rename_all = "snake_case")]
pub enum SplitShiftedBasisElement {
    StateCostMonomial { monomial: CostMonomial },
    LocalCostPower { power: usize },
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SplitShiftedTransformEntry {
    pub basis_index: usize,
    pub coefficient: i64,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SplitShiftedBoundKind {
    OccupationCostRelative,
    InterfaceAdditive,
    TerminalAdditive,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SplitShiftedBlockDerivation {
    pub block_index: usize,
    pub order: u8,
    pub family: SplitShiftedGramFamily,
    pub owner: SplitShiftedBlockOwner,
    pub owner_block_index: usize,
    pub gram_side: usize,
    pub basis_bound: SplitShiftedBasisBound,
    pub basis: Vec<SplitShiftedBasisElement>,
    pub basis_phases: Vec<SplitShiftedBasisPhase>,
    pub transform_orientation: String,
    pub transform_rows: Vec<Vec<SplitShiftedTransformEntry>>,
    pub localizer: HausdorffLocalizer,
    pub localizer_supremum: String,
    /// Per basis coordinate: `|z_i|^2 <= value*c` for occupation and
    /// `|z_i|^2 <= value` for finite-mass interface/terminal measures.
    pub basis_squared_bounds: Vec<Option<String>>,
    pub coordinate_bounds: Vec<Option<String>>,
    pub bound_kind: SplitShiftedBoundKind,
    /// Trace coefficient relative to cell cost or the owning finite mass.
    pub safe_block_bound: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SplitShiftedGramBlock {
    pub derivation: SplitShiftedBlockDerivation,
    /// Exactly zero for an originally PSD block and positive for a failing block.
    pub delta: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SplitShiftedExactDualCertificate {
    pub schema: String,
    pub block_order: String,
    pub split_grid_hash: String,
    pub formulation_hash: String,
    pub original: SplitExactDualCertificate,
    pub beta: String,
    pub blocks: Vec<SplitShiftedGramBlock>,
    pub occupation_cost_multipliers_by_cell: Vec<String>,
    pub total_occupation_cost_multiplier: String,
    pub interface_additive_discount: String,
    pub terminal_additive_discounts_by_cell: Vec<String>,
    pub terminal_additive_discount: String,
    pub finite_mass_correction: String,
    pub discounted_bound: String,
    pub bound_target: String,
    #[serde(default)]
    pub provenance: Option<serde_json::Value>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SplitShiftedExactAuditReport {
    pub sign_convention: &'static str,
    pub coefficient_count: usize,
    pub nonzero_original_exact_residual_count: usize,
    pub original_exact_bound_beta: String,
    pub gram_count: usize,
    pub original_psd_gram_count: usize,
    pub shifted_gram_count: usize,
    pub positive_definite_gram_count_after_shift: usize,
    pub semidefinite_gram_count_after_shift: usize,
    pub all_shifted_gram_matrices_exactly_positive_semidefinite: bool,
    pub minimum_nonzero_exact_ldl_pivot_after_shift: String,
    pub exact_occupation_cost_multipliers_by_cell: Vec<String>,
    pub exact_total_occupation_cost_multiplier: String,
    pub exact_interface_additive_discount: String,
    pub exact_terminal_additive_discounts_by_cell: Vec<String>,
    pub exact_terminal_additive_discount: String,
    pub exact_finite_mass_correction: String,
    pub exact_discounted_bound: String,
    pub certified_bound: String,
    pub bound_margin: String,
    pub rigorous_bound: f64,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SplitShiftedSalvageBlockRecord {
    pub derivation: SplitShiftedBlockDerivation,
    pub original_exactly_psd: bool,
    pub required_delta: String,
    pub exact_ldl_calls: usize,
    pub salvageable: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure_reason: Option<ShiftedSalvageReason>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SplitShiftedSalvageFailureRecord {
    pub schema: String,
    pub status: String,
    pub order: u8,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub formulation_hash: String,
    pub beta: String,
    pub original_identity_exact: bool,
    pub blocks: Vec<SplitShiftedSalvageBlockRecord>,
    pub unsalvageable_blocks: Vec<usize>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
#[allow(clippy::large_enum_variant)]
pub enum SplitShiftedSalvageOutcome {
    Certified {
        certificate: SplitShiftedExactDualCertificate,
    },
    Unsalvageable {
        failure: SplitShiftedSalvageFailureRecord,
    },
}

#[derive(Debug, Error)]
pub enum SplitShiftedExactAuditError {
    #[error("unsupported split shifted exact certificate schema {0:?}")]
    Schema(String),
    #[error("unsupported split shifted block ordering {0:?}")]
    BlockOrder(String),
    #[error("split shifted grid hash {found:?} does not match embedded v1 hash {expected:?}")]
    SplitGridHash { found: String, expected: String },
    #[error(
        "split shifted formulation hash {found:?} does not match regenerated hash {expected:?}"
    )]
    FormulationHash { found: String, expected: String },
    #[error("wrong split shifted block count: expected {expected}, found {found}")]
    BlockCount { expected: usize, found: usize },
    #[error("split shifted block {block} derivation does not match regenerated metadata")]
    Derivation { block: usize },
    #[error("raw split exact identity has {count} nonzero coefficients before shifting")]
    RawIdentity { count: usize },
    #[error("declared raw split beta {found} does not equal reconstructed {expected}")]
    Beta { found: String, expected: String },
    #[error("split block {block} delta must be an exact nonnegative rational")]
    Delta { block: usize },
    #[error("originally PSD split block {block} must have delta exactly zero")]
    UnexpectedShift { block: usize },
    #[error("originally non-PSD split block {block} must have delta exactly positive")]
    MissingShift { block: usize },
    #[error(
        "occupation split block {block} coordinate {coordinate} has no finite cost-relative bound"
    )]
    UnsalvageableOccupation { block: usize, coordinate: usize },
    #[error("declared occupation cell multipliers do not match regenerated exact values")]
    OccupationCells,
    #[error("declared occupation multiplier {found} does not equal regenerated {expected}")]
    OccupationTotal { found: String, expected: String },
    #[error("declared interface discount {found} does not equal regenerated {expected}")]
    InterfaceDiscount { found: String, expected: String },
    #[error("declared terminal cell discounts do not match regenerated exact values")]
    TerminalCells,
    #[error("declared terminal discount {found} does not equal regenerated {expected}")]
    TerminalDiscount { found: String, expected: String },
    #[error("declared finite-mass correction {found} does not equal regenerated {expected}")]
    FiniteMassCorrection { found: String, expected: String },
    #[error("declared discounted bound {found} does not equal regenerated {expected}")]
    DiscountedBound { found: String, expected: String },
    #[error("split shifted target {target} fails beta-E >= target*(1+K); margin {margin}")]
    TargetBound { target: String, margin: String },
    #[error(transparent)]
    Split(#[from] SplitExactAuditError),
    #[error(transparent)]
    Exact(#[from] ExactAuditError),
    #[error(transparent)]
    Shift(#[from] ShiftedExactAuditError),
}

fn as_big_rational(value: Rational) -> BigRational {
    BigRational::new(
        BigInt::from(value.numerator),
        BigInt::from(value.denominator),
    )
}

fn identity_transform(size: usize) -> Vec<Vec<(usize, i64)>> {
    (0..size).map(|index| vec![(index, 1)]).collect()
}

fn encode_transform(rows: &[Vec<(usize, i64)>]) -> Vec<Vec<SplitShiftedTransformEntry>> {
    rows.iter()
        .map(|row| {
            row.iter()
                .map(|&(basis_index, coefficient)| SplitShiftedTransformEntry {
                    basis_index,
                    coefficient,
                })
                .collect()
        })
        .collect()
}

fn localizer_supremum(localizer: HausdorffLocalizer) -> BigRational {
    match localizer {
        HausdorffLocalizer::One => BigRational::one(),
        HausdorffLocalizer::XiOneMinusXi => BigRational::new(BigInt::one(), BigInt::from(4)),
    }
}

fn safe_coordinate_bounds(
    transform_rows: &[Vec<(usize, i64)>],
    basis_bounds: &[Option<BigRational>],
    localizer: &BigRational,
) -> Vec<Option<BigRational>> {
    transform_rows
        .iter()
        .map(|row| {
            let mut l1 = BigInt::zero();
            let mut weighted = BigRational::zero();
            for &(basis_index, coefficient) in row {
                let absolute = BigInt::from(coefficient.abs());
                if absolute.is_zero() {
                    continue;
                }
                let bound = basis_bounds[basis_index].as_ref()?;
                l1 += &absolute;
                weighted += BigRational::from_integer(absolute) * bound;
            }
            Some(BigRational::from_integer(l1) * weighted * localizer)
        })
        .collect()
}

fn safe_block_bound(coordinate_bounds: &[Option<BigRational>]) -> Option<BigRational> {
    coordinate_bounds
        .iter()
        .cloned()
        .collect::<Option<Vec<_>>>()
        .map(|values| values.into_iter().sum())
}

fn basis_phases(basis: &[CostMonomial], variables: usize) -> Vec<SplitShiftedBasisPhase> {
    basis
        .iter()
        .map(|monomial| {
            if reflection_phase_is_i(monomial, variables) {
                SplitShiftedBasisPhase::I
            } else {
                SplitShiftedBasisPhase::One
            }
        })
        .collect()
}

fn occupation_derivation(
    block_index: usize,
    order: u8,
    cell_index: usize,
    owner_block_index: usize,
    metadata: &ExactGramShiftMetadata,
) -> SplitShiftedBlockDerivation {
    let localizer = localizer_supremum(metadata.localizer);
    let basis_bounds = metadata
        .basis_cost_ratios
        .iter()
        .map(|bound| bound.map(as_big_rational))
        .collect::<Vec<_>>();
    let coordinate_bounds =
        safe_coordinate_bounds(&metadata.transform_rows, &basis_bounds, &localizer);
    let block_bound = safe_block_bound(&coordinate_bounds);
    SplitShiftedBlockDerivation {
        block_index,
        order,
        family: metadata.family.into(),
        owner: SplitShiftedBlockOwner::OccupationCell { cell_index },
        owner_block_index,
        gram_side: metadata.transform_rows.len(),
        basis_bound: SplitShiftedBasisBound::RydbergCostRelativeOccupationMonomials,
        basis: metadata
            .basis
            .iter()
            .cloned()
            .map(|monomial| SplitShiftedBasisElement::StateCostMonomial { monomial })
            .collect(),
        basis_phases: basis_phases(&metadata.basis, 5),
        transform_orientation: SPLIT_SHIFTED_TRANSFORM_ORIENTATION_V1.into(),
        transform_rows: encode_transform(&metadata.transform_rows),
        localizer: metadata.localizer,
        localizer_supremum: localizer.to_string(),
        basis_squared_bounds: basis_bounds
            .iter()
            .map(|bound| bound.as_ref().map(ToString::to_string))
            .collect(),
        coordinate_bounds: coordinate_bounds
            .iter()
            .map(|bound| bound.as_ref().map(ToString::to_string))
            .collect(),
        bound_kind: SplitShiftedBoundKind::OccupationCostRelative,
        safe_block_bound: block_bound.map(|bound| bound.to_string()),
    }
}

fn interface_derivation(
    block_index: usize,
    order: u8,
    interface_index: usize,
    knot: String,
    owner_block_index: usize,
    basis: &[CostMonomial],
) -> SplitShiftedBlockDerivation {
    let transform = identity_transform(basis.len());
    let basis_bounds = vec![Some(BigRational::one()); basis.len()];
    let localizer = BigRational::one();
    let coordinate_bounds = safe_coordinate_bounds(&transform, &basis_bounds, &localizer);
    SplitShiftedBlockDerivation {
        block_index,
        order,
        family: SplitShiftedGramFamily::InterfaceMoment,
        owner: SplitShiftedBlockOwner::InterfaceKnot {
            interface_index,
            knot_index: interface_index + 1,
            knot,
        },
        owner_block_index,
        gram_side: basis.len(),
        basis_bound: SplitShiftedBasisBound::UnitStateInterfaceMonomials,
        basis: basis
            .iter()
            .cloned()
            .map(|monomial| SplitShiftedBasisElement::StateCostMonomial { monomial })
            .collect(),
        basis_phases: basis_phases(basis, 4),
        transform_orientation: SPLIT_SHIFTED_TRANSFORM_ORIENTATION_V1.into(),
        transform_rows: encode_transform(&transform),
        localizer: HausdorffLocalizer::One,
        localizer_supremum: "1".into(),
        basis_squared_bounds: vec![Some("1".into()); basis.len()],
        coordinate_bounds: coordinate_bounds
            .iter()
            .map(|bound| bound.as_ref().map(ToString::to_string))
            .collect(),
        bound_kind: SplitShiftedBoundKind::InterfaceAdditive,
        safe_block_bound: safe_block_bound(&coordinate_bounds).map(|bound| bound.to_string()),
    }
}

fn terminal_derivation(
    block_index: usize,
    order: u8,
    cell_index: usize,
    owner_block_index: usize,
    side: usize,
) -> SplitShiftedBlockDerivation {
    let localizer_kind = if owner_block_index == 0 {
        HausdorffLocalizer::One
    } else {
        HausdorffLocalizer::XiOneMinusXi
    };
    let family = if owner_block_index == 0 {
        SplitShiftedGramFamily::TerminalMoment
    } else {
        SplitShiftedGramFamily::TerminalXiOneMinusXi
    };
    let transform = identity_transform(side);
    let basis_bounds = vec![Some(BigRational::one()); side];
    let localizer = localizer_supremum(localizer_kind);
    let coordinate_bounds = safe_coordinate_bounds(&transform, &basis_bounds, &localizer);
    SplitShiftedBlockDerivation {
        block_index,
        order,
        family,
        owner: SplitShiftedBlockOwner::TerminalCell { cell_index },
        owner_block_index,
        gram_side: side,
        basis_bound: SplitShiftedBasisBound::UnitIntervalTerminalMonomials,
        basis: (0..side)
            .map(|power| SplitShiftedBasisElement::LocalCostPower { power })
            .collect(),
        basis_phases: vec![SplitShiftedBasisPhase::One; side],
        transform_orientation: SPLIT_SHIFTED_TRANSFORM_ORIENTATION_V1.into(),
        transform_rows: encode_transform(&transform),
        localizer: localizer_kind,
        localizer_supremum: localizer.to_string(),
        basis_squared_bounds: vec![Some("1".into()); side],
        coordinate_bounds: coordinate_bounds
            .iter()
            .map(|bound| bound.as_ref().map(ToString::to_string))
            .collect(),
        bound_kind: SplitShiftedBoundKind::TerminalAdditive,
        safe_block_bound: safe_block_bound(&coordinate_bounds).map(|bound| bound.to_string()),
    }
}

fn derivations_for_model(
    order: u8,
    grid: &SplitGrid,
    model: &ExactSplitModel,
) -> Result<Vec<SplitShiftedBlockDerivation>, SplitShiftedExactAuditError> {
    let base = exact_certificate_model(order).map_err(ExactAuditError::Model)?;
    let occupation = base
        .gram_shift_metadata()
        .into_iter()
        .take(base.occupation_gram_count())
        .collect::<Vec<_>>();
    let interfaces = interface_gram_bases(order);
    let dimensions = model.gram_dimensions();
    let mut result = Vec::with_capacity(dimensions.len());
    for cell_index in 0..model.cell_count() {
        for (owner_block_index, metadata) in occupation.iter().enumerate() {
            result.push(occupation_derivation(
                result.len(),
                order,
                cell_index,
                owner_block_index,
                metadata,
            ));
        }
    }
    for interface_index in 0..model.cell_count().saturating_sub(1) {
        let knot = grid.canonical_knots()[interface_index + 1].clone();
        for (owner_block_index, basis) in interfaces.iter().enumerate() {
            result.push(interface_derivation(
                result.len(),
                order,
                interface_index,
                knot.clone(),
                owner_block_index,
                basis,
            ));
        }
    }
    for cell_index in 0..model.cell_count() {
        for owner_block_index in 0..2 {
            let side = dimensions[result.len()];
            result.push(terminal_derivation(
                result.len(),
                order,
                cell_index,
                owner_block_index,
                side,
            ));
        }
    }
    debug_assert_eq!(result.len(), dimensions.len());
    Ok(result)
}

/// Regenerate every split block's physical owner, exact basis, transform,
/// reflection phase, localizer, and theorem-safe trace bound.
pub fn split_shifted_block_derivations(
    order: u8,
    grid: &SplitGrid,
) -> Result<Vec<SplitShiftedBlockDerivation>, SplitShiftedExactAuditError> {
    let model = ExactSplitModel::create(order, grid).map_err(SplitExactAuditError::Model)?;
    derivations_for_model(order, grid, &model)
}

fn parse_delta(block: usize, encoded: &str) -> Result<BigRational, SplitShiftedExactAuditError> {
    let value =
        ScalarParser::parse(encoded).map_err(|_| SplitShiftedExactAuditError::Delta { block })?;
    if !value.sqrt2.is_zero() || value.rational.is_negative() {
        return Err(SplitShiftedExactAuditError::Delta { block });
    }
    Ok(value.rational)
}

fn raw_identity_and_beta(
    certificate: &SplitExactDualCertificate,
    layout: &ValidatedLayout,
) -> Result<(Vec<BigQsqrt2>, BigQsqrt2), SplitShiftedExactAuditError> {
    let multipliers = certificate
        .liouville_multipliers_by_cell
        .iter()
        .flatten()
        .map(|value| ScalarParser::parse(value))
        .collect::<Result<Vec<_>, _>>()?;
    let normalization = ScalarParser::parse(&certificate.normalization)?;
    let grams = flattened_grams(certificate);
    let identity = reconstructed_identity(
        &layout.model,
        &multipliers,
        &normalization,
        &grams,
        &layout.dimensions,
    )?;
    let mut beta = normalization.neg();
    for (multiplier, row) in multipliers.iter().zip(&layout.model.rows) {
        beta = beta.add(
            &multiplier.mul(&BigQsqrt2::from_rational(BigRational::from_integer(
                BigInt::from(-row.rhs),
            ))),
        );
    }
    Ok((identity, beta))
}

/// Recheck the raw embedded v1 identity without attempting any Gram shift.
/// This lets callers report the precise stage of a salvage infrastructure error.
pub fn split_shifted_original_identity_is_exact(
    certificate: &SplitExactDualCertificate,
) -> Result<bool, SplitShiftedExactAuditError> {
    let layout = validate_layout(certificate)?;
    let (identity, _) = raw_identity_and_beta(certificate, &layout)?;
    Ok(identity.iter().all(BigQsqrt2::is_zero))
}

#[derive(Clone)]
struct Correction {
    owner: SplitShiftedBlockOwner,
    kind: SplitShiftedBoundKind,
    value: BigRational,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AggregatedCorrections {
    occupation_by_cell: Vec<BigRational>,
    occupation_total: BigRational,
    interface_discount: BigRational,
    terminal_by_cell: Vec<BigRational>,
    terminal_discount: BigRational,
    finite_mass_correction: BigRational,
}

fn maximum(values: &[BigRational]) -> BigRational {
    values
        .iter()
        .cloned()
        .max()
        .unwrap_or_else(BigRational::zero)
}

fn aggregate_corrections(
    cell_count: usize,
    corrections: impl IntoIterator<Item = Correction>,
) -> AggregatedCorrections {
    let mut occupation_by_cell = vec![BigRational::zero(); cell_count];
    let mut interface_discount = BigRational::zero();
    let mut terminal_by_cell = vec![BigRational::zero(); cell_count];
    for correction in corrections {
        match (correction.kind, correction.owner) {
            (
                SplitShiftedBoundKind::OccupationCostRelative,
                SplitShiftedBlockOwner::OccupationCell { cell_index },
            ) => occupation_by_cell[cell_index] += correction.value,
            (
                SplitShiftedBoundKind::InterfaceAdditive,
                SplitShiftedBlockOwner::InterfaceKnot { .. },
            ) => interface_discount += correction.value,
            (
                SplitShiftedBoundKind::TerminalAdditive,
                SplitShiftedBlockOwner::TerminalCell { cell_index },
            ) => terminal_by_cell[cell_index] += correction.value,
            _ => unreachable!("regenerated split block kind and owner agree"),
        }
    }
    let occupation_total = maximum(&occupation_by_cell);
    let terminal_discount = maximum(&terminal_by_cell);
    let finite_mass_correction = &interface_discount + &terminal_discount;
    AggregatedCorrections {
        occupation_by_cell,
        occupation_total,
        interface_discount,
        terminal_by_cell,
        terminal_discount,
        finite_mass_correction,
    }
}

fn corrections_from_blocks(
    blocks: &[SplitShiftedGramBlock],
) -> Result<Vec<Correction>, SplitShiftedExactAuditError> {
    blocks
        .iter()
        .enumerate()
        .filter_map(|(block, declared)| {
            let delta = match parse_delta(block, &declared.delta) {
                Ok(delta) if delta.is_zero() => return None,
                Ok(delta) => delta,
                Err(error) => return Some(Err(error)),
            };
            let bound = match declared.derivation.safe_block_bound.as_deref() {
                Some(bound) => match exact_rational(bound) {
                    Ok(bound) => bound,
                    Err(error) => return Some(Err(error.into())),
                },
                None => {
                    let coordinate = declared
                        .derivation
                        .coordinate_bounds
                        .iter()
                        .position(Option::is_none)
                        .expect("a missing safe block bound has a missing coordinate");
                    return Some(Err(SplitShiftedExactAuditError::UnsalvageableOccupation {
                        block,
                        coordinate,
                    }));
                }
            };
            Some(Ok(Correction {
                owner: declared.derivation.owner.clone(),
                kind: declared.derivation.bound_kind,
                value: delta * bound,
            }))
        })
        .collect()
}

fn strings(values: &[BigRational]) -> Vec<String> {
    values.iter().map(ToString::to_string).collect()
}

/// Build the additive split-shifted wrapper. Classification of zero/PSD blocks
/// remains an audit responsibility; this constructor only requires the raw v1
/// identity to close exactly and computes the declared theorem arithmetic.
pub fn build_split_shifted_exact_certificate(
    original: SplitExactDualCertificate,
    shifts: Vec<String>,
) -> Result<SplitShiftedExactDualCertificate, SplitShiftedExactAuditError> {
    let layout = validate_layout(&original)?;
    let (identity, beta) = raw_identity_and_beta(&original, &layout)?;
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if nonzero != 0 {
        return Err(SplitShiftedExactAuditError::RawIdentity { count: nonzero });
    }
    let derivations = derivations_for_model(original.order, &layout.grid, &layout.model)?;
    if shifts.len() != derivations.len() {
        return Err(SplitShiftedExactAuditError::BlockCount {
            expected: derivations.len(),
            found: shifts.len(),
        });
    }
    let blocks = derivations
        .into_iter()
        .zip(shifts)
        .enumerate()
        .map(|(block, (derivation, delta))| {
            parse_delta(block, &delta)?;
            Ok(SplitShiftedGramBlock { derivation, delta })
        })
        .collect::<Result<Vec<_>, SplitShiftedExactAuditError>>()?;
    let aggregated =
        aggregate_corrections(layout.model.cell_count(), corrections_from_blocks(&blocks)?);
    let numerator = beta.sub(&BigQsqrt2::from_rational(
        aggregated.finite_mass_correction.clone(),
    ));
    let denominator = BigQsqrt2::from_rational(BigRational::one() + &aggregated.occupation_total);
    let discounted = numerator.div(&denominator)?;
    Ok(SplitShiftedExactDualCertificate {
        schema: SPLIT_SHIFTED_EXACT_SCHEMA_V1.into(),
        block_order: SPLIT_SHIFTED_BLOCK_ORDER_V1.into(),
        split_grid_hash: original.split_grid_hash.clone(),
        formulation_hash: original.formulation_hash.clone(),
        original,
        beta: beta.to_string(),
        blocks,
        occupation_cost_multipliers_by_cell: strings(&aggregated.occupation_by_cell),
        total_occupation_cost_multiplier: aggregated.occupation_total.to_string(),
        interface_additive_discount: aggregated.interface_discount.to_string(),
        terminal_additive_discounts_by_cell: strings(&aggregated.terminal_by_cell),
        terminal_additive_discount: aggregated.terminal_discount.to_string(),
        finite_mass_correction: aggregated.finite_mass_correction.to_string(),
        discounted_bound: discounted.to_string(),
        bound_target: discounted.to_string(),
        provenance: None,
    })
}

pub fn salvage_split_shifted_exact_certificate(
    original: SplitExactDualCertificate,
) -> Result<SplitShiftedSalvageOutcome, SplitShiftedExactAuditError> {
    salvage_split_shifted_exact_certificate_inner(original)
}

pub fn salvage_split_shifted_exact_certificate_with_jobs(
    original: SplitExactDualCertificate,
    jobs: usize,
) -> Result<SplitShiftedSalvageOutcome, SplitShiftedExactAuditError> {
    if jobs == 0 {
        return Err(ExactAuditError::AuditJobs.into());
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|error| ExactAuditError::ThreadPool(error.to_string()))?
        .install(|| salvage_split_shifted_exact_certificate_inner(original))
}

fn salvage_split_shifted_exact_certificate_inner(
    original: SplitExactDualCertificate,
) -> Result<SplitShiftedSalvageOutcome, SplitShiftedExactAuditError> {
    let layout = validate_layout(&original)?;
    let (identity, beta) = raw_identity_and_beta(&original, &layout)?;
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if nonzero != 0 {
        return Err(SplitShiftedExactAuditError::RawIdentity { count: nonzero });
    }
    let derivations = derivations_for_model(original.order, &layout.grid, &layout.model)?;
    let grams = flattened_grams(&original);
    let searches = grams
        .par_iter()
        .enumerate()
        .map(|(block, encoded)| {
            let matrix = parse_matrix(block, encoded, layout.dimensions[block])?;
            let mut exact_check = matrix.clone();
            match exact_psd_result(block, &mut exact_check) {
                Ok(_) => Ok((true, "0".into(), 1_usize)),
                Err(ExactAuditError::GramPivot { .. }) => {
                    let seed = floating_minimum_eigenvalue(&matrix)?;
                    let search = exact_rational_gram_shift(encoded, seed)?;
                    Ok((false, search.delta, search.exact_ldl_calls + 1))
                }
                Err(error) => Err(error.into()),
            }
        })
        .collect::<Result<Vec<_>, SplitShiftedExactAuditError>>()?;
    let blocks = derivations
        .iter()
        .zip(&searches)
        .map(
            |(derivation, (original_exactly_psd, delta, exact_ldl_calls))| {
                let coordinates = if !original_exactly_psd
                    && derivation.bound_kind == SplitShiftedBoundKind::OccupationCostRelative
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
                                    entry.coefficient != 0
                                        && derivation.basis_squared_bounds[entry.basis_index]
                                            .is_none()
                                })
                                .map(|entry| entry.basis_index)
                                .collect(),
                        })
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                let failure_reason = (!coordinates.is_empty()).then_some(
                    ShiftedSalvageReason::NoFiniteCostRelativeBoundDerived { coordinates },
                );
                SplitShiftedSalvageBlockRecord {
                    derivation: derivation.clone(),
                    original_exactly_psd: *original_exactly_psd,
                    required_delta: delta.clone(),
                    exact_ldl_calls: *exact_ldl_calls,
                    salvageable: failure_reason.is_none(),
                    failure_reason,
                }
            },
        )
        .collect::<Vec<_>>();
    let unsalvageable_blocks = blocks
        .iter()
        .filter(|block| !block.salvageable)
        .map(|block| block.derivation.block_index)
        .collect::<Vec<_>>();
    if !unsalvageable_blocks.is_empty() {
        return Ok(SplitShiftedSalvageOutcome::Unsalvageable {
            failure: SplitShiftedSalvageFailureRecord {
                schema: SPLIT_SHIFTED_SALVAGE_FAILURE_SCHEMA_V1.into(),
                status: "unsalvageable".into(),
                order: original.order,
                knots: original.knots.clone(),
                split_grid_hash: original.split_grid_hash.clone(),
                formulation_hash: original.formulation_hash.clone(),
                beta: beta.to_string(),
                original_identity_exact: true,
                blocks,
                unsalvageable_blocks,
            },
        });
    }
    let shifts = searches.into_iter().map(|(_, delta, _)| delta).collect();
    let certificate = build_split_shifted_exact_certificate(original, shifts)?;
    audit_split_shifted_exact_certificate(&certificate)?;
    Ok(SplitShiftedSalvageOutcome::Certified { certificate })
}

pub fn audit_split_shifted_exact_certificate(
    certificate: &SplitShiftedExactDualCertificate,
) -> Result<SplitShiftedExactAuditReport, SplitShiftedExactAuditError> {
    audit_split_shifted_exact_certificate_inner(certificate)
}

pub fn audit_split_shifted_exact_certificate_with_jobs(
    certificate: &SplitShiftedExactDualCertificate,
    jobs: usize,
) -> Result<SplitShiftedExactAuditReport, SplitShiftedExactAuditError> {
    if jobs == 0 {
        return Err(ExactAuditError::AuditJobs.into());
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|error| ExactAuditError::ThreadPool(error.to_string()))?
        .install(|| audit_split_shifted_exact_certificate_inner(certificate))
}

struct BlockAudit {
    shifted: bool,
    positive_definite: bool,
    minimum: Option<BigQsqrt2>,
    correction: Option<Correction>,
}

fn parse_declared_rationals(
    encoded: &[String],
) -> Result<Vec<BigRational>, SplitShiftedExactAuditError> {
    encoded
        .iter()
        .map(|value| exact_rational(value).map_err(Into::into))
        .collect()
}

fn audit_split_shifted_exact_certificate_inner(
    certificate: &SplitShiftedExactDualCertificate,
) -> Result<SplitShiftedExactAuditReport, SplitShiftedExactAuditError> {
    if certificate.schema != SPLIT_SHIFTED_EXACT_SCHEMA_V1 {
        return Err(SplitShiftedExactAuditError::Schema(
            certificate.schema.clone(),
        ));
    }
    if certificate.block_order != SPLIT_SHIFTED_BLOCK_ORDER_V1 {
        return Err(SplitShiftedExactAuditError::BlockOrder(
            certificate.block_order.clone(),
        ));
    }
    let original = &certificate.original;
    let layout = validate_layout(original)?;
    if certificate.split_grid_hash != original.split_grid_hash {
        return Err(SplitShiftedExactAuditError::SplitGridHash {
            found: certificate.split_grid_hash.clone(),
            expected: original.split_grid_hash.clone(),
        });
    }
    let regenerated =
        structure(original.order, &layout.grid).map_err(SplitExactAuditError::Model)?;
    if certificate.formulation_hash != regenerated.formulation_hash {
        return Err(SplitShiftedExactAuditError::FormulationHash {
            found: certificate.formulation_hash.clone(),
            expected: regenerated.formulation_hash,
        });
    }

    // This raw, unshifted check is deliberately first. The theorem starts
    // from an exact split identity at beta, never from a shifted residual.
    let (identity, beta) = raw_identity_and_beta(original, &layout)?;
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if nonzero != 0 {
        return Err(SplitShiftedExactAuditError::RawIdentity { count: nonzero });
    }
    let declared_beta = ScalarParser::parse(&certificate.beta)?;
    if declared_beta != beta {
        return Err(SplitShiftedExactAuditError::Beta {
            found: declared_beta.to_string(),
            expected: beta.to_string(),
        });
    }

    let expected = derivations_for_model(original.order, &layout.grid, &layout.model)?;
    if certificate.blocks.len() != expected.len() {
        return Err(SplitShiftedExactAuditError::BlockCount {
            expected: expected.len(),
            found: certificate.blocks.len(),
        });
    }
    for (block, (declared, regenerated)) in certificate.blocks.iter().zip(&expected).enumerate() {
        if declared.derivation != *regenerated {
            return Err(SplitShiftedExactAuditError::Derivation { block });
        }
    }

    let grams = flattened_grams(original);
    let audits = grams
        .par_iter()
        .zip(&certificate.blocks)
        .enumerate()
        .map(|(block, (encoded, declared))| {
            let matrix = parse_matrix(block, encoded, layout.dimensions[block])?;
            let delta = parse_delta(block, &declared.delta)?;
            let mut original_check = matrix.clone();
            match exact_psd_result(block, &mut original_check) {
                Ok((minimum, positive_definite)) => {
                    if !delta.is_zero() {
                        return Err(SplitShiftedExactAuditError::UnexpectedShift { block });
                    }
                    Ok(BlockAudit {
                        shifted: false,
                        positive_definite,
                        minimum,
                        correction: None,
                    })
                }
                Err(ExactAuditError::GramPivot { .. }) => {
                    if !delta.is_positive() {
                        return Err(SplitShiftedExactAuditError::MissingShift { block });
                    }
                    let mut shifted = matrix;
                    add_diagonal_shift(&mut shifted, &delta);
                    let (minimum, positive_definite) = exact_psd_result(block, &mut shifted)?;
                    let bound =
                        declared
                            .derivation
                            .safe_block_bound
                            .as_deref()
                            .ok_or_else(|| {
                                SplitShiftedExactAuditError::UnsalvageableOccupation {
                                    block,
                                    coordinate: declared
                                        .derivation
                                        .coordinate_bounds
                                        .iter()
                                        .position(Option::is_none)
                                        .expect("missing safe bound has a missing coordinate"),
                                }
                            })?;
                    Ok(BlockAudit {
                        shifted: true,
                        positive_definite,
                        minimum,
                        correction: Some(Correction {
                            owner: declared.derivation.owner.clone(),
                            kind: declared.derivation.bound_kind,
                            value: delta * exact_rational(bound)?,
                        }),
                    })
                }
                Err(error) => Err(error.into()),
            }
        })
        .collect::<Result<Vec<_>, SplitShiftedExactAuditError>>()?;

    let aggregated = aggregate_corrections(
        layout.model.cell_count(),
        audits.iter().filter_map(|audit| audit.correction.clone()),
    );
    if parse_declared_rationals(&certificate.occupation_cost_multipliers_by_cell)?
        != aggregated.occupation_by_cell
    {
        return Err(SplitShiftedExactAuditError::OccupationCells);
    }
    let declared_occupation = exact_rational(&certificate.total_occupation_cost_multiplier)?;
    if declared_occupation != aggregated.occupation_total {
        return Err(SplitShiftedExactAuditError::OccupationTotal {
            found: declared_occupation.to_string(),
            expected: aggregated.occupation_total.to_string(),
        });
    }
    let declared_interface = exact_rational(&certificate.interface_additive_discount)?;
    if declared_interface != aggregated.interface_discount {
        return Err(SplitShiftedExactAuditError::InterfaceDiscount {
            found: declared_interface.to_string(),
            expected: aggregated.interface_discount.to_string(),
        });
    }
    if parse_declared_rationals(&certificate.terminal_additive_discounts_by_cell)?
        != aggregated.terminal_by_cell
    {
        return Err(SplitShiftedExactAuditError::TerminalCells);
    }
    let declared_terminal = exact_rational(&certificate.terminal_additive_discount)?;
    if declared_terminal != aggregated.terminal_discount {
        return Err(SplitShiftedExactAuditError::TerminalDiscount {
            found: declared_terminal.to_string(),
            expected: aggregated.terminal_discount.to_string(),
        });
    }
    let declared_finite = exact_rational(&certificate.finite_mass_correction)?;
    if declared_finite != aggregated.finite_mass_correction {
        return Err(SplitShiftedExactAuditError::FiniteMassCorrection {
            found: declared_finite.to_string(),
            expected: aggregated.finite_mass_correction.to_string(),
        });
    }
    let numerator = beta.sub(&BigQsqrt2::from_rational(
        aggregated.finite_mass_correction.clone(),
    ));
    let denominator = BigQsqrt2::from_rational(BigRational::one() + &aggregated.occupation_total);
    let discounted = numerator.div(&denominator)?;
    let declared_discounted = ScalarParser::parse(&certificate.discounted_bound)?;
    if declared_discounted != discounted {
        return Err(SplitShiftedExactAuditError::DiscountedBound {
            found: declared_discounted.to_string(),
            expected: discounted.to_string(),
        });
    }
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let margin = numerator.sub(&target.mul(&denominator));
    if !margin.is_zero() && !margin.is_positive() {
        return Err(SplitShiftedExactAuditError::TargetBound {
            target: target.to_string(),
            margin: margin.to_string(),
        });
    }
    let rigorous_bound = target.to_f64().ok_or_else(|| {
        ExactAuditError::InvalidScalar(
            "split shifted target cannot be represented as f64 for reporting".into(),
        )
    })?;
    let shifted_count = audits.iter().filter(|audit| audit.shifted).count();
    let positive_count = audits
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
    Ok(SplitShiftedExactAuditReport {
        sign_convention: "raw c + A_cell^T lambda + n*sum terminal_j[0] - S^T G = 0 at beta; shifted occupation trace <= max_j(K_j)*C, interface penalties sum, terminal correction <= max_j(E_j), certify (beta-E)/(1+K)",
        coefficient_count: layout.model.coefficient_count(),
        nonzero_original_exact_residual_count: 0,
        original_exact_bound_beta: beta.to_string(),
        gram_count: audits.len(),
        original_psd_gram_count: audits.len() - shifted_count,
        shifted_gram_count: shifted_count,
        positive_definite_gram_count_after_shift: positive_count,
        semidefinite_gram_count_after_shift: audits.len() - positive_count,
        all_shifted_gram_matrices_exactly_positive_semidefinite: true,
        minimum_nonzero_exact_ldl_pivot_after_shift: minimum,
        exact_occupation_cost_multipliers_by_cell: strings(&aggregated.occupation_by_cell),
        exact_total_occupation_cost_multiplier: aggregated.occupation_total.to_string(),
        exact_interface_additive_discount: aggregated.interface_discount.to_string(),
        exact_terminal_additive_discounts_by_cell: strings(&aggregated.terminal_by_cell),
        exact_terminal_additive_discount: aggregated.terminal_discount.to_string(),
        exact_finite_mass_correction: aggregated.finite_mass_correction.to_string(),
        exact_discounted_bound: discounted.to_string(),
        certified_bound: target.to_string(),
        bound_margin: margin.to_string(),
        rigorous_bound,
    })
}

#[cfg(test)]
mod tests {
    use super::super::split::EncodedMatrix;
    use super::*;
    use std::collections::BTreeMap;

    fn zero_matrix(side: usize) -> EncodedMatrix {
        vec![vec!["0".into(); side]; side]
    }

    fn diagonal_operator(
        model: &ExactSplitModel,
        block: usize,
        coordinate: usize,
    ) -> BTreeMap<usize, BigQsqrt2> {
        let mut result = BTreeMap::new();
        model.for_each_gram_entry_coefficient(
            block,
            coordinate,
            coordinate,
            |position, coefficient| {
                let value = BigQsqrt2::from_small(coefficient);
                let entry = result.entry(position).or_insert_with(BigQsqrt2::zero);
                *entry = entry.add(&value);
            },
        );
        result.retain(|_, coefficient| !coefficient.is_zero());
        result
    }

    fn add_operators(
        left: &BTreeMap<usize, BigQsqrt2>,
        right: &BTreeMap<usize, BigQsqrt2>,
    ) -> BTreeMap<usize, BigQsqrt2> {
        let mut result = left.clone();
        for (&position, coefficient) in right {
            let entry = result.entry(position).or_insert_with(BigQsqrt2::zero);
            *entry = entry.add(coefficient);
        }
        result.retain(|_, coefficient| !coefficient.is_zero());
        result
    }

    fn grouped_certificate_for_grid(
        mut grams: Vec<EncodedMatrix>,
        grid: &SplitGrid,
    ) -> SplitExactDualCertificate {
        let order = 2;
        let model = ExactSplitModel::create(order, grid).unwrap();
        let split_structure = structure(order, grid).unwrap();
        let occupation_grams_by_cell = (0..model.cell_count())
            .map(|_| {
                (0..model.occupation_gram_count_per_cell())
                    .map(|_| grams.remove(0))
                    .collect()
            })
            .collect();
        let interface_grams_by_knot = (0..model.cell_count() - 1)
            .map(|_| {
                (0..model.interface_gram_count_per_interface())
                    .map(|_| grams.remove(0))
                    .collect()
            })
            .collect();
        let terminal_grams_by_cell = (0..model.cell_count())
            .map(|_| (0..2).map(|_| grams.remove(0)).collect())
            .collect();
        assert!(grams.is_empty());
        SplitExactDualCertificate {
            schema: super::super::split::SPLIT_EXACT_SCHEMA_V1.into(),
            order,
            knots: grid.canonical_knots(),
            split_grid_hash: grid.canonical_hash(),
            formulation_hash: split_structure.formulation_hash,
            exposure_upper: crate::stationary_hausdorff::EXPOSURE_UPPER.to_string(),
            bound_target: "0".into(),
            equality_order: "cell_major_liouville_v1".into(),
            liouville_multipliers_by_cell: vec![
                vec!["0".into(); model.equality_count_per_cell()];
                model.cell_count()
            ],
            normalization: "0".into(),
            gram_order: "occupation_by_cell_then_interface_by_knot_then_terminal_pair_by_cell_v1"
                .into(),
            occupation_grams_by_cell,
            interface_grams_by_knot,
            terminal_grams_by_cell,
            provenance: None,
        }
    }

    fn weak_split_certificate_for_grid(grid: &SplitGrid) -> SplitExactDualCertificate {
        let order = 2;
        let model = ExactSplitModel::create(order, grid).unwrap();
        let dimensions = model.gram_dimensions();
        let mut grams = dimensions
            .iter()
            .copied()
            .map(zero_matrix)
            .collect::<Vec<_>>();
        let mut cost = Vec::new();
        model.for_each_cost_coefficient(|position, coefficient| cost.push((position, coefficient)));
        for (cost_position, cost_coefficient) in cost {
            let (block, gram_coefficient) = dimensions
                .iter()
                .enumerate()
                .filter(|(_, side)| **side == 1)
                .find_map(|(block, _)| {
                    let operator = diagonal_operator(&model, block, 0);
                    (operator.len() == 1 && operator.contains_key(&cost_position))
                        .then(|| (block, operator[&cost_position].clone()))
                })
                .expect("each split running-cost coordinate has a singleton SOS block");
            let value = BigQsqrt2::from_small(cost_coefficient)
                .div(&gram_coefficient)
                .unwrap();
            assert!(value.is_positive());
            grams[block][0][0] = value.to_string();
        }
        let certificate = grouped_certificate_for_grid(grams, grid);
        let layout = validate_layout(&certificate).unwrap();
        let (identity, beta) = raw_identity_and_beta(&certificate, &layout).unwrap();
        assert!(identity.iter().all(BigQsqrt2::is_zero));
        assert!(beta.is_zero());
        certificate
    }

    fn weak_split_certificate() -> SplitExactDualCertificate {
        weak_split_certificate_for_grid(&"0,1/2,1".parse::<SplitGrid>().unwrap())
    }

    fn add_rational(value: &mut String, increment: &str) {
        *value = ScalarParser::parse(value)
            .unwrap()
            .add(&ScalarParser::parse(increment).unwrap())
            .to_string();
    }

    fn flat_grams_mut(certificate: &mut SplitExactDualCertificate) -> Vec<&mut EncodedMatrix> {
        certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .collect()
    }

    fn add_failing_occupation(
        certificate: &mut SplitExactDualCertificate,
        cell_index: usize,
        require_finite_bound: bool,
    ) -> usize {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let model = ExactSplitModel::create(certificate.order, &grid).unwrap();
        let derivations = split_shifted_block_derivations(certificate.order, &grid).unwrap();
        let occupation_per_cell = model.occupation_gram_count_per_cell();
        let range = cell_index * occupation_per_cell..(cell_index + 1) * occupation_per_cell;
        let target = range
            .clone()
            .find(|&block| {
                derivations[block].family == SplitShiftedGramFamily::OccupationIntervalDiagonal
                    && derivations[block].gram_side == 1
                    && derivations[block].safe_block_bound.is_some() == require_finite_bound
                    && flattened_grams(certificate)[block][0][0] == "0"
            })
            .unwrap();
        let target_operator = diagonal_operator(&model, target, 0);
        let support = range
            .flat_map(|block| {
                (0..derivations[block].gram_side).map(move |coordinate| (block, coordinate))
            })
            .find(|&(block, coordinate)| {
                derivations[block].family == SplitShiftedGramFamily::OccupationXiOneMinusXi
                    && diagonal_operator(&model, block, coordinate) == target_operator
            })
            .unwrap();
        let mut grams = flat_grams_mut(certificate);
        add_rational(&mut grams[support.0][support.1][support.1], "1/1000");
        grams[target][0][0] = "-1/1000".into();
        drop(grams);
        let layout = validate_layout(certificate).unwrap();
        let (identity, _) = raw_identity_and_beta(certificate, &layout).unwrap();
        assert!(identity.iter().all(BigQsqrt2::is_zero));
        target
    }

    fn certificate_grid(certificate: &SplitExactDualCertificate) -> SplitGrid {
        certificate.knots.join(",").parse().unwrap()
    }

    fn assert_raw_identity_exact(certificate: &SplitExactDualCertificate) {
        assert!(split_shifted_original_identity_is_exact(certificate).unwrap());
    }

    fn add_failing_interface(
        certificate: &mut SplitExactDualCertificate,
        interface_index: usize,
    ) -> usize {
        let grid = certificate_grid(certificate);
        let model = ExactSplitModel::create(certificate.order, &grid).unwrap();
        let derivations = split_shifted_block_derivations(certificate.order, &grid).unwrap();
        let candidates = derivations
            .iter()
            .filter(|derivation| {
                matches!(
                    derivation.owner,
                    SplitShiftedBlockOwner::InterfaceKnot {
                        interface_index: found,
                        ..
                    } if found == interface_index
                )
            })
            .flat_map(|derivation| {
                (0..derivation.gram_side).map(|coordinate| {
                    (
                        derivation.block_index,
                        coordinate,
                        diagonal_operator(&model, derivation.block_index, coordinate),
                    )
                })
            })
            .collect::<Vec<_>>();
        let (target, left, right) = candidates
            .iter()
            .find_map(|target| {
                candidates.iter().find_map(|left| {
                    candidates.iter().find_map(|right| {
                        (target.0 != left.0
                            && target.0 != right.0
                            && target.2 == add_operators(&left.2, &right.2))
                        .then_some(((target.0, target.1), (left.0, left.1), (right.0, right.1)))
                    })
                })
            })
            .expect("the interface sphere quotient has a diagonal Gram relation");
        let mut grams = flat_grams_mut(certificate);
        grams[target.0][target.1][target.1] = "-1/1000".into();
        add_rational(&mut grams[left.0][left.1][left.1], "1/1000");
        add_rational(&mut grams[right.0][right.1][right.1], "1/1000");
        drop(grams);
        assert_raw_identity_exact(certificate);
        target.0
    }

    fn terminal_blocks(
        certificate: &SplitExactDualCertificate,
        cell_index: usize,
    ) -> (usize, usize) {
        let grid = certificate_grid(certificate);
        let derivations = split_shifted_block_derivations(certificate.order, &grid).unwrap();
        let find = |family| {
            derivations
                .iter()
                .find(|derivation| {
                    derivation.family == family
                        && derivation.owner == SplitShiftedBlockOwner::TerminalCell { cell_index }
                })
                .unwrap()
                .block_index
        };
        (
            find(SplitShiftedGramFamily::TerminalMoment),
            find(SplitShiftedGramFamily::TerminalXiOneMinusXi),
        )
    }

    fn add_failing_terminal_moment(
        certificate: &mut SplitExactDualCertificate,
        cell_index: usize,
    ) -> usize {
        let (moment, _) = terminal_blocks(certificate, cell_index);
        let mut grams = flat_grams_mut(certificate);
        grams[moment][1][1] = "-1/1000".into();
        grams[moment][0][2] = "1/2000".into();
        grams[moment][2][0] = "1/2000".into();
        drop(grams);
        assert_raw_identity_exact(certificate);
        moment
    }

    fn add_failing_terminal_interval(
        certificate: &mut SplitExactDualCertificate,
        cell_index: usize,
    ) -> (usize, usize) {
        let (moment, interval) = terminal_blocks(certificate, cell_index);
        let mut grams = flat_grams_mut(certificate);
        grams[interval][0][0] = "-1/1000".into();
        grams[moment][0][1] = "1/2000".into();
        grams[moment][1][0] = "1/2000".into();
        grams[moment][1][1] = "-1/1000".into();
        drop(grams);
        assert_raw_identity_exact(certificate);
        (moment, interval)
    }

    fn shifted_split_certificate() -> SplitShiftedExactDualCertificate {
        let mut original = weak_split_certificate();
        let shifted = add_failing_occupation(&mut original, 0, true);
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let mut shifts = vec!["0".into(); split_shifted_block_derivations(2, &grid).unwrap().len()];
        shifts[shifted] = "1/1000".into();
        build_split_shifted_exact_certificate(original, shifts).unwrap()
    }

    #[test]
    fn exact_split_theorem_uses_max_cell_cost_sum_interfaces_and_max_terminal_cell() {
        let q = |value: i64| BigRational::from_integer(BigInt::from(value));
        let corrections = aggregate_corrections(
            3,
            [
                Correction {
                    owner: SplitShiftedBlockOwner::OccupationCell { cell_index: 0 },
                    kind: SplitShiftedBoundKind::OccupationCostRelative,
                    value: q(2),
                },
                Correction {
                    owner: SplitShiftedBlockOwner::OccupationCell { cell_index: 1 },
                    kind: SplitShiftedBoundKind::OccupationCostRelative,
                    value: q(5),
                },
                Correction {
                    owner: SplitShiftedBlockOwner::InterfaceKnot {
                        interface_index: 0,
                        knot_index: 1,
                        knot: "1/3".into(),
                    },
                    kind: SplitShiftedBoundKind::InterfaceAdditive,
                    value: q(3),
                },
                Correction {
                    owner: SplitShiftedBlockOwner::InterfaceKnot {
                        interface_index: 1,
                        knot_index: 2,
                        knot: "2/3".into(),
                    },
                    kind: SplitShiftedBoundKind::InterfaceAdditive,
                    value: q(4),
                },
                Correction {
                    owner: SplitShiftedBlockOwner::TerminalCell { cell_index: 0 },
                    kind: SplitShiftedBoundKind::TerminalAdditive,
                    value: q(11),
                },
                Correction {
                    owner: SplitShiftedBlockOwner::TerminalCell { cell_index: 2 },
                    kind: SplitShiftedBoundKind::TerminalAdditive,
                    value: q(7),
                },
            ],
        );
        assert_eq!(corrections.occupation_by_cell, vec![q(2), q(5), q(0)]);
        assert_eq!(corrections.occupation_total, q(5));
        assert_eq!(corrections.interface_discount, q(7));
        assert_eq!(corrections.terminal_by_cell, vec![q(11), q(0), q(7)]);
        assert_eq!(corrections.terminal_discount, q(11));
        assert_eq!(corrections.finite_mass_correction, q(18));

        let beta = BigQsqrt2::from_rational(q(30));
        let numerator = beta.sub(&BigQsqrt2::from_rational(
            corrections.finite_mass_correction,
        ));
        let denominator = BigQsqrt2::from_rational(q(1) + corrections.occupation_total);
        assert_eq!(numerator.div(&denominator).unwrap().to_string(), "2");
        assert!(
            numerator
                .sub(&ScalarParser::parse("2").unwrap().mul(&denominator))
                .is_zero()
        );
    }

    #[test]
    fn regenerates_every_split_owner_basis_phase_localizer_and_safe_bound() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let blocks = split_shifted_block_derivations(2, &grid).unwrap();
        let model = ExactSplitModel::create(2, &grid).unwrap();
        assert_eq!(blocks.len(), model.gram_dimensions().len());
        for (index, block) in blocks.iter().enumerate() {
            assert_eq!(block.block_index, index);
            assert_eq!(block.order, 2);
            assert_eq!(block.gram_side, model.gram_dimensions()[index]);
            assert_eq!(block.basis.len(), block.basis_phases.len());
            assert_eq!(block.transform_rows.len(), block.gram_side);
        }
        let interface = blocks
            .iter()
            .find(|block| block.family == SplitShiftedGramFamily::InterfaceMoment)
            .unwrap();
        assert!(matches!(
            interface.owner,
            SplitShiftedBlockOwner::InterfaceKnot {
                interface_index: 0,
                knot_index: 1,
                ref knot,
            } if knot == "1/2"
        ));
        assert_eq!(
            interface.safe_block_bound.as_deref(),
            Some(interface.gram_side.to_string().as_str())
        );
        let terminal_interval = blocks
            .iter()
            .find(|block| block.family == SplitShiftedGramFamily::TerminalXiOneMinusXi)
            .unwrap();
        assert_eq!(terminal_interval.localizer_supremum, "1/4");
        assert_eq!(terminal_interval.safe_block_bound, Some("1/2".into()));
    }

    #[test]
    fn salvages_identity_preserving_interface_and_terminal_shifts_end_to_end() {
        let grid = "0,1/3,2/3,1".parse::<SplitGrid>().unwrap();
        let mut original = weak_split_certificate_for_grid(&grid);
        let interface_targets = [
            add_failing_interface(&mut original, 0),
            add_failing_interface(&mut original, 1),
        ];
        let terminal_cell_zero = add_failing_terminal_moment(&mut original, 0);
        let (terminal_cell_one_moment, terminal_cell_one_interval) =
            add_failing_terminal_interval(&mut original, 1);
        assert_raw_identity_exact(&original);

        let outcome = salvage_split_shifted_exact_certificate_with_jobs(original, 2).unwrap();
        let SplitShiftedSalvageOutcome::Certified { certificate } = outcome else {
            panic!("finite-mass Gram shifts must be salvageable")
        };
        let report = audit_split_shifted_exact_certificate_with_jobs(&certificate, 2).unwrap();
        for target in interface_targets.into_iter().chain([
            terminal_cell_zero,
            terminal_cell_one_moment,
            terminal_cell_one_interval,
        ]) {
            assert_ne!(certificate.blocks[target].delta, "0");
        }

        let mut interface_indices = Vec::new();
        let mut expected_interface = BigRational::zero();
        let mut expected_terminal = vec![BigRational::zero(); 3];
        for (block, declared) in certificate.blocks.iter().enumerate() {
            let delta = parse_delta(block, &declared.delta).unwrap();
            if delta.is_zero() {
                continue;
            }
            match &declared.derivation.owner {
                SplitShiftedBlockOwner::InterfaceKnot {
                    interface_index, ..
                } => {
                    interface_indices.push(*interface_index);
                    expected_interface += delta
                        * BigRational::from_integer(BigInt::from(declared.derivation.gram_side));
                }
                SplitShiftedBlockOwner::TerminalCell { cell_index } => {
                    let bound = match declared.derivation.family {
                        SplitShiftedGramFamily::TerminalMoment => {
                            BigRational::from_integer(BigInt::from(3))
                        }
                        SplitShiftedGramFamily::TerminalXiOneMinusXi => {
                            BigRational::new(BigInt::one(), BigInt::from(2))
                        }
                        _ => panic!("terminal owner has terminal family"),
                    };
                    expected_terminal[*cell_index] += delta * bound;
                }
                SplitShiftedBlockOwner::OccupationCell { .. } => {
                    panic!("finite-mass fixture must not shift occupation blocks")
                }
            }
        }
        interface_indices.sort_unstable();
        assert_eq!(interface_indices, vec![0, 1]);
        assert_eq!(
            report.exact_interface_additive_discount,
            expected_interface.to_string()
        );
        assert_eq!(
            parse_declared_rationals(&report.exact_terminal_additive_discounts_by_cell).unwrap(),
            expected_terminal
        );
        assert!(expected_terminal[1] > expected_terminal[0]);
        assert!(expected_terminal[0].is_positive());
        assert!(expected_terminal[2].is_zero());
        assert_eq!(
            report.exact_terminal_additive_discount,
            expected_terminal[1].to_string()
        );
        assert_eq!(
            report.exact_finite_mass_correction,
            (&expected_interface + &expected_terminal[1]).to_string()
        );

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.terminal_additive_discounts_by_cell[0], "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::TerminalCells)
        ));

        let mut tampered = certificate;
        add_rational(&mut tampered.finite_mass_correction, "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::FiniteMassCorrection { .. })
        ));
    }

    #[test]
    fn split_shifted_audit_is_serial_parallel_identical_and_rejects_tampering() {
        let certificate = shifted_split_certificate();
        let shifted = certificate
            .blocks
            .iter()
            .position(|block| block.delta != "0")
            .unwrap();
        let serial = audit_split_shifted_exact_certificate_with_jobs(&certificate, 1).unwrap();
        let parallel = audit_split_shifted_exact_certificate_with_jobs(&certificate, 2).unwrap();
        assert_eq!(serial, parallel);
        assert_eq!(serial.shifted_gram_count, 1);
        assert_eq!(serial.exact_total_occupation_cost_multiplier, "1/1000");

        let mut tampered = certificate.clone();
        tampered.schema.push_str("-tampered");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::Schema(_))
        ));

        let mut tampered = certificate.clone();
        tampered.blocks[shifted].derivation.family = SplitShiftedGramFamily::InterfaceMoment;
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::Derivation { .. })
        ));

        let mut tampered = certificate.clone();
        tampered.blocks[shifted].derivation.owner =
            SplitShiftedBlockOwner::OccupationCell { cell_index: 1 };
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::Derivation { .. })
        ));

        let mut tampered = certificate.clone();
        tampered.blocks[shifted].derivation.safe_block_bound = Some("0".into());
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::Derivation { .. })
        ));

        let mut tampered = certificate.clone();
        tampered.blocks[shifted].delta = "999/1000000".into();
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::Exact(
                ExactAuditError::GramPivot { .. }
            ))
        ));

        for invalid in ["-1/1000", "sqrt(2)/1000"] {
            let mut tampered = certificate.clone();
            tampered.blocks[shifted].delta = invalid.into();
            assert!(matches!(
                audit_split_shifted_exact_certificate(&tampered),
                Err(SplitShiftedExactAuditError::Delta { block }) if block == shifted
            ));
        }

        let mut tampered = certificate.clone();
        add_rational(
            &mut tampered.original.occupation_grams_by_cell[0]
                [tampered.blocks[shifted].derivation.owner_block_index][0][0],
            "1/1000000",
        );
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::RawIdentity { .. })
        ));

        let mut tampered = certificate.clone();
        tampered.beta = "1".into();
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::Beta { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.occupation_cost_multipliers_by_cell[0], "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::OccupationCells)
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.total_occupation_cost_multiplier, "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::OccupationTotal { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.interface_additive_discount, "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::InterfaceDiscount { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.terminal_additive_discount, "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::TerminalDiscount { .. })
        ));

        let mut tampered = certificate.clone();
        add_rational(&mut tampered.discounted_bound, "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::DiscountedBound { .. })
        ));

        let mut tampered = certificate;
        add_rational(&mut tampered.bound_target, "1");
        assert!(matches!(
            audit_split_shifted_exact_certificate(&tampered),
            Err(SplitShiftedExactAuditError::TargetBound { .. })
        ));
    }

    #[test]
    fn exact_zero_and_already_psd_split_blocks_cannot_shift() {
        let original = weak_split_certificate();
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let count = split_shifted_block_derivations(2, &grid).unwrap().len();
        let mut certificate =
            build_split_shifted_exact_certificate(original, vec!["0".into(); count]).unwrap();
        let zero = flattened_grams(&certificate.original)
            .iter()
            .position(|matrix| matrix.iter().flatten().all(|value| value == "0"))
            .unwrap();
        certificate.blocks[zero].delta = "1/1000".into();
        assert!(matches!(
            audit_split_shifted_exact_certificate(&certificate),
            Err(SplitShiftedExactAuditError::UnexpectedShift { block }) if block == zero
        ));
    }

    #[test]
    fn salvage_is_parallel_stable_and_rejects_required_zero_cost_occupation_shift() {
        let mut original = weak_split_certificate();
        let salvageable = add_failing_occupation(&mut original, 0, true);
        let unsalvageable = add_failing_occupation(&mut original, 1, false);
        let serial =
            salvage_split_shifted_exact_certificate_with_jobs(original.clone(), 1).unwrap();
        let parallel = salvage_split_shifted_exact_certificate_with_jobs(original, 2).unwrap();
        assert_eq!(
            serde_json::to_value(&serial).unwrap(),
            serde_json::to_value(&parallel).unwrap()
        );
        let SplitShiftedSalvageOutcome::Unsalvageable { failure } = serial else {
            panic!("a required zero-cost occupation shift must reject salvage")
        };
        assert_eq!(failure.unsalvageable_blocks, vec![unsalvageable]);
        assert!(failure.blocks[salvageable].salvageable);
        assert!(!failure.blocks[unsalvageable].salvageable);
        assert!(matches!(
            failure.blocks[unsalvageable].failure_reason,
            Some(ShiftedSalvageReason::NoFiniteCostRelativeBoundDerived { .. })
        ));
    }

    #[test]
    fn split_family_partition_tampering_is_rejected_before_shift_audit() {
        let mut certificate = shifted_split_certificate();
        let interface = certificate.original.interface_grams_by_knot[0].remove(0);
        certificate.original.occupation_grams_by_cell[0].push(interface);
        assert!(matches!(
            audit_split_shifted_exact_certificate(&certificate),
            Err(SplitShiftedExactAuditError::Split(
                SplitExactAuditError::GroupCount { .. }
            ))
        ));
    }
}
