//! Optimizer-free exact audit of stationary-torus dual certificates.
//!
//! Certificate scalars use arbitrary-precision `Q(sqrt(2))`, independently of
//! the bounded exact coefficients used while assembling floating solver tasks.

use crate::algebra::Qsqrt2;
use crate::stationary_torus::exact_certificate_model;
use nalgebra::DMatrix;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::sync::Mutex;
use thiserror::Error;

const EXACT_SCHEMA_V1: &str = "jan22-exact-dual-q-v1";
const HAUSDORFF_SCHEMA_V1: &str = "jan22-cost-lifted-exact-dual-q-v1";
const EXACT_SCHEMA_V2: &str = "minexposure/stationary-exact-dual-v2";

mod split;
pub use split::{
    SPLIT_EXACT_SCHEMA_V1, SPLIT_REPAIR_SYSTEM_SCHEMA_V1, SplitConeRepairDiagnostics,
    SplitConeRepairPlan, SplitExactAuditError, SplitExactDualCertificate,
    SplitExactRepairDiagnostics, SplitFaceBlock, SplitFaceRepairReport, SplitNativeBarFaceBlock,
    SplitNativeBarFacePlan, SplitNearNullEigenDiagnostics, SplitRepairSystemSummary,
    SplitRotatedConeRepairPlan, SplitRotatedFaceBuildReport, SplitRotatedFaceState,
    SplitRotatedKernelBuildReport, SplitRotatedKernelState, apply_split_cone_repair,
    apply_split_rotated_cone_repair, audit_split_exact_certificate,
    audit_split_exact_certificate_with_jobs, augment_split_rotated_kernels_with_zero_rows,
    build_split_bar_cone_repair_problem, build_split_bar_cone_repair_problem_scaled,
    build_split_bar_cone_repair_problem_scaled_restricted, build_split_cone_repair_problem,
    build_split_kernel_bar_cone_repair_problem_scaled,
    build_split_kernel_bar_cone_repair_problem_scaled_restricted, build_split_native_bar_face_plan,
    build_split_rotated_bar_cone_repair_problem_scaled,
    build_split_rotated_bar_cone_repair_problem_scaled_restricted,
    check_split_exact_affine_closure, check_split_exact_kernel_closure, export_split_repair_system,
    minimum_reconstructed_split_gram_eigenvalue, project_split_grams_to_rotated_kernels,
    repair_split_exact_identity, repair_split_exact_identity_componentwise,
    repair_split_exact_identity_componentwise_with_support, repair_split_exact_identity_on_faces,
    repair_split_exact_identity_on_rotated_faces, repair_split_exact_identity_ordered,
    repair_split_exact_identity_restricted, repair_split_exact_identity_with_kernels,
    repair_split_exact_identity_with_support, restore_split_rotated_gram_faces,
    select_split_rotated_gram_faces, select_split_rotated_gram_kernels,
    split_near_null_eigen_diagnostics, split_rotated_face_states,
    validate_split_rotated_gram_kernels, zero_small_split_face_coordinate_rows,
    zero_small_split_gram_rows,
};
mod split_shifted;
pub use split_shifted::{
    SPLIT_SHIFTED_EXACT_SCHEMA_V1, SPLIT_SHIFTED_SALVAGE_ERROR_SCHEMA_V1,
    SPLIT_SHIFTED_SALVAGE_FAILURE_SCHEMA_V1, SplitShiftedBasisBound, SplitShiftedBasisElement,
    SplitShiftedBasisPhase, SplitShiftedBlockDerivation, SplitShiftedBlockOwner,
    SplitShiftedBoundKind, SplitShiftedExactAuditError, SplitShiftedExactAuditReport,
    SplitShiftedExactDualCertificate, SplitShiftedGramBlock, SplitShiftedGramFamily,
    SplitShiftedSalvageBlockRecord, SplitShiftedSalvageFailureRecord, SplitShiftedSalvageOutcome,
    SplitShiftedTransformEntry, audit_split_shifted_exact_certificate,
    audit_split_shifted_exact_certificate_with_jobs, build_split_shifted_exact_certificate,
    salvage_split_shifted_exact_certificate, salvage_split_shifted_exact_certificate_with_jobs,
    split_shifted_block_derivations, split_shifted_original_identity_is_exact,
};
mod shifted;
pub use shifted::{
    ExactShiftSearch, SHIFTED_HAUSDORFF_SCHEMA_V1, SHIFTED_SALVAGE_FAILURE_SCHEMA_V1,
    ShiftedBlockDerivation, ShiftedBoundKind, ShiftedExactAuditError, ShiftedExactAuditReport,
    ShiftedExactDualCertificate, ShiftedGramBlock, ShiftedSalvageBlockRecord,
    ShiftedSalvageFailureRecord, ShiftedSalvageOutcome, ShiftedSalvageReason,
    ShiftedTransformEntry, ShiftedZeroCostCoordinate, audit_shifted_exact_certificate,
    audit_shifted_exact_certificate_with_jobs, build_shifted_exact_certificate,
    exact_rational_gram_shift, salvage_exact_shifted_certificate,
    salvage_exact_shifted_certificate_with_jobs, shifted_block_derivations,
};

#[derive(Clone, Debug, Eq, PartialEq)]
struct BigQsqrt2 {
    rational: BigRational,
    sqrt2: BigRational,
}

impl BigQsqrt2 {
    fn zero() -> Self {
        Self {
            rational: BigRational::zero(),
            sqrt2: BigRational::zero(),
        }
    }

    fn from_rational(value: BigRational) -> Self {
        Self {
            rational: value,
            sqrt2: BigRational::zero(),
        }
    }

    fn from_small(value: Qsqrt2) -> Self {
        fn rational(value: crate::Rational) -> BigRational {
            BigRational::new(
                BigInt::from(value.numerator),
                BigInt::from(value.denominator),
            )
        }
        Self {
            rational: rational(value.rational),
            sqrt2: rational(value.sqrt2),
        }
    }

    fn add(&self, rhs: &Self) -> Self {
        Self {
            rational: &self.rational + &rhs.rational,
            sqrt2: &self.sqrt2 + &rhs.sqrt2,
        }
    }

    fn sub(&self, rhs: &Self) -> Self {
        Self {
            rational: &self.rational - &rhs.rational,
            sqrt2: &self.sqrt2 - &rhs.sqrt2,
        }
    }

    fn neg(&self) -> Self {
        Self {
            rational: -&self.rational,
            sqrt2: -&self.sqrt2,
        }
    }

    fn mul(&self, rhs: &Self) -> Self {
        let two = BigRational::from_integer(BigInt::from(2));
        Self {
            rational: &self.rational * &rhs.rational + &two * &self.sqrt2 * &rhs.sqrt2,
            sqrt2: &self.rational * &rhs.sqrt2 + &self.sqrt2 * &rhs.rational,
        }
    }

    fn div(&self, rhs: &Self) -> Result<Self, ExactAuditError> {
        let two = BigRational::from_integer(BigInt::from(2));
        let denominator = &rhs.rational * &rhs.rational - &two * &rhs.sqrt2 * &rhs.sqrt2;
        if denominator.is_zero() {
            return Err(ExactAuditError::InvalidScalar(
                "division by zero in Q(sqrt(2))".into(),
            ));
        }
        Ok(Self {
            rational: (&self.rational * &rhs.rational - &two * &self.sqrt2 * &rhs.sqrt2)
                / &denominator,
            sqrt2: (&self.sqrt2 * &rhs.rational - &self.rational * &rhs.sqrt2) / denominator,
        })
    }

    fn mul_small(&self, rhs: Qsqrt2) -> Self {
        self.mul(&Self::from_small(rhs))
    }

    fn is_zero(&self) -> bool {
        self.rational.is_zero() && self.sqrt2.is_zero()
    }

    /// Decide positivity using rational comparisons only.
    fn is_positive(&self) -> bool {
        let a = &self.rational;
        let b = &self.sqrt2;
        if b.is_zero() {
            return a.is_positive();
        }
        if !a.is_negative() && b.is_positive() {
            return true;
        }
        if !a.is_positive() && b.is_negative() {
            return false;
        }
        let comparison = a * a - BigRational::from_integer(BigInt::from(2)) * b * b;
        if a.is_positive() {
            comparison.is_positive()
        } else {
            comparison.is_negative()
        }
    }

    fn to_f64(&self) -> Option<f64> {
        Some(self.rational.to_f64()? + self.sqrt2.to_f64()? * std::f64::consts::SQRT_2)
    }

    /// Rational upper bound using sqrt(2) < 2.
    fn absolute_upper(&self) -> BigRational {
        self.rational.abs() + BigRational::from_integer(BigInt::from(2)) * self.sqrt2.abs()
    }
}

impl fmt::Display for BigQsqrt2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.sqrt2.is_zero() {
            return write!(formatter, "{}", self.rational);
        }
        if self.rational.is_zero() {
            return write!(formatter, "{}*sqrt(2)", self.sqrt2);
        }
        if self.sqrt2.is_negative() {
            write!(formatter, "{} - {}*sqrt(2)", self.rational, -&self.sqrt2)
        } else {
            write!(formatter, "{} + {}*sqrt(2)", self.rational, self.sqrt2)
        }
    }
}

struct ScalarParser {
    input: Vec<u8>,
    position: usize,
}

impl ScalarParser {
    fn parse(input: &str) -> Result<BigQsqrt2, ExactAuditError> {
        let compact = input
            .bytes()
            .filter(|byte| !byte.is_ascii_whitespace())
            .collect::<Vec<_>>();
        let mut parser = Self {
            input: compact,
            position: 0,
        };
        let value = parser.expression()?;
        if parser.position != parser.input.len() {
            return Err(parser.error("unexpected trailing input"));
        }
        Ok(value)
    }

    fn expression(&mut self) -> Result<BigQsqrt2, ExactAuditError> {
        let mut value = self.term()?;
        loop {
            if self.consume(b'+') {
                value = value.add(&self.term()?);
            } else if self.consume(b'-') {
                value = value.sub(&self.term()?);
            } else {
                return Ok(value);
            }
        }
    }

    fn term(&mut self) -> Result<BigQsqrt2, ExactAuditError> {
        let mut value = self.factor()?;
        loop {
            if self.consume(b'*') {
                value = value.mul(&self.factor()?);
            } else if self.consume(b'/') {
                value = value.div(&self.factor()?)?;
            } else {
                return Ok(value);
            }
        }
    }

    fn factor(&mut self) -> Result<BigQsqrt2, ExactAuditError> {
        if self.consume(b'+') {
            return self.factor();
        }
        if self.consume(b'-') {
            return Ok(self.factor()?.neg());
        }
        if self.consume_bytes(b"sqrt(2)") {
            return Ok(BigQsqrt2 {
                rational: BigRational::zero(),
                sqrt2: BigRational::one(),
            });
        }
        if self.consume(b'(') {
            let value = self.expression()?;
            if !self.consume(b')') {
                return Err(self.error("missing closing parenthesis"));
            }
            return Ok(value);
        }
        self.number().map(BigQsqrt2::from_rational)
    }

    fn number(&mut self) -> Result<BigRational, ExactAuditError> {
        let start = self.position;
        while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
            self.position += 1;
        }
        let integer_end = self.position;
        let mut fractional_digits = 0_u32;
        if self.consume(b'.') {
            let fractional_start = self.position;
            while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                self.position += 1;
            }
            fractional_digits = u32::try_from(self.position - fractional_start)
                .map_err(|_| self.error("decimal is too long"))?;
            if fractional_digits == 0 {
                return Err(self.error("decimal point must be followed by digits"));
            }
        }
        if integer_end == start && fractional_digits == 0 {
            return Err(self.error("expected a number"));
        }
        let mantissa_end = self.position;
        let exponent = if self.consume(b'e') || self.consume(b'E') {
            let negative = self.consume(b'-');
            if !negative {
                let _ = self.consume(b'+');
            }
            let exponent_start = self.position;
            while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
                self.position += 1;
            }
            if exponent_start == self.position {
                return Err(self.error("scientific exponent has no digits"));
            }
            let magnitude = std::str::from_utf8(&self.input[exponent_start..self.position])
                .expect("ASCII digits")
                .parse::<i32>()
                .map_err(|_| self.error("scientific exponent is too large"))?;
            if negative { -magnitude } else { magnitude }
        } else {
            0
        };

        let digits = self.input[start..mantissa_end]
            .iter()
            .copied()
            .filter(|&byte| byte != b'.')
            .collect::<Vec<_>>();
        let numerator =
            BigInt::parse_bytes(&digits, 10).ok_or_else(|| self.error("invalid decimal digits"))?;
        let fractional_digits =
            i32::try_from(fractional_digits).map_err(|_| self.error("decimal is too long"))?;
        let decimal_exponent = exponent
            .checked_sub(fractional_digits)
            .ok_or_else(|| self.error("scientific exponent is too large"))?;
        if decimal_exponent >= 0 {
            Ok(BigRational::from_integer(
                numerator * BigInt::from(10_u8).pow(decimal_exponent as u32),
            ))
        } else {
            Ok(BigRational::new(
                numerator,
                BigInt::from(10_u8).pow(decimal_exponent.unsigned_abs()),
            ))
        }
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.position).copied()
    }

    fn consume(&mut self, expected: u8) -> bool {
        if self.peek() == Some(expected) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn consume_bytes(&mut self, expected: &[u8]) -> bool {
        if self.input[self.position..].starts_with(expected) {
            self.position += expected.len();
            true
        } else {
            false
        }
    }

    fn error(&self, message: &str) -> ExactAuditError {
        ExactAuditError::InvalidScalar(format!("{message} at byte {}", self.position))
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ExactDualCertificate {
    pub schema: String,
    pub order: u8,
    pub bound_target: String,
    pub equalities: Vec<String>,
    #[serde(default)]
    pub grams: Vec<Vec<Vec<String>>>,
    #[serde(default)]
    pub exposure_upper: Option<String>,
    #[serde(default)]
    pub normalization: Option<String>,
    #[serde(default)]
    pub occupation_grams: Vec<Vec<Vec<String>>>,
    #[serde(default)]
    pub terminal_grams: Vec<Vec<Vec<String>>>,
    #[serde(default)]
    pub residual_policy: Option<String>,
    #[serde(default)]
    pub residual_upper: Option<String>,
    #[serde(default)]
    pub formulation_hash: Option<String>,
    #[serde(default)]
    pub provenance: Option<serde_json::Value>,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ExactAuditReport {
    pub sign_convention: &'static str,
    pub coefficient_count: usize,
    pub nonzero_exact_residual_count: usize,
    pub all_gram_matrices_exactly_positive_definite: bool,
    pub all_gram_matrices_exactly_positive_semidefinite: bool,
    pub positive_definite_gram_count: usize,
    pub zero_gram_count: usize,
    pub residual_certified_gram_count: usize,
    pub exact_ldl_certified_gram_count: usize,
    pub minimum_certified_gram_eigenvalue_lower_bound: String,
    pub minimum_exact_ldl_pivot: String,
    pub exact_endpoint_bound: String,
    pub cost_relative_residual_upper: String,
    pub certified_bound: String,
    pub endpoint_margin_after_residual: String,
    pub strictly_exceeds_target: bool,
    pub rigorous_bound: f64,
}

#[derive(Debug, Error)]
pub enum ExactAuditError {
    #[error("unsupported exact certificate schema {0:?}")]
    Schema(String),
    #[error("invalid Q(sqrt(2)) scalar: {0}")]
    InvalidScalar(String),
    #[error("wrong equality multiplier count: expected {expected}, found {found}")]
    EqualityCount { expected: usize, found: usize },
    #[error("wrong Gram block count: expected {expected}, found {found}")]
    GramCount { expected: usize, found: usize },
    #[error("Gram block {block} has shape mismatch: expected {expected}x{expected}")]
    GramShape { block: usize, expected: usize },
    #[error("Gram block {block} is not exactly symmetric at ({row}, {column})")]
    GramSymmetry {
        block: usize,
        row: usize,
        column: usize,
    },
    #[error("Gram block {block} LDL pivot {pivot} is not exactly positive: {value}")]
    GramPivot {
        block: usize,
        pivot: usize,
        value: String,
    },
    #[error("exact coefficient identity failed with {count} nonzero residuals")]
    Identity { count: usize },
    #[error("stationary exact v2 requires cost_relative residual policy")]
    ResidualPolicy,
    #[error(
        "cost-relative residual is unsound: coefficient {position} has Rydberg degree {degree}, below two"
    )]
    ResidualDegree { position: usize, degree: u16 },
    #[error("declared residual upper {declared} is below reconstructed upper {reconstructed}")]
    ResidualUpper {
        declared: String,
        reconstructed: String,
    },
    #[error("certificate formulation hash {found:?} does not match regenerated hash {expected:?}")]
    FormulationHash { found: String, expected: String },
    #[error("certificate bound {bound} is below target {target}")]
    Bound { bound: String, target: String },
    #[error("cost-lift exposure upper must be exactly 2935887/1000000")]
    ExposureUpper,
    #[error("cost-lift certificate is missing its normalization multiplier")]
    Normalization,
    #[error("internal stationary-torus model error: {0}")]
    Model(String),
    #[error("audit job count must be positive")]
    AuditJobs,
    #[error("cannot create exact-audit thread pool: {0}")]
    ThreadPool(String),
    #[error("low-degree exact residual repair is inconsistent")]
    ResidualRepair,
}

#[derive(Clone)]
enum ParsedGram {
    Rational(Vec<Vec<BigRational>>),
    Quadratic(Vec<Vec<BigQsqrt2>>),
}

fn parse_matrix(
    block: usize,
    encoded: &[Vec<String>],
    expected: usize,
) -> Result<ParsedGram, ExactAuditError> {
    if encoded.len() != expected || encoded.iter().any(|row| row.len() != expected) {
        return Err(ExactAuditError::GramShape { block, expected });
    }
    let matrix = encoded
        .iter()
        .map(|row| {
            row.iter()
                .map(|value| ScalarParser::parse(value))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (row, values) in matrix.iter().enumerate() {
        for (column, value) in values.iter().enumerate().take(row) {
            if value != &matrix[column][row] {
                return Err(ExactAuditError::GramSymmetry { block, row, column });
            }
        }
    }
    if matrix.iter().flatten().all(|value| value.sqrt2.is_zero()) {
        Ok(ParsedGram::Rational(
            matrix
                .into_iter()
                .map(|row| row.into_iter().map(|value| value.rational).collect())
                .collect(),
        ))
    } else {
        Ok(ParsedGram::Quadratic(matrix))
    }
}

const SQRT2_ENCLOSURE_DENOMINATOR: i128 = 100_000_000_000;
const SQRT2_ENCLOSURE_LOWER_NUMERATOR: i128 = 141_421_356_237;
const SQRT2_ENCLOSURE_UPPER_NUMERATOR: i128 = 141_421_356_238;
const _: () = assert!(
    SQRT2_ENCLOSURE_LOWER_NUMERATOR * SQRT2_ENCLOSURE_LOWER_NUMERATOR
        < 2 * SQRT2_ENCLOSURE_DENOMINATOR * SQRT2_ENCLOSURE_DENOMINATOR
        && SQRT2_ENCLOSURE_UPPER_NUMERATOR * SQRT2_ENCLOSURE_UPPER_NUMERATOR
            > 2 * SQRT2_ENCLOSURE_DENOMINATOR * SQRT2_ENCLOSURE_DENOMINATOR
);

#[derive(Clone)]
struct Dyadic {
    numerator: BigInt,
    denominator_bits: usize,
}

impl Dyadic {
    fn zero() -> Self {
        Self {
            numerator: BigInt::zero(),
            denominator_bits: 0,
        }
    }

    /// Recover the exact dyadic rational represented by a finite `f64`.
    fn from_f64(value: f64) -> Option<Self> {
        if !value.is_finite() {
            return None;
        }
        let bits = value.to_bits();
        let exponent_bits = ((bits >> 52) & 0x7ff) as i32;
        let fraction = bits & ((1_u64 << 52) - 1);
        let (mut mantissa, mut exponent) = if exponent_bits == 0 {
            (fraction, -1074)
        } else {
            ((1_u64 << 52) | fraction, exponent_bits - 1023 - 52)
        };
        if mantissa == 0 {
            return Some(Self::zero());
        }
        let trailing = mantissa.trailing_zeros();
        mantissa >>= trailing;
        exponent += trailing as i32;
        let mut numerator = BigInt::from(mantissa);
        if bits >> 63 != 0 {
            numerator = -numerator;
        }
        if exponent >= 0 {
            numerator <<= exponent as usize;
            Some(Self {
                numerator,
                denominator_bits: 0,
            })
        } else {
            Some(Self {
                numerator,
                denominator_bits: (-exponent) as usize,
            })
        }
    }

    fn scaled_numerator(&self, denominator_bits: usize) -> BigInt {
        debug_assert!(denominator_bits >= self.denominator_bits);
        &self.numerator << (denominator_bits - self.denominator_bits)
    }
}

#[derive(Clone)]
struct ExactQsqrt2 {
    rational: BigRational,
    sqrt2: BigRational,
}

struct ResidualGramCertificate {
    minimum_eigenvalue_lower_bound: BigRational,
    removed_zero_rows: usize,
}

enum PositiveGramCertificate {
    Residual(ResidualGramCertificate),
    ExactLdl(BigQsqrt2),
}

/// Attempt a rigorous positive-definiteness proof without rational arithmetic
/// in the cubic loop. Numerical eigendecomposition and Cholesky only choose a
/// dyadic hint. Acceptance is decided by an exact common-denominator residual.
fn residual_gram_certificate(matrix: &ParsedGram) -> Option<ResidualGramCertificate> {
    let dimension = match matrix {
        ParsedGram::Rational(values) => values.len(),
        ParsedGram::Quadratic(values) => values.len(),
    };
    let active = (0..dimension)
        .filter(|&row| (0..dimension).any(|column| !matrix.entry_is_zero(row, column)))
        .collect::<Vec<_>>();
    if active.is_empty() {
        return None;
    }
    let compressed_dimension = active.len();
    let mut floating = DMatrix::<f64>::zeros(compressed_dimension, compressed_dimension);
    let mut exact = Vec::with_capacity(compressed_dimension * compressed_dimension);
    let mut exact_denominator = BigInt::one();
    for (compressed_row, &row) in active.iter().enumerate() {
        for (compressed_column, &column) in active.iter().enumerate() {
            let (rational, sqrt2, float) = match matrix {
                ParsedGram::Rational(values) => {
                    (&values[row][column], None, values[row][column].to_f64()?)
                }
                ParsedGram::Quadratic(values) => (
                    &values[row][column].rational,
                    Some(&values[row][column].sqrt2),
                    values[row][column].to_f64()?,
                ),
            };
            if !float.is_finite() {
                return None;
            }
            floating[(compressed_row, compressed_column)] = float;
            let sqrt2 = sqrt2.cloned().unwrap_or_else(BigRational::zero);
            exact_denominator = exact_denominator.lcm(rational.denom()).lcm(sqrt2.denom());
            exact.push(ExactQsqrt2 {
                rational: rational.clone(),
                sqrt2,
            });
        }
    }

    let lambda_estimate = floating
        .clone()
        .symmetric_eigen()
        .eigenvalues
        .iter()
        .copied()
        .fold(f64::INFINITY, f64::min);
    if !lambda_estimate.is_finite() || lambda_estimate <= 0.0 {
        return None;
    }
    let delta_float = lambda_estimate / 2.0;
    if !delta_float.is_finite() || delta_float <= 0.0 {
        return None;
    }
    let delta = Dyadic::from_f64(delta_float)?;
    let mut factor_denominator_bits = delta.denominator_bits;
    let mut shifted = floating;
    for index in 0..compressed_dimension {
        shifted[(index, index)] -= delta_float;
    }
    let cholesky = shifted.cholesky()?;
    let factor = cholesky.l();
    let mut exact_factor = vec![vec![Dyadic::zero(); compressed_dimension]; compressed_dimension];
    for row in 0..compressed_dimension {
        for column in 0..=row {
            let value = Dyadic::from_f64(factor[(row, column)])?;
            factor_denominator_bits = factor_denominator_bits.max(value.denominator_bits);
            exact_factor[row][column] = value;
        }
    }
    let factor_integers = exact_factor
        .iter()
        .map(|row| {
            row.iter()
                .map(|value| value.scaled_numerator(factor_denominator_bits))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let factor_product_denominator_bits = factor_denominator_bits.checked_mul(2)?;
    let factor_product_denominator = BigInt::one() << factor_product_denominator_bits;
    let residual_denominator = exact_denominator.lcm(&factor_product_denominator);
    let factor_product_multiplier = &residual_denominator / factor_product_denominator;
    let delta_integer =
        delta.scaled_numerator(factor_product_denominator_bits) * &factor_product_multiplier;
    if !delta_integer.is_positive() {
        return None;
    }
    let sqrt2_denominator = BigInt::from(SQRT2_ENCLOSURE_DENOMINATOR);
    let sqrt2_lower = BigInt::from(SQRT2_ENCLOSURE_LOWER_NUMERATOR);
    let sqrt2_upper = BigInt::from(SQRT2_ENCLOSURE_UPPER_NUMERATOR);
    let mut row_residual_upper_numerators = vec![BigInt::zero(); compressed_dimension];
    for row in 0..compressed_dimension {
        for column in 0..=row {
            let entry = &exact[row * compressed_dimension + column];
            let mut rational =
                entry.rational.numer() * (&residual_denominator / entry.rational.denom());
            if row == column {
                rational -= &delta_integer;
            }
            let mut factor_product = BigInt::zero();
            for (row_value, column_value) in factor_integers[row][..=column]
                .iter()
                .zip(&factor_integers[column][..=column])
            {
                factor_product += row_value * column_value;
            }
            rational -= factor_product * &factor_product_multiplier;
            let sqrt2 = entry.sqrt2.numer() * (&residual_denominator / entry.sqrt2.denom());
            let lower_value = (&rational * &sqrt2_denominator + &sqrt2 * &sqrt2_lower).abs();
            let upper_value = (&rational * &sqrt2_denominator + &sqrt2 * &sqrt2_upper).abs();
            let absolute_upper = lower_value.max(upper_value);
            row_residual_upper_numerators[row] += &absolute_upper;
            if row != column {
                row_residual_upper_numerators[column] += absolute_upper;
            }
        }
    }
    let strict_threshold = &delta_integer * &sqrt2_denominator;
    if row_residual_upper_numerators
        .iter()
        .any(|row_sum| row_sum >= &strict_threshold)
    {
        return None;
    }
    let maximum_row_residual = row_residual_upper_numerators.into_iter().max()?;
    let margin_numerator = strict_threshold - maximum_row_residual;
    let margin_denominator = residual_denominator * sqrt2_denominator;
    Some(ResidualGramCertificate {
        minimum_eigenvalue_lower_bound: BigRational::new(margin_numerator, margin_denominator),
        removed_zero_rows: dimension - compressed_dimension,
    })
}

/// In-place exact LDL^T; only the lower triangle is overwritten with `L`.
fn positive_ldl_minimum(
    block: usize,
    matrix: &mut [Vec<BigQsqrt2>],
) -> Result<BigQsqrt2, ExactAuditError> {
    let dimension = matrix.len();
    let mut pivots = Vec::with_capacity(dimension);
    let mut minimum: Option<BigQsqrt2> = None;
    for column in 0..dimension {
        let mut used = BigQsqrt2::zero();
        for previous in 0..column {
            let square = matrix[column][previous].mul(&matrix[column][previous]);
            used = used.add(&square.mul(&pivots[previous]));
        }
        let pivot = matrix[column][column].sub(&used);
        if !pivot.is_positive() {
            return Err(ExactAuditError::GramPivot {
                block,
                pivot: column,
                value: pivot.to_string(),
            });
        }
        if minimum
            .as_ref()
            .is_none_or(|current| current.sub(&pivot).is_positive())
        {
            minimum = Some(pivot.clone());
        }
        for row in (column + 1)..dimension {
            let mut used = BigQsqrt2::zero();
            for previous in 0..column {
                let product = matrix[row][previous].mul(&matrix[column][previous]);
                used = used.add(&product.mul(&pivots[previous]));
            }
            matrix[row][column] = matrix[row][column].sub(&used).div(&pivot)?;
        }
        pivots.push(pivot);
    }
    Ok(minimum.expect("certificate Gram blocks are nonempty"))
}

/// Fast path for the overwhelmingly common case where a Gram is rational.
fn positive_rational_ldl_minimum(
    block: usize,
    matrix: &mut [Vec<BigRational>],
) -> Result<BigRational, ExactAuditError> {
    let dimension = matrix.len();
    let mut pivots = Vec::with_capacity(dimension);
    let mut minimum: Option<BigRational> = None;
    for column in 0..dimension {
        let mut used = BigRational::zero();
        for previous in 0..column {
            used += &matrix[column][previous] * &matrix[column][previous] * &pivots[previous];
        }
        let pivot = &matrix[column][column] - used;
        if !pivot.is_positive() {
            return Err(ExactAuditError::GramPivot {
                block,
                pivot: column,
                value: pivot.to_string(),
            });
        }
        if minimum.as_ref().is_none_or(|current| current > &pivot) {
            minimum = Some(pivot.clone());
        }
        for row in (column + 1)..dimension {
            let mut used = BigRational::zero();
            for previous in 0..column {
                used += &matrix[row][previous] * &matrix[column][previous] * &pivots[previous];
            }
            matrix[row][column] = (&matrix[row][column] - used) / &pivot;
        }
        pivots.push(pivot);
    }
    Ok(minimum.expect("certificate Gram blocks are nonempty"))
}

impl ParsedGram {
    fn positive_certificate(
        &mut self,
        block: usize,
    ) -> Result<PositiveGramCertificate, ExactAuditError> {
        if let Some(certificate) = residual_gram_certificate(self)
            && certificate.removed_zero_rows == 0
        {
            return Ok(PositiveGramCertificate::Residual(certificate));
        }
        self.positive_ldl_minimum(block)
            .map(PositiveGramCertificate::ExactLdl)
    }

    fn positive_ldl_minimum(&mut self, block: usize) -> Result<BigQsqrt2, ExactAuditError> {
        match self {
            Self::Rational(matrix) => {
                positive_rational_ldl_minimum(block, matrix).map(BigQsqrt2::from_rational)
            }
            Self::Quadratic(matrix) => positive_ldl_minimum(block, matrix),
        }
    }

    fn entry_times_small(&self, row: usize, column: usize, scalar: Qsqrt2) -> BigQsqrt2 {
        match self {
            Self::Rational(matrix) => {
                let entry = &matrix[row][column];
                let scalar = BigQsqrt2::from_small(scalar);
                BigQsqrt2 {
                    rational: entry * scalar.rational,
                    sqrt2: entry * scalar.sqrt2,
                }
            }
            Self::Quadratic(matrix) => matrix[row][column].mul_small(scalar),
        }
    }

    fn entry_is_zero(&self, row: usize, column: usize) -> bool {
        match self {
            Self::Rational(matrix) => matrix[row][column].is_zero(),
            Self::Quadratic(matrix) => matrix[row][column].is_zero(),
        }
    }

    fn is_zero_matrix(&self) -> bool {
        match self {
            Self::Rational(matrix) => matrix.iter().flatten().all(Zero::is_zero),
            Self::Quadratic(matrix) => matrix.iter().flatten().all(BigQsqrt2::is_zero),
        }
    }
}

fn add_assign(target: &mut BigQsqrt2, value: &BigQsqrt2) {
    target.rational += &value.rational;
    target.sqrt2 += &value.sqrt2;
}

fn sub_assign(target: &mut BigQsqrt2, value: &BigQsqrt2) {
    target.rational -= &value.rational;
    target.sqrt2 -= &value.sqrt2;
}

fn reconstructed_identity(
    model: &crate::stationary_torus::ExactCertificateModel,
    multipliers: &[BigQsqrt2],
    grams: &[Vec<Vec<String>>],
) -> Result<Vec<BigQsqrt2>, ExactAuditError> {
    let mut identity = vec![BigQsqrt2::zero(); model.coefficient_count()];
    for &(position, coefficient) in &model.cost {
        add_assign(&mut identity[position], &BigQsqrt2::from_small(coefficient));
    }
    for (multiplier, row) in multipliers.iter().zip(&model.equalities) {
        for &(position, coefficient) in &row.coefficients {
            add_assign(&mut identity[position], &multiplier.mul_small(coefficient));
        }
    }
    for (block_index, encoded) in grams.iter().enumerate() {
        let matrix = parse_matrix(block_index, encoded, model.gram_dimensions()[block_index])?;
        let dimension = model.gram_dimensions()[block_index];
        for row in 0..dimension {
            for column in row..dimension {
                if matrix.entry_is_zero(row, column) {
                    continue;
                }
                model.for_each_gram_entry_coefficient(
                    block_index,
                    row,
                    column,
                    |position, coefficient| {
                        sub_assign(
                            &mut identity[position],
                            &matrix.entry_times_small(row, column, coefficient),
                        );
                    },
                );
                if row != column {
                    model.for_each_gram_entry_coefficient(
                        block_index,
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
    Ok(identity)
}

/// Exactly adjust equality multipliers so the residual has no constant or
/// linear Rydberg terms. This is required before a free-time residual can be
/// bounded relative to the quadratic running cost.
#[allow(clippy::needless_range_loop)]
pub fn repair_low_degree_residual(
    certificate: &mut ExactDualCertificate,
) -> Result<(), ExactAuditError> {
    let model = exact_certificate_model(certificate.order).map_err(ExactAuditError::Model)?;
    let mut multipliers = certificate
        .equalities
        .iter()
        .map(|value| ScalarParser::parse(value))
        .collect::<Result<Vec<_>, _>>()?;
    let identity = reconstructed_identity(&model, &multipliers, &certificate.grams)?;
    let positions = (0..model.coefficient_count())
        .filter(|&position| model.rydberg_degree(position) < 2)
        .collect::<Vec<_>>();
    let columns = multipliers.len();
    let mut system = positions
        .iter()
        .map(|&position| {
            let mut row = vec![BigQsqrt2::zero(); columns + 1];
            for (column, equality) in model.equalities.iter().enumerate() {
                if let Some((_, coefficient)) = equality
                    .coefficients
                    .iter()
                    .find(|&&(candidate, _)| candidate == position)
                {
                    row[column] = BigQsqrt2::from_small(*coefficient);
                }
            }
            row[columns] = identity[position].neg();
            row
        })
        .collect::<Vec<_>>();

    let mut pivot_row = 0;
    let mut pivots = Vec::new();
    for column in 0..columns {
        let Some(found) = (pivot_row..system.len()).find(|&row| !system[row][column].is_zero())
        else {
            continue;
        };
        system.swap(pivot_row, found);
        let pivot = system[pivot_row][column].clone();
        for entry in column..=columns {
            system[pivot_row][entry] = system[pivot_row][entry].div(&pivot)?;
        }
        for row in 0..system.len() {
            if row == pivot_row || system[row][column].is_zero() {
                continue;
            }
            let factor = system[row][column].clone();
            for entry in column..=columns {
                system[row][entry] = system[row][entry].sub(&factor.mul(&system[pivot_row][entry]));
            }
        }
        pivots.push(column);
        pivot_row += 1;
        if pivot_row == system.len() {
            break;
        }
    }
    if system[pivot_row..]
        .iter()
        .any(|row| row[..columns].iter().all(BigQsqrt2::is_zero) && !row[columns].is_zero())
    {
        return Err(ExactAuditError::ResidualRepair);
    }
    for (row, &column) in pivots.iter().enumerate() {
        multipliers[column] = multipliers[column].add(&system[row][columns]);
    }
    certificate.equalities = multipliers.iter().map(ToString::to_string).collect();
    let repaired = reconstructed_identity(&model, &multipliers, &certificate.grams)?;
    if repaired
        .iter()
        .enumerate()
        .any(|(position, value)| model.rydberg_degree(position) < 2 && !value.is_zero())
    {
        return Err(ExactAuditError::ResidualRepair);
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum RepairVariable {
    Equality(usize),
    Gram {
        block: usize,
        row: usize,
        column: usize,
    },
}

/// Project a rounded dual back onto the exact coefficient-identity affine
/// space using equality multipliers and Gram diagonal entries.
#[allow(clippy::needless_range_loop)]
pub fn repair_exact_identity(
    certificate: &mut ExactDualCertificate,
) -> Result<(), ExactAuditError> {
    let model = exact_certificate_model(certificate.order).map_err(ExactAuditError::Model)?;
    let mut multipliers = certificate
        .equalities
        .iter()
        .map(|value| ScalarParser::parse(value))
        .collect::<Result<Vec<_>, _>>()?;
    let identity = reconstructed_identity(&model, &multipliers, &certificate.grams)?;
    let rows = model.coefficient_count();
    let mut variables = Vec::new();
    let mut columns = Vec::<BTreeMap<usize, BigQsqrt2>>::new();
    for (equality_index, equality) in model.equalities.iter().enumerate() {
        variables.push(RepairVariable::Equality(equality_index));
        columns.push(
            equality
                .coefficients
                .iter()
                .map(|&(position, value)| (position, BigQsqrt2::from_small(value)))
                .collect(),
        );
    }
    for (block, dimension) in model.gram_dimensions().into_iter().enumerate() {
        for row in 0..dimension {
            for column_index in row..dimension {
                let mut coefficients = BTreeMap::new();
                model.for_each_gram_entry_coefficient(
                    block,
                    row,
                    column_index,
                    |position, value| {
                        let value = BigQsqrt2::from_small(value).neg();
                        add_assign(
                            coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
                            &value,
                        );
                    },
                );
                if row != column_index {
                    model.for_each_gram_entry_coefficient(
                        block,
                        column_index,
                        row,
                        |position, value| {
                            let value = BigQsqrt2::from_small(value).neg();
                            add_assign(
                                coefficients.entry(position).or_insert_with(BigQsqrt2::zero),
                                &value,
                            );
                        },
                    );
                }
                variables.push(RepairVariable::Gram {
                    block,
                    row,
                    column: column_index,
                });
                columns.push(coefficients);
            }
        }
    }
    // Rank-revealing floating elimination chooses a compact column basis; the
    // actual repair below is still performed and checked entirely exactly.
    let mut selected = Vec::new();
    let mut numeric_basis: Vec<Vec<f64>> = Vec::new();
    for (candidate, column) in columns.iter().enumerate() {
        let mut vector = vec![0.0; rows];
        for (&row, value) in column {
            vector[row] = value.to_f64().ok_or(ExactAuditError::ResidualRepair)?;
        }
        for (&(pivot, _), basis) in selected.iter().zip(&numeric_basis) {
            let factor = vector[pivot];
            if factor != 0.0 {
                for row in 0..rows {
                    vector[row] -= factor * basis[row];
                }
            }
        }
        let Some((pivot, magnitude)) = vector
            .iter()
            .enumerate()
            .map(|(row, value)| (row, value.abs()))
            .max_by(|left, right| left.1.total_cmp(&right.1))
        else {
            continue;
        };
        if magnitude <= 1e-9 {
            continue;
        }
        let scale = vector[pivot];
        for value in &mut vector {
            *value /= scale;
        }
        selected.push((pivot, candidate));
        numeric_basis.push(vector);
    }
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
            values.push(identity[row].neg());
            values
        })
        .collect::<Vec<_>>();
    for column in 0..rank {
        let found = (column..rank)
            .find(|&row| !system[row][column].is_zero())
            .ok_or(ExactAuditError::ResidualRepair)?;
        system.swap(column, found);
        let pivot = system[column][column].clone();
        for entry in column..=rank {
            system[column][entry] = system[column][entry].div(&pivot)?;
        }
        for row in 0..rank {
            if row == column || system[row][column].is_zero() {
                continue;
            }
            let factor = system[row][column].clone();
            for entry in column..=rank {
                system[row][entry] = system[row][entry].sub(&factor.mul(&system[column][entry]));
            }
        }
    }
    for (column, &(_, candidate)) in selected.iter().enumerate() {
        let correction = &system[column][rank];
        match variables[candidate] {
            RepairVariable::Equality(index) => {
                multipliers[index] = multipliers[index].add(correction);
            }
            RepairVariable::Gram { block, row, column } => {
                let current = ScalarParser::parse(&certificate.grams[block][row][column])?;
                let repaired = current.add(correction).to_string();
                certificate.grams[block][row][column] = repaired.clone();
                certificate.grams[block][column][row] = repaired;
            }
        }
    }
    certificate.equalities = multipliers.iter().map(ToString::to_string).collect();
    if reconstructed_identity(&model, &multipliers, &certificate.grams)?
        .iter()
        .any(|value| !value.is_zero())
    {
        return Err(ExactAuditError::ResidualRepair);
    }
    Ok(())
}

/// Return the number of nonzero low-degree terms and the same conservative
/// rational coefficient upper used by the cost-relative auditor.
pub fn residual_diagnostics(
    certificate: &ExactDualCertificate,
) -> Result<(usize, String), ExactAuditError> {
    let model = exact_certificate_model(certificate.order).map_err(ExactAuditError::Model)?;
    let multipliers = certificate
        .equalities
        .iter()
        .map(|value| ScalarParser::parse(value))
        .collect::<Result<Vec<_>, _>>()?;
    let identity = reconstructed_identity(&model, &multipliers, &certificate.grams)?;
    let low_degree = identity
        .iter()
        .enumerate()
        .filter(|(position, value)| model.rydberg_degree(*position) < 2 && !value.is_zero())
        .count();
    let upper = identity.iter().fold(BigRational::zero(), |sum, value| {
        sum + BigRational::from_integer(BigInt::from(8)) * value.absolute_upper()
    });
    Ok((low_degree, upper.to_string()))
}

/// Blend an exact feasible interior seed with a rounded discovery dual. The
/// returned metadata and target come from `candidate`.
pub fn blend_with_exact_seed(
    seed: &ExactDualCertificate,
    candidate: &mut ExactDualCertificate,
    numerator: i128,
    denominator: i128,
) -> Result<(), ExactAuditError> {
    if denominator <= 0 || numerator < 0 || numerator > denominator {
        return Err(ExactAuditError::ResidualRepair);
    }
    if seed.order != candidate.order
        || seed.equalities.len() != candidate.equalities.len()
        || seed.grams.len() != candidate.grams.len()
    {
        return Err(ExactAuditError::ResidualRepair);
    }
    let alpha = BigQsqrt2::from_rational(BigRational::new(
        BigInt::from(numerator),
        BigInt::from(denominator),
    ));
    let one_minus = BigQsqrt2::from_rational(BigRational::new(
        BigInt::from(denominator - numerator),
        BigInt::from(denominator),
    ));
    let blend = |left: &str, right: &str| -> Result<String, ExactAuditError> {
        Ok(ScalarParser::parse(left)?
            .mul(&one_minus)
            .add(&ScalarParser::parse(right)?.mul(&alpha))
            .to_string())
    };
    candidate.equalities = seed
        .equalities
        .iter()
        .zip(&candidate.equalities)
        .map(|(left, right)| blend(left, right))
        .collect::<Result<Vec<_>, _>>()?;
    for (seed_block, candidate_block) in seed.grams.iter().zip(&mut candidate.grams) {
        if seed_block.len() != candidate_block.len() {
            return Err(ExactAuditError::ResidualRepair);
        }
        for (seed_row, candidate_row) in seed_block.iter().zip(candidate_block) {
            if seed_row.len() != candidate_row.len() {
                return Err(ExactAuditError::ResidualRepair);
            }
            for (left, right) in seed_row.iter().zip(candidate_row) {
                *right = blend(left, right)?;
            }
        }
    }
    Ok(())
}

pub fn audit_exact_certificate(
    certificate: &ExactDualCertificate,
) -> Result<ExactAuditReport, ExactAuditError> {
    audit_exact_certificate_inner(certificate)
}

/// Audit with an explicit number of independent Gram-checking workers.
pub fn audit_exact_certificate_with_jobs(
    certificate: &ExactDualCertificate,
    jobs: usize,
) -> Result<ExactAuditReport, ExactAuditError> {
    if jobs == 0 {
        return Err(ExactAuditError::AuditJobs);
    }
    rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .map_err(|error| ExactAuditError::ThreadPool(error.to_string()))?
        .install(|| audit_exact_certificate_inner(certificate))
}

fn audit_exact_certificate_inner(
    certificate: &ExactDualCertificate,
) -> Result<ExactAuditReport, ExactAuditError> {
    if certificate.schema == HAUSDORFF_SCHEMA_V1 {
        return audit_hausdorff_certificate_inner(certificate);
    }
    if certificate.schema != EXACT_SCHEMA_V1 && certificate.schema != EXACT_SCHEMA_V2 {
        return Err(ExactAuditError::Schema(certificate.schema.clone()));
    }
    let model = exact_certificate_model(certificate.order).map_err(ExactAuditError::Model)?;
    let cost_relative = certificate.schema == EXACT_SCHEMA_V2;
    if cost_relative {
        if certificate.residual_policy.as_deref() != Some("cost_relative") {
            return Err(ExactAuditError::ResidualPolicy);
        }
        let expected = crate::stationary_torus::structure(certificate.order)
            .map_err(ExactAuditError::Model)?
            .formulation_hash;
        let found = certificate.formulation_hash.clone().unwrap_or_default();
        if found != expected {
            return Err(ExactAuditError::FormulationHash { found, expected });
        }
    }
    if certificate.equalities.len() != model.equalities.len() {
        return Err(ExactAuditError::EqualityCount {
            expected: model.equalities.len(),
            found: certificate.equalities.len(),
        });
    }
    let dimensions = model.gram_dimensions();
    if certificate.grams.len() != dimensions.len() {
        return Err(ExactAuditError::GramCount {
            expected: dimensions.len(),
            found: certificate.grams.len(),
        });
    }

    let multipliers = certificate
        .equalities
        .iter()
        .map(|value| ScalarParser::parse(value))
        .collect::<Result<Vec<_>, _>>()?;
    let target = ScalarParser::parse(&certificate.bound_target)?;
    let mut bound = BigQsqrt2::zero();
    let mut identity = vec![BigQsqrt2::zero(); model.coefficient_count()];
    for &(position, coefficient) in &model.cost {
        add_assign(&mut identity[position], &BigQsqrt2::from_small(coefficient));
    }
    for (multiplier, row) in multipliers.iter().zip(&model.equalities) {
        add_assign(
            &mut bound,
            &multiplier.mul(&BigQsqrt2::from_rational(BigRational::from_integer(
                BigInt::from(row.endpoint),
            ))),
        );
        for &(position, coefficient) in &row.coefficients {
            add_assign(&mut identity[position], &multiplier.mul_small(coefficient));
        }
    }

    let identity = Mutex::new(identity);
    let minimum_pivot = Mutex::new(None::<BigQsqrt2>);
    let minimum_residual_bound = Mutex::new(None::<BigRational>);
    let residual_certified_count = Mutex::new(0_usize);
    let exact_ldl_certified_count = Mutex::new(0_usize);
    certificate.grams.par_iter().enumerate().try_for_each(
        |(block_index, encoded)| -> Result<(), ExactAuditError> {
            let dimension = dimensions[block_index];
            let mut matrix = parse_matrix(block_index, encoded, dimension)?;
            match matrix.positive_certificate(block_index)? {
                PositiveGramCertificate::Residual(certificate) => {
                    *residual_certified_count
                        .lock()
                        .expect("residual-count mutex is not poisoned") += 1;
                    let mut global = minimum_residual_bound
                        .lock()
                        .expect("minimum-residual-bound mutex is not poisoned");
                    if global
                        .as_ref()
                        .is_none_or(|current| current > &certificate.minimum_eigenvalue_lower_bound)
                    {
                        *global = Some(certificate.minimum_eigenvalue_lower_bound);
                    }
                }
                PositiveGramCertificate::ExactLdl(block_minimum) => {
                    *exact_ldl_certified_count
                        .lock()
                        .expect("exact-LDL-count mutex is not poisoned") += 1;
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
            }
            let mut contribution = BTreeMap::<usize, BigQsqrt2>::new();
            for row in 0..dimension {
                for column in row..dimension {
                    if matrix.entry_is_zero(row, column) {
                        continue;
                    }
                    model.for_each_gram_entry_coefficient(
                        block_index,
                        row,
                        column,
                        |position, coefficient| {
                            let value = matrix.entry_times_small(row, column, coefficient);
                            add_assign(
                                contribution.entry(position).or_insert_with(BigQsqrt2::zero),
                                &value,
                            );
                        },
                    );
                    if row != column {
                        model.for_each_gram_entry_coefficient(
                            block_index,
                            column,
                            row,
                            |position, coefficient| {
                                let value = matrix.entry_times_small(row, column, coefficient);
                                add_assign(
                                    contribution.entry(position).or_insert_with(BigQsqrt2::zero),
                                    &value,
                                );
                            },
                        );
                    }
                }
            }
            {
                let mut global = identity.lock().expect("identity mutex is not poisoned");
                for (position, value) in contribution {
                    sub_assign(&mut global[position], &value);
                }
            }
            Ok(())
        },
    )?;

    let identity = identity
        .into_inner()
        .expect("identity mutex is not poisoned");
    let nonzero = identity.iter().filter(|value| !value.is_zero()).count();
    if !cost_relative && nonzero != 0 {
        return Err(ExactAuditError::Identity { count: nonzero });
    }
    let residual_upper = if cost_relative {
        let mut reconstructed = BigRational::zero();
        for (position, value) in identity.iter().enumerate() {
            if value.is_zero() {
                continue;
            }
            let degree = model.rydberg_degree(position);
            if degree < 2 {
                return Err(ExactAuditError::ResidualDegree { position, degree });
            }
            // A real moment coordinate has magnitude at most twice its
            // monomial. Any monomial with at least two Rydberg factors is at
            // most 4L, hence each coordinate is at most 8L.
            reconstructed += BigRational::from_integer(BigInt::from(8)) * value.absolute_upper();
        }
        let declared_value = certificate
            .residual_upper
            .as_deref()
            .ok_or(ExactAuditError::ResidualPolicy)
            .and_then(ScalarParser::parse)?;
        if !declared_value.sqrt2.is_zero() || declared_value.rational.is_negative() {
            return Err(ExactAuditError::ResidualPolicy);
        }
        if declared_value.rational < reconstructed {
            return Err(ExactAuditError::ResidualUpper {
                declared: declared_value.rational.to_string(),
                reconstructed: reconstructed.to_string(),
            });
        }
        declared_value.rational
    } else {
        BigRational::zero()
    };
    let one_plus_residual = BigQsqrt2::from_rational(BigRational::one() + &residual_upper);
    let required_endpoint = target.mul(&one_plus_residual);
    let difference = bound.sub(&required_endpoint);
    if !difference.is_zero() && !difference.is_positive() {
        return Err(ExactAuditError::Bound {
            bound: bound.to_string(),
            target: required_endpoint.to_string(),
        });
    }
    let rigorous_bound = target.to_f64().ok_or_else(|| {
        ExactAuditError::InvalidScalar("target cannot be represented as f64 for reporting".into())
    })?;
    let minimum_pivot = minimum_pivot
        .into_inner()
        .expect("minimum-pivot mutex is not poisoned");
    let minimum_residual_bound = minimum_residual_bound
        .into_inner()
        .expect("minimum-residual-bound mutex is not poisoned");
    let residual_certified_gram_count = residual_certified_count
        .into_inner()
        .expect("residual-count mutex is not poisoned");
    let exact_ldl_certified_gram_count = exact_ldl_certified_count
        .into_inner()
        .expect("exact-LDL-count mutex is not poisoned");
    Ok(ExactAuditReport {
        sign_convention: "c + A^T lambda - S^T Z = 0",
        coefficient_count: model.coefficient_count(),
        nonzero_exact_residual_count: nonzero,
        all_gram_matrices_exactly_positive_definite: true,
        all_gram_matrices_exactly_positive_semidefinite: true,
        positive_definite_gram_count: dimensions.len(),
        zero_gram_count: 0,
        residual_certified_gram_count,
        exact_ldl_certified_gram_count,
        minimum_certified_gram_eigenvalue_lower_bound: minimum_residual_bound.map_or_else(
            || "not applicable (no Gram matrix used residual certification)".into(),
            |value| value.to_string(),
        ),
        minimum_exact_ldl_pivot: minimum_pivot.map_or_else(
            || "not applicable (no Gram matrix required exact LDL)".into(),
            |value| value.to_string(),
        ),
        exact_endpoint_bound: bound.to_string(),
        cost_relative_residual_upper: residual_upper.to_string(),
        certified_bound: target.to_string(),
        endpoint_margin_after_residual: difference.to_string(),
        strictly_exceeds_target: !difference.is_zero(),
        rigorous_bound,
    })
}

fn audit_hausdorff_certificate_inner(
    certificate: &ExactDualCertificate,
) -> Result<ExactAuditReport, ExactAuditError> {
    let exposure_upper = certificate
        .exposure_upper
        .as_deref()
        .ok_or(ExactAuditError::ExposureUpper)
        .and_then(ScalarParser::parse)?;
    let expected_upper = BigQsqrt2::from_rational(BigRational::new(
        BigInt::from(2_935_887_i64),
        BigInt::from(1_000_000_i64),
    ));
    if exposure_upper != expected_upper {
        return Err(ExactAuditError::ExposureUpper);
    }
    let model = crate::stationary_hausdorff::exact_certificate_model(certificate.order)
        .map_err(ExactAuditError::Model)?;
    if certificate.equalities.len() != model.equalities.len() {
        return Err(ExactAuditError::EqualityCount {
            expected: model.equalities.len(),
            found: certificate.equalities.len(),
        });
    }
    if certificate.occupation_grams.len() != model.occupation_gram_count()
        || certificate.terminal_grams.len() != 2
    {
        return Err(ExactAuditError::GramCount {
            expected: model.gram_dimensions().len(),
            found: certificate.occupation_grams.len() + certificate.terminal_grams.len(),
        });
    }
    let dimensions = model.gram_dimensions();
    let encoded_grams = certificate
        .occupation_grams
        .iter()
        .chain(&certificate.terminal_grams)
        .collect::<Vec<_>>();
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
    let target = ScalarParser::parse(&certificate.bound_target)?;
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

    let identity = Mutex::new(identity);
    let minimum_pivot = Mutex::new(None::<BigQsqrt2>);
    let minimum_residual_bound = Mutex::new(None::<BigRational>);
    let residual_certified_count = Mutex::new(0_usize);
    let exact_ldl_certified_count = Mutex::new(0_usize);
    let positive_count = Mutex::new(0_usize);
    let zero_count = Mutex::new(0_usize);
    encoded_grams.par_iter().enumerate().try_for_each(
        |(block_index, encoded)| -> Result<(), ExactAuditError> {
            let dimension = dimensions[block_index];
            let mut matrix = parse_matrix(block_index, encoded, dimension)?;
            if matrix.is_zero_matrix() {
                *zero_count.lock().expect("zero-count mutex is not poisoned") += 1;
                return Ok(());
            }
            match matrix.positive_certificate(block_index)? {
                PositiveGramCertificate::Residual(certificate) => {
                    *residual_certified_count
                        .lock()
                        .expect("residual-count mutex is not poisoned") += 1;
                    let mut global = minimum_residual_bound
                        .lock()
                        .expect("minimum-residual-bound mutex is not poisoned");
                    if global
                        .as_ref()
                        .is_none_or(|current| current > &certificate.minimum_eigenvalue_lower_bound)
                    {
                        *global = Some(certificate.minimum_eigenvalue_lower_bound);
                    }
                }
                PositiveGramCertificate::ExactLdl(block_minimum) => {
                    *exact_ldl_certified_count
                        .lock()
                        .expect("exact-LDL-count mutex is not poisoned") += 1;
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
            }
            *positive_count
                .lock()
                .expect("positive-count mutex is not poisoned") += 1;
            let mut contribution = BTreeMap::<usize, BigQsqrt2>::new();
            for row in 0..dimension {
                for column in row..dimension {
                    if matrix.entry_is_zero(row, column) {
                        continue;
                    }
                    model.for_each_gram_entry_coefficient(
                        block_index,
                        row,
                        column,
                        |position, coefficient| {
                            let value = matrix.entry_times_small(row, column, coefficient);
                            add_assign(
                                contribution.entry(position).or_insert_with(BigQsqrt2::zero),
                                &value,
                            );
                        },
                    );
                    if row != column {
                        model.for_each_gram_entry_coefficient(
                            block_index,
                            column,
                            row,
                            |position, coefficient| {
                                let value = matrix.entry_times_small(row, column, coefficient);
                                add_assign(
                                    contribution.entry(position).or_insert_with(BigQsqrt2::zero),
                                    &value,
                                );
                            },
                        );
                    }
                }
            }
            {
                let mut global = identity.lock().expect("identity mutex is not poisoned");
                for (position, value) in contribution {
                    sub_assign(&mut global[position], &value);
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
        return Err(ExactAuditError::Identity { count: nonzero });
    }
    let difference = bound.sub(&target);
    if !difference.is_zero() && !difference.is_positive() {
        return Err(ExactAuditError::Bound {
            bound: bound.to_string(),
            target: target.to_string(),
        });
    }
    let rigorous_bound = target.to_f64().ok_or_else(|| {
        ExactAuditError::InvalidScalar("target cannot be represented as f64 for reporting".into())
    })?;
    let minimum_pivot = minimum_pivot
        .into_inner()
        .expect("minimum-pivot mutex is not poisoned");
    let minimum_residual_bound = minimum_residual_bound
        .into_inner()
        .expect("minimum-residual-bound mutex is not poisoned");
    let residual_certified_gram_count = residual_certified_count
        .into_inner()
        .expect("residual-count mutex is not poisoned");
    let exact_ldl_certified_gram_count = exact_ldl_certified_count
        .into_inner()
        .expect("exact-LDL-count mutex is not poisoned");
    let positive_definite_gram_count = positive_count
        .into_inner()
        .expect("positive-count mutex is not poisoned");
    let zero_gram_count = zero_count
        .into_inner()
        .expect("zero-count mutex is not poisoned");
    Ok(ExactAuditReport {
        sign_convention: "c + A^T lambda + n*terminal[0] - S^T Z = 0; bound=sum(lambda*initial)-n",
        coefficient_count: model.coefficient_count(),
        nonzero_exact_residual_count: 0,
        all_gram_matrices_exactly_positive_definite: zero_gram_count == 0,
        all_gram_matrices_exactly_positive_semidefinite: true,
        positive_definite_gram_count,
        zero_gram_count,
        residual_certified_gram_count,
        exact_ldl_certified_gram_count,
        minimum_certified_gram_eigenvalue_lower_bound: minimum_residual_bound.map_or_else(
            || "not applicable (no Gram matrix used residual certification)".into(),
            |value| value.to_string(),
        ),
        minimum_exact_ldl_pivot: minimum_pivot.map_or_else(
            || "not applicable (no Gram matrix required exact LDL)".into(),
            |value| value.to_string(),
        ),
        exact_endpoint_bound: bound.to_string(),
        cost_relative_residual_upper: "0".into(),
        certified_bound: target.to_string(),
        endpoint_margin_after_residual: difference.to_string(),
        strictly_exceeds_target: !difference.is_zero(),
        rigorous_bound,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_exact_certificate_scalar_language() {
        assert_eq!(
            ScalarParser::parse(
                "-2382032905087/2000000000000 + 3566489411307*sqrt(2)/2000000000000"
            )
            .unwrap(),
            BigQsqrt2 {
                rational: BigRational::new(
                    BigInt::from(-2_382_032_905_087_i64),
                    BigInt::from(2_000_000_000_000_i64),
                ),
                sqrt2: BigRational::new(
                    BigInt::from(3_566_489_411_307_i64),
                    BigInt::from(2_000_000_000_000_i64),
                ),
            }
        );
        assert_eq!(
            ScalarParser::parse("5.78466550000000e-5").unwrap(),
            BigQsqrt2::from_rational(BigRational::new(
                BigInt::from(11_569_331_i64),
                BigInt::from(200_000_000_000_i64),
            ))
        );
    }

    #[test]
    fn rejects_malformed_or_overflowing_scientific_exponents() {
        for input in ["1e-+2", "1.00e-2147483647"] {
            assert!(ScalarParser::parse(input).is_err(), "accepted {input}");
        }
        for (input, expected) in [("1.25e+2", "125"), ("1.25e-2", "1/80")] {
            assert_eq!(
                ScalarParser::parse(input).unwrap(),
                ScalarParser::parse(expected).unwrap()
            );
        }
    }

    #[test]
    fn decides_quadratic_surd_sign_exactly() {
        assert!(ScalarParser::parse("-1 + sqrt(2)").unwrap().is_positive());
        assert!(!ScalarParser::parse("1 - sqrt(2)").unwrap().is_positive());
        assert!(ScalarParser::parse("3 - 2*sqrt(2)").unwrap().is_positive());
    }

    #[test]
    fn source_order_matches_order_five_certificate_layout() {
        let model = exact_certificate_model(5).unwrap();
        assert_eq!(model.coefficient_count(), 273);
        assert_eq!(model.equalities.len(), 66);
        assert_eq!(model.gram_dimensions().len(), 79);
        assert_eq!(
            &model.gram_dimensions()[..8],
            &[39, 36, 37, 26, 27, 28, 32, 30]
        );
    }

    fn order_five_certificate() -> ExactDualCertificate {
        serde_json::from_str(include_str!(
            "../../../certificates/jan22-cz-exposure-order5-exact-dual.json"
        ))
        .unwrap()
    }

    fn order_five_hausdorff_certificate() -> ExactDualCertificate {
        serde_json::from_str(include_str!(
            "../../../certificates/jan22-cz-exposure-cost-lifted-order5-exact-dual.json"
        ))
        .unwrap()
    }

    fn imported_certificates() -> Vec<ExactDualCertificate> {
        [
            include_str!("../../../certificates/jan22-cz-exposure-order4-exact-dual.json"),
            include_str!("../../../certificates/jan22-cz-exposure-order5-exact-dual.json"),
            include_str!("../../../certificates/jan22-cz-exposure-order6-exact-dual.json"),
            include_str!("../../../certificates/jan22-cz-exposure-order7-exact-dual.json"),
            include_str!("../../../certificates/jan22-cz-exposure-order8-exact-dual.json"),
        ]
        .into_iter()
        .map(|encoded| serde_json::from_str(encoded).unwrap())
        .collect()
    }

    #[test]
    fn imported_exact_certificates_have_expected_targets_and_layouts() {
        let certificates = imported_certificates();
        for (certificate, order, target, coefficients, equalities, grams) in [
            (&certificates[0], 4, "27/10", 118, 32, 51),
            (&certificates[1], 5, "14/5", 273, 66, 79),
            (&certificates[2], 6, "71/25", 561, 120, 113),
            (&certificates[3], 7, "143/50", 1054, 203, 153),
            (&certificates[4], 8, "1153/400", 1854, 326, 199),
        ] {
            assert_eq!(certificate.schema, EXACT_SCHEMA_V1);
            assert_eq!(certificate.order, order);
            assert_eq!(certificate.bound_target, target);
            assert_eq!(certificate.equalities.len(), equalities);
            assert_eq!(certificate.grams.len(), grams);
            assert_eq!(
                exact_certificate_model(order).unwrap().coefficient_count(),
                coefficients
            );
        }
    }

    #[test]
    fn order_five_certificate_proves_280_without_an_optimizer() {
        let certificate = order_five_certificate();
        let report = audit_exact_certificate_with_jobs(&certificate, 1).unwrap();
        assert_eq!(report.coefficient_count, 273);
        assert_eq!(report.nonzero_exact_residual_count, 0);
        assert!(report.all_gram_matrices_exactly_positive_definite);
        assert!(report.strictly_exceeds_target);
        assert_eq!(report.rigorous_bound, 2.8);
        assert_eq!(
            report,
            audit_exact_certificate_with_jobs(&certificate, 2).unwrap()
        );
    }

    #[test]
    fn rejects_a_non_positive_gram_tamper() {
        for mut certificate in imported_certificates() {
            certificate.grams[0][0][0] = "-1".into();
            assert!(matches!(
                audit_exact_certificate_with_jobs(&certificate, 1),
                Err(ExactAuditError::GramPivot { .. })
            ));
        }
    }

    #[test]
    fn rejects_one_coefficient_tamper_in_every_imported_certificate() {
        for mut certificate in imported_certificates() {
            certificate.grams[0][0][1] = "1".into();
            assert!(matches!(
                audit_exact_certificate_with_jobs(&certificate, 1),
                Err(ExactAuditError::GramSymmetry { .. })
            ));
        }
    }

    #[test]
    fn rejects_an_exact_identity_tamper() {
        let mut certificate = order_five_certificate();
        let index = exact_certificate_model(5)
            .unwrap()
            .equalities
            .iter()
            .position(|row| !row.coefficients.is_empty())
            .unwrap();
        certificate.equalities[index] = format!("({}) + 1", certificate.equalities[index]);
        assert!(matches!(
            audit_exact_certificate(&certificate),
            Err(ExactAuditError::Identity { .. })
        ));
    }

    #[test]
    fn rejects_a_target_above_the_exact_bound() {
        let mut certificate = order_five_certificate();
        certificate.bound_target = "3".into();
        assert!(matches!(
            audit_exact_certificate(&certificate),
            Err(ExactAuditError::Bound { .. })
        ));
    }

    #[test]
    fn hausdorff_order_five_certificate_proves_288_and_rejects_tampering() {
        let mut certificate = order_five_hausdorff_certificate();
        let report = audit_exact_certificate_with_jobs(&certificate, 2).unwrap();
        assert_eq!(report.coefficient_count, 752);
        assert_eq!(report.nonzero_exact_residual_count, 0);
        assert!(report.all_gram_matrices_exactly_positive_semidefinite);
        assert!(!report.all_gram_matrices_exactly_positive_definite);
        assert_eq!(report.positive_definite_gram_count, 172);
        assert_eq!(report.zero_gram_count, 92);
        assert_eq!(report.residual_certified_gram_count, 172);
        assert_eq!(report.exact_ldl_certified_gram_count, 0);
        assert!(
            ScalarParser::parse(&report.minimum_certified_gram_eigenvalue_lower_bound)
                .unwrap()
                .is_positive()
        );
        assert_eq!(
            report.minimum_exact_ldl_pivot,
            "not applicable (no Gram matrix required exact LDL)"
        );
        assert_eq!(report.exact_endpoint_bound, "72/25");
        assert_eq!(report.cost_relative_residual_upper, "0");
        assert_eq!(report.certified_bound, "72/25");
        assert_eq!(report.endpoint_margin_after_residual, "0");
        assert_eq!(report.rigorous_bound, 2.88);

        certificate.occupation_grams[0][0][0] = "-1".into();
        assert!(matches!(
            audit_exact_certificate_with_jobs(&certificate, 2),
            Err(ExactAuditError::GramPivot { .. })
        ));
    }
}
