//! Exact assembly of the unrestricted JAN22 ideal-blockade CZ hierarchy.
//!
//! This is a native Rust port of the formulation committed in
//! `Finite_blockade_pulse` at commit `677eba8905756a4dd4d1f0c760b0375ebec67161`.
//! Polynomial and Liouville coefficients are assembled over Q(sqrt(2)); the
//! source Helmert face basis is applied while assembling the floating conic
//! problem at the solver boundary.

use crate::algebra::{Qsqrt2, Rational};
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::monomial::{Exponent, monomials};
use num_complex::Complex64;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Add, Mul, Neg};

const BULK_VARIABLES: usize = 5;
const STATE_VARIABLES: usize = 4;
const U: usize = 0;
const G1: usize = 1;
const R1: usize = 2;
const G2: usize = 3;
const R2: usize = 4;

const BULK_CHARGES: [(i32, i32); BULK_VARIABLES] = [(1, 0), (0, 1), (-1, 1), (0, 2), (-1, 2)];
const STATE_CHARGES: [(i32, i32); STATE_VARIABLES] = [(0, 1), (-1, 1), (0, 2), (-1, 2)];

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct MixedMonomial {
    pub anti: Exponent,
    pub holo: Exponent,
}

impl MixedMonomial {
    fn conjugate(&self) -> Self {
        Self {
            anti: self.holo.clone(),
            holo: self.anti.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ComplexExact {
    pub(crate) re: Qsqrt2,
    pub(crate) im: Qsqrt2,
}

impl ComplexExact {
    pub(crate) const ZERO: Self = Self {
        re: Qsqrt2::ZERO,
        im: Qsqrt2::ZERO,
    };
    pub(crate) const ONE: Self = Self {
        re: Qsqrt2 {
            rational: Rational::ONE,
            sqrt2: Rational::ZERO,
        },
        im: Qsqrt2::ZERO,
    };
    pub(crate) const I: Self = Self {
        re: Qsqrt2::ZERO,
        im: Qsqrt2 {
            rational: Rational::ONE,
            sqrt2: Rational::ZERO,
        },
    };

    pub(crate) fn conjugate(self) -> Self {
        Self {
            re: self.re,
            im: -self.im,
        }
    }

    pub(crate) fn real(value: Qsqrt2) -> Self {
        Self {
            re: value,
            im: Qsqrt2::ZERO,
        }
    }
}

impl Add for ComplexExact {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl Neg for ComplexExact {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            re: -self.re,
            im: -self.im,
        }
    }
}

impl Mul for ComplexExact {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }
}

type Charge = (i32, i32);
type Polynomial = BTreeMap<MixedMonomial, ComplexExact>;

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct StationaryTorusStructure {
    pub order: u8,
    pub maximum_moment_degree: u8,
    pub moment_count: usize,
    pub liouville_equality_count: usize,
    pub psd_block_sides: Vec<usize>,
    pub largest_psd_side: usize,
    pub sum_psd_squares: usize,
    pub sum_psd_cubes: usize,
    pub basis_hash: String,
    pub liouville_basis_hash: String,
    pub formulation_hash: String,
    pub source_repository: &'static str,
    pub source_commit: &'static str,
    pub source_path: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct ArchivedMosekResult {
    pub objective: f64,
    pub iterations: u32,
    pub solve_time_seconds: f64,
    pub reproduction_tolerance: f64,
    pub source_path: &'static str,
}

#[derive(Clone, Debug)]
pub struct StationaryTorusProblem {
    pub structure: StationaryTorusStructure,
    pub conic: ConicProblem,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StrengthenedStationaryTorusStructure {
    #[serde(flatten)]
    pub base: StationaryTorusStructure,
    pub cost_cap: Rational,
    pub cost_weighted_moment_cap_count: usize,
    pub strengthening: &'static str,
}

#[derive(Clone, Debug)]
pub struct StrengthenedStationaryTorusProblem {
    pub structure: StrengthenedStationaryTorusStructure,
    pub conic: ConicProblem,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct GramBlockMetadata {
    pub charge: (i32, i32),
    pub side: usize,
}

pub fn archived_mosek_result(order: u8) -> Option<ArchivedMosekResult> {
    let (objective, iterations, solve_time_seconds) = match order {
        6 => (2.862_459_569_797_198, 20, 3.241_652_637_720_108),
        7 => (2.881_934_186_062_437_7, 24, 5.961_326_554_417_61),
        8 => (2.888_931_017_810_112, 30, 25.634_834_591_299_295),
        9 => (2.898_149_470_676_406_4, 30, 110.393_974_386_155_6),
        10 => (2.901_646_000_244_462, 45, 603.610_483_177_006_2),
        11 => (2.904_745_260_134_998_6, 43, 2_307.975_546_665_489_7),
        _ => return None,
    };
    Some(ArchivedMosekResult {
        objective,
        iterations,
        solve_time_seconds,
        reproduction_tolerance: 1e-4,
        source_path: match order {
            6 => "verification_results/jan22_cz_exposure_stationary_torus_o6_mosek.json",
            7 => "verification_results/jan22_cz_exposure_stationary_torus_o7_mosek.json",
            8 => "verification_results/jan22_cz_exposure_stationary_torus_o8_mosek.json",
            9 => "verification_results/jan22_cz_exposure_stationary_torus_o9_mosek.json",
            10 => "verification_results/jan22_cz_exposure_stationary_torus_o10_mosek.json",
            11 => "verification_results/jan22_cz_exposure_stationary_torus_o11_mosek.json",
            _ => unreachable!(),
        },
    })
}

fn charge(exponent: &Exponent, charges: &[Charge]) -> Charge {
    exponent
        .0
        .iter()
        .zip(charges)
        .fold((0, 0), |sum, (&power, &(first, second))| {
            (
                sum.0 + i32::from(power) * first,
                sum.1 + i32::from(power) * second,
            )
        })
}

fn add_exponents(left: &Exponent, right: &Exponent) -> Exponent {
    Exponent(left.0.iter().zip(&right.0).map(|(&a, &b)| a + b).collect())
}

fn shift(left: &MixedMonomial, right: &MixedMonomial) -> MixedMonomial {
    MixedMonomial {
        anti: add_exponents(&left.anti, &right.anti),
        holo: add_exponents(&left.holo, &right.holo),
    }
}

fn is_normal(key: &MixedMonomial, variables: usize) -> bool {
    let eliminated: &[usize] = if variables == BULK_VARIABLES {
        &[U, G1, G2]
    } else {
        &[0, 2]
    };
    eliminated
        .iter()
        .all(|&index| key.anti.0[index] == 0 || key.holo.0[index] == 0)
}

fn binomial(n: u16, k: u16) -> i64 {
    (0..k).fold(1_i64, |value, index| {
        value * i64::from(n - index) / i64::from(index + 1)
    })
}

fn normal_form(key: &MixedMonomial, variables: usize) -> BTreeMap<MixedMonomial, i64> {
    let mut anti = key.anti.0.clone();
    let mut holo = key.holo.0.clone();
    let sphere_pairs: &[(usize, usize)] = if variables == BULK_VARIABLES {
        let pairs = anti[U].min(holo[U]);
        anti[U] -= pairs;
        holo[U] -= pairs;
        &[(G1, R1), (G2, R2)]
    } else {
        &[(0, 1), (2, 3)]
    };

    let mut paired_powers = Vec::new();
    for &(ground, rydberg) in sphere_pairs {
        let pairs = anti[ground].min(holo[ground]);
        anti[ground] -= pairs;
        holo[ground] -= pairs;
        paired_powers.push((rydberg, pairs));
    }

    let mut result = BTreeMap::from([(
        MixedMonomial {
            anti: Exponent(anti),
            holo: Exponent(holo),
        },
        1_i64,
    )]);
    for (rydberg, pairs) in paired_powers {
        let mut expanded = BTreeMap::new();
        for (reduced, coefficient) in result {
            for power in 0..=pairs {
                let mut next = reduced.clone();
                next.anti.0[rydberg] += power;
                next.holo.0[rydberg] += power;
                let sign = if power % 2 == 0 { 1 } else { -1 };
                *expanded.entry(next).or_insert(0) += coefficient * sign * binomial(pairs, power);
            }
        }
        result = expanded;
    }
    result.retain(|_, coefficient| *coefficient != 0);
    result
}

fn normal_invariant_monomials(
    variables: usize,
    maximum_degree: u16,
    charges: &[Charge],
) -> Vec<MixedMonomial> {
    let through_degree = monomials(variables, maximum_degree);
    let mut result = Vec::new();
    for anti in &through_degree {
        let remaining = maximum_degree - anti.degree();
        let anti_charge = charge(anti, charges);
        for holo in monomials(variables, remaining) {
            let key = MixedMonomial {
                anti: anti.clone(),
                holo,
            };
            if charge(&key.holo, charges) == anti_charge && is_normal(&key, variables) {
                result.push(key);
            }
        }
    }
    result
}

fn normal_mixed_basis(
    variables: usize,
    maximum_degree: u16,
    charges: &[Charge],
) -> BTreeMap<Charge, Vec<MixedMonomial>> {
    let through_degree = monomials(variables, maximum_degree);
    let mut blocks: BTreeMap<Charge, Vec<MixedMonomial>> = BTreeMap::new();
    for anti in &through_degree {
        let remaining = maximum_degree - anti.degree();
        let anti_charge = charge(anti, charges);
        for holo in monomials(variables, remaining) {
            let key = MixedMonomial {
                anti: anti.clone(),
                holo,
            };
            if !is_normal(&key, variables) {
                continue;
            }
            let holo_charge = charge(&key.holo, charges);
            let net = (holo_charge.0 - anti_charge.0, holo_charge.1 - anti_charge.1);
            blocks.entry(net).or_default().push(key);
        }
    }
    blocks.retain(|&(first, second), _| (first, second) <= (-first, -second));
    blocks
}

/// Preserve the insertion order of the Python exact-certificate schema.
///
/// The numerical conic problem is insensitive to PSD block order and uses a
/// `BTreeMap` above. Exact certificate payloads are positional, however, and
/// the reference builder retained the first-seen order of charge blocks.
fn source_order_mixed_basis(
    variables: usize,
    maximum_degree: u16,
    charges: &[Charge],
) -> Vec<(Charge, Vec<MixedMonomial>)> {
    let through_degree = monomials(variables, maximum_degree);
    let mut positions = BTreeMap::new();
    let mut blocks: Vec<(Charge, Vec<MixedMonomial>)> = Vec::new();
    for anti in &through_degree {
        let remaining = maximum_degree - anti.degree();
        let anti_charge = charge(anti, charges);
        for holo in monomials(variables, remaining) {
            let key = MixedMonomial {
                anti: anti.clone(),
                holo,
            };
            if !is_normal(&key, variables) {
                continue;
            }
            let holo_charge = charge(&key.holo, charges);
            let net = (holo_charge.0 - anti_charge.0, holo_charge.1 - anti_charge.1);
            if net > (-net.0, -net.1) {
                continue;
            }
            let position = match positions.get(&net) {
                Some(&position) => position,
                None => {
                    let position = blocks.len();
                    positions.insert(net, position);
                    blocks.push((net, Vec::new()));
                    position
                }
            };
            blocks[position].1.push(key);
        }
    }
    blocks
}

fn reflection_phase(key: &MixedMonomial, variables: usize) -> ComplexExact {
    if variables == STATE_VARIABLES || (key.anti.0[U] + key.holo.0[U]).is_multiple_of(2) {
        ComplexExact::ONE
    } else {
        ComplexExact::I
    }
}

#[derive(Clone, Debug)]
struct MomentSpace {
    keys: Vec<MixedMonomial>,
    index: BTreeMap<MixedMonomial, usize>,
}

impl MomentSpace {
    fn create(maximum_degree: u16) -> Self {
        let canonical = normal_invariant_monomials(BULK_VARIABLES, maximum_degree, &BULK_CHARGES)
            .into_iter()
            .map(|key| key.clone().min(key.conjugate()))
            .collect::<BTreeSet<_>>();
        let keys = canonical.into_iter().collect::<Vec<_>>();
        let index = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(position, key)| (key, position))
            .collect();
        Self { keys, index }
    }

    fn coefficient(&self, key: &MixedMonomial, coefficient: ComplexExact) -> (usize, Qsqrt2) {
        let conjugate = key.conjugate();
        let canonical = key.clone().min(conjugate);
        let column = self.index[&canonical];
        let phase = reflection_phase(&canonical, BULK_VARIABLES);
        let phase = if *key == canonical {
            phase
        } else {
            phase.conjugate()
        };
        let value = coefficient * phase;
        assert_eq!(
            value.im,
            Qsqrt2::ZERO,
            "reflection-rephased coefficient must be real for {key:?}"
        );
        (column, value.re)
    }
}

fn gram_entry(left: &MixedMonomial, right: &MixedMonomial) -> MixedMonomial {
    MixedMonomial {
        anti: add_exponents(&left.holo, &right.anti),
        holo: add_exponents(&left.anti, &right.holo),
    }
}

/// Orthonormal Helmert columns spanning the exact restriction kernel on `r1=r2=0`.
fn zero_cost_face(basis: &[MixedMonomial]) -> Vec<Vec<(usize, f64)>> {
    let mut columns = Vec::new();
    let mut groups: BTreeMap<(i32, i32, i32), Vec<usize>> = BTreeMap::new();
    for (index, key) in basis.iter().enumerate() {
        if key.anti.0[R1] != 0 || key.holo.0[R1] != 0 || key.anti.0[R2] != 0 || key.holo.0[R2] != 0
        {
            columns.push(vec![(index, 1.0)]);
        } else {
            groups
                .entry((
                    i32::from(key.holo.0[U]) - i32::from(key.anti.0[U]),
                    i32::from(key.holo.0[G1]) - i32::from(key.anti.0[G1]),
                    i32::from(key.holo.0[G2]) - i32::from(key.anti.0[G2]),
                ))
                .or_default()
                .push(index);
        }
    }
    for indices in groups.values() {
        for offset in 1..indices.len() {
            let normalization = ((offset * (offset + 1)) as f64).sqrt();
            let mut column = indices[..offset]
                .iter()
                .map(|&index| (index, 1.0 / normalization))
                .collect::<Vec<_>>();
            column.push((indices[offset], -(offset as f64) / normalization));
            columns.push(column);
        }
    }
    columns
}

/// Integer zero-cost-face columns in the exact certificate's positional order.
fn integer_zero_cost_face(basis: &[MixedMonomial]) -> Vec<Vec<(usize, i64)>> {
    let mut columns = Vec::new();
    let mut group_positions = BTreeMap::new();
    let mut groups: Vec<((i32, i32, i32), Vec<usize>)> = Vec::new();
    for (index, key) in basis.iter().enumerate() {
        if key.anti.0[R1] != 0 || key.holo.0[R1] != 0 || key.anti.0[R2] != 0 || key.holo.0[R2] != 0
        {
            columns.push(vec![(index, 1)]);
        } else {
            let character = (
                i32::from(key.holo.0[U]) - i32::from(key.anti.0[U]),
                i32::from(key.holo.0[G1]) - i32::from(key.anti.0[G1]),
                i32::from(key.holo.0[G2]) - i32::from(key.anti.0[G2]),
            );
            let position = match group_positions.get(&character) {
                Some(&position) => position,
                None => {
                    let position = groups.len();
                    group_positions.insert(character, position);
                    groups.push((character, Vec::new()));
                    position
                }
            };
            groups[position].1.push(index);
        }
    }
    for (_, indices) in groups {
        for offset in 1..indices.len() {
            let mut column = indices[..offset]
                .iter()
                .map(|&index| (index, 1))
                .collect::<Vec<_>>();
            column.push((indices[offset], -(offset as i64)));
            columns.push(column);
        }
    }
    columns
}

fn state_to_bulk(key: &MixedMonomial) -> MixedMonomial {
    let mut anti = vec![0];
    anti.extend(&key.anti.0);
    let mut holo = vec![0];
    holo.extend(&key.holo.0);
    MixedMonomial {
        anti: Exponent(anti),
        holo: Exponent(holo),
    }
}

fn exponent_with(variables: usize, index: usize) -> Exponent {
    let mut exponent = vec![0; variables];
    exponent[index] = 1;
    Exponent(exponent)
}

fn add_term(polynomial: &mut Polynomial, key: MixedMonomial, coefficient: ComplexExact) {
    let value = polynomial.get(&key).copied().unwrap_or(ComplexExact::ZERO) + coefficient;
    if value == ComplexExact::ZERO {
        polynomial.remove(&key);
    } else {
        polynomial.insert(key, value);
    }
}

fn liouville_derivative(test: &MixedMonomial) -> Polynomial {
    let mut derivative = Polynomial::new();
    for (ground, rydberg, kappa) in [
        (0, 1, Qsqrt2::new(Rational::new(1, 2), Rational::ZERO)),
        (2, 3, Qsqrt2::new(Rational::ZERO, Rational::new(1, 2))),
    ] {
        if test.holo.0[ground] != 0 {
            let mut reduced = test.clone();
            reduced.holo.0[ground] -= 1;
            let base = state_to_bulk(&reduced);
            let mut factor = MixedMonomial {
                anti: Exponent(vec![0; BULK_VARIABLES]),
                holo: Exponent(vec![0; BULK_VARIABLES]),
            };
            factor.holo.0[U] = 1;
            factor.holo.0[1 + rydberg] = 1;
            add_term(
                &mut derivative,
                shift(&base, &factor),
                -ComplexExact::I
                    * ComplexExact::real(kappa * Qsqrt2::from(i64::from(test.holo.0[ground]))),
            );
        }
        if test.holo.0[rydberg] != 0 {
            let mut reduced = test.clone();
            reduced.holo.0[rydberg] -= 1;
            let base = state_to_bulk(&reduced);
            let factor = MixedMonomial {
                anti: exponent_with(BULK_VARIABLES, U),
                holo: exponent_with(BULK_VARIABLES, 1 + ground),
            };
            add_term(
                &mut derivative,
                shift(&base, &factor),
                -ComplexExact::I
                    * ComplexExact::real(kappa * Qsqrt2::from(i64::from(test.holo.0[rydberg]))),
            );
        }
        if test.anti.0[ground] != 0 {
            let mut reduced = test.clone();
            reduced.anti.0[ground] -= 1;
            let base = state_to_bulk(&reduced);
            let mut factor = MixedMonomial {
                anti: Exponent(vec![0; BULK_VARIABLES]),
                holo: Exponent(vec![0; BULK_VARIABLES]),
            };
            factor.anti.0[U] = 1;
            factor.anti.0[1 + rydberg] = 1;
            add_term(
                &mut derivative,
                shift(&base, &factor),
                ComplexExact::I
                    * ComplexExact::real(kappa * Qsqrt2::from(i64::from(test.anti.0[ground]))),
            );
        }
        if test.anti.0[rydberg] != 0 {
            let mut reduced = test.clone();
            reduced.anti.0[rydberg] -= 1;
            let base = state_to_bulk(&reduced);
            let factor = MixedMonomial {
                anti: exponent_with(BULK_VARIABLES, 1 + ground),
                holo: exponent_with(BULK_VARIABLES, U),
            };
            add_term(
                &mut derivative,
                shift(&base, &factor),
                ComplexExact::I
                    * ComplexExact::real(kappa * Qsqrt2::from(i64::from(test.anti.0[rydberg]))),
            );
        }
    }
    derivative
}

fn reduce_polynomial(polynomial: &Polynomial) -> Polynomial {
    let mut result = Polynomial::new();
    for (key, &coefficient) in polynomial {
        for (normal, integer) in normal_form(key, BULK_VARIABLES) {
            add_term(
                &mut result,
                normal,
                coefficient * ComplexExact::real(Qsqrt2::from(integer)),
            );
        }
    }
    result
}

fn initial_value(test: &MixedMonomial) -> i64 {
    let rydberg = [1, 3];
    if rydberg
        .iter()
        .any(|&index| test.anti.0[index] != 0 || test.holo.0[index] != 0)
    {
        0
    } else {
        1
    }
}

fn target_value(test: &MixedMonomial) -> i64 {
    let rydberg = [1, 3];
    if rydberg
        .iter()
        .any(|&index| test.anti.0[index] != 0 || test.holo.0[index] != 0)
    {
        0
    } else if (test.anti.0[2] + test.holo.0[2]).is_multiple_of(2) {
        1
    } else {
        -1
    }
}

#[derive(Default)]
struct SparseBuilder(BTreeMap<(usize, usize), f64>);

impl SparseBuilder {
    fn add(&mut self, row: usize, column: usize, value: Qsqrt2) {
        self.add_f64(row, column, value.to_f64());
    }

    fn add_f64(&mut self, row: usize, column: usize, value: f64) {
        if value != 0.0 {
            *self.0.entry((column, row)).or_default() += value;
        }
    }

    fn finish(self) -> Vec<(usize, usize, f64)> {
        self.0
            .into_iter()
            .filter_map(|((column, row), value)| (value != 0.0).then_some((row, column, value)))
            .collect()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ExactLiouvilleRow {
    pub(crate) endpoint: i64,
    pub(crate) coefficients: Vec<(usize, Qsqrt2)>,
}

#[derive(Clone, Debug)]
struct ExactGramBlock {
    basis: Vec<MixedMonomial>,
    face: Vec<Vec<(usize, i64)>>,
}

/// Exact, optimizer-free coefficient operator for positional dual certificates.
#[derive(Clone, Debug)]
pub(crate) struct ExactCertificateModel {
    moments: MomentSpace,
    pub(crate) cost: Vec<(usize, Qsqrt2)>,
    pub(crate) equalities: Vec<ExactLiouvilleRow>,
    blocks: Vec<ExactGramBlock>,
}

impl ExactCertificateModel {
    pub(crate) fn coefficient_count(&self) -> usize {
        self.moments.keys.len()
    }

    pub(crate) fn gram_dimensions(&self) -> Vec<usize> {
        self.blocks.iter().map(|block| block.face.len()).collect()
    }

    pub(crate) fn rydberg_degree(&self, position: usize) -> u16 {
        let key = &self.moments.keys[position];
        [R1, R2]
            .into_iter()
            .map(|variable| key.anti.0[variable] + key.holo.0[variable])
            .sum()
    }

    /// Stream coefficients of one face-Gram entry without materializing the
    /// dense affine operator. The caller supplies both `(row, column)` and
    /// `(column, row)` for an off-diagonal symmetric variable when needed.
    pub(crate) fn for_each_gram_entry_coefficient(
        &self,
        block_index: usize,
        row: usize,
        column: usize,
        mut visit: impl FnMut(usize, Qsqrt2),
    ) {
        let block = &self.blocks[block_index];
        for &(left_index, left_weight) in &block.face[row] {
            for &(right_index, right_weight) in &block.face[column] {
                let left = &block.basis[left_index];
                let right = &block.basis[right_index];
                let phase = reflection_phase(left, BULK_VARIABLES).conjugate()
                    * reflection_phase(right, BULK_VARIABLES);
                let face_weight = left_weight * right_weight;
                for (key, normal_coefficient) in
                    normal_form(&gram_entry(left, right), BULK_VARIABLES)
                {
                    let coefficient =
                        phase * ComplexExact::real(Qsqrt2::from(normal_coefficient * face_weight));
                    let (position, value) = self.moments.coefficient(&key, coefficient);
                    visit(position, value);
                }
            }
        }
    }
}

pub(crate) fn exact_certificate_model(order: u8) -> Result<ExactCertificateModel, String> {
    if order < 2 {
        return Err("stationary-torus order must be at least two".into());
    }
    let moments = MomentSpace::create(2 * u16::from(order));
    let tests =
        normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
            .collect::<Vec<_>>();

    let cost = [(R1, Rational::new(1, 2)), (R2, Rational::new(1, 4))]
        .into_iter()
        .map(|(variable, coefficient)| {
            let exponent = exponent_with(BULK_VARIABLES, variable);
            let key = MixedMonomial {
                anti: exponent.clone(),
                holo: exponent,
            };
            (
                moments.index[&key],
                Qsqrt2::new(coefficient, Rational::ZERO),
            )
        })
        .collect();

    let equalities = tests
        .iter()
        .map(|test| {
            let coefficients = reduce_polynomial(&liouville_derivative(test))
                .into_iter()
                .map(|(key, coefficient)| moments.coefficient(&key, coefficient))
                .collect();
            ExactLiouvilleRow {
                endpoint: initial_value(test) - target_value(test),
                coefficients,
            }
        })
        .collect();

    let blocks = source_order_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES)
        .into_iter()
        .filter_map(|(_, basis)| {
            let face = integer_zero_cost_face(&basis);
            (!face.is_empty()).then_some(ExactGramBlock { basis, face })
        })
        .collect();

    Ok(ExactCertificateModel {
        moments,
        cost,
        equalities,
        blocks,
    })
}

/// Assemble the same hierarchy in the source-ordered integer facial basis used
/// by exact certificates. This is a certification discovery lane; the regular
/// floating assembly remains unchanged for source-parity runs.
pub fn assemble_exactification(order: u8) -> Result<StationaryTorusProblem, String> {
    let structure = structure(order)?;
    let model = exact_certificate_model(order)?;
    let mut q = vec![0.0; model.coefficient_count()];
    for &(position, coefficient) in &model.cost {
        q[position] = coefficient.to_f64();
    }

    let mut sparse = SparseBuilder::default();
    let mut b = Vec::new();
    for (row, equality) in model.equalities.iter().enumerate() {
        for &(column, coefficient) in &equality.coefficients {
            sparse.add(row, column, coefficient);
        }
        b.push(-(equality.endpoint as f64));
    }
    let mut cones = vec![Cone::Zero(model.equalities.len())];
    let mut next_row = model.equalities.len();
    for (block_index, side) in model.gram_dimensions().into_iter().enumerate() {
        for column in 0..side {
            for row in 0..=column {
                let scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                model.for_each_gram_entry_coefficient(
                    block_index,
                    row,
                    column,
                    |position, coefficient| {
                        sparse.add(next_row, position, -(coefficient * scale));
                    },
                );
                b.push(0.0);
                next_row += 1;
            }
        }
        cones.push(Cone::PsdTriangle(side));
    }
    let conic = ConicProblem {
        q,
        a: SparseMatrix {
            rows: next_row,
            cols: model.coefficient_count(),
            entries: sparse.finish(),
        },
        b,
        cones,
    };
    conic.validate()?;
    Ok(StationaryTorusProblem { structure, conic })
}

pub fn structure(order: u8) -> Result<StationaryTorusStructure, String> {
    if order < 2 {
        return Err("stationary-torus order must be at least two".into());
    }
    let moments = MomentSpace::create(2 * u16::from(order));
    let tests =
        normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
            .collect::<Vec<_>>();
    let blocks = normal_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES);
    let mut psd_block_sides = blocks
        .values()
        .map(|basis| zero_cost_face(basis).len())
        .filter(|&side| side != 0)
        .collect::<Vec<_>>();
    psd_block_sides.sort_unstable_by(|left, right| right.cmp(left));
    let basis_hash = format!(
        "sha256:{:x}",
        Sha256::digest(serde_json::to_vec(&moments.keys).expect("basis serializes"))
    );
    let liouville_basis_hash = format!(
        "sha256:{:x}",
        Sha256::digest(serde_json::to_vec(&tests).expect("Liouville basis serializes"))
    );
    let formulation_hash = format!(
        "sha256:{:x}",
        Sha256::digest(
            serde_json::to_vec(&serde_json::json!({
                "schema": "minexposure/stationary-torus-v1",
                "order": order,
                "basis_hash": &basis_hash,
                "liouville_basis_hash": &liouville_basis_hash,
                "psd_block_sides": &psd_block_sides,
                "field": "Q(sqrt(2))",
                "liouville_realification": "source_real_row_then_zero_imaginary_row",
                "quotient": ["|u|^2=1", "|g1|^2+|r1|^2=1", "|g2|^2+|r2|^2=1"],
                "face": "orthonormal_helmert_kernel_r1_r2_zero",
                "source_commit": "677eba8905756a4dd4d1f0c760b0375ebec67161"
            }))
            .expect("formulation identity serializes"),
        )
    );
    Ok(StationaryTorusStructure {
        order,
        maximum_moment_degree: 2 * order,
        moment_count: moments.keys.len(),
        liouville_equality_count: tests.len(),
        largest_psd_side: psd_block_sides.first().copied().unwrap_or(0),
        sum_psd_squares: psd_block_sides.iter().map(|side| side * side).sum(),
        sum_psd_cubes: psd_block_sides.iter().map(|side| side * side * side).sum(),
        psd_block_sides,
        basis_hash,
        liouville_basis_hash,
        formulation_hash,
        source_repository: "https://github.com/wanda0929/Finite_blockade_pulse",
        source_commit: "677eba8905756a4dd4d1f0c760b0375ebec67161",
        source_path: "verification/jan22_cz_exposure_stationary_torus_sdp.py",
    })
}

/// Charge and side of each PSD block in native conic assembly order.
///
/// This is diagnostic metadata for matching solution dumps across relaxation
/// orders; it is deliberately kept out of the canonical structure payload.
pub fn gram_block_metadata(order: u8) -> Result<Vec<GramBlockMetadata>, String> {
    if order < 2 {
        return Err("stationary-torus order must be at least two".into());
    }
    Ok(
        normal_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES)
            .into_iter()
            .filter_map(|(charge, basis)| {
                let side = zero_cost_face(&basis).len();
                (side != 0).then_some(GramBlockMetadata { charge, side })
            })
            .collect(),
    )
}

pub fn assemble(order: u8) -> Result<StationaryTorusProblem, String> {
    let structure = structure(order)?;
    let moments = MomentSpace::create(2 * u16::from(order));
    let tests =
        normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
            .collect::<Vec<_>>();
    let blocks = normal_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES);

    let mut q = vec![0.0; moments.keys.len()];
    for (variable, coefficient) in [(R1, 0.5), (R2, 0.25)] {
        let exponent = exponent_with(BULK_VARIABLES, variable);
        let key = MixedMonomial {
            anti: exponent.clone(),
            holo: exponent,
        };
        q[moments.index[&key]] = coefficient;
    }

    let mut sparse = SparseBuilder::default();
    let mut b = Vec::new();
    for (index, test) in tests.iter().enumerate() {
        // The source writes each real Liouville equation with complex constants.
        // CVXPY realifies it as an active real row followed by an identically
        // zero imaginary row. Preserve that canonical task structure because it
        // affects MOSEK's numerical path at the retained high orders.
        let row = 2 * index;
        let derivative = reduce_polynomial(&liouville_derivative(test));
        for (key, coefficient) in derivative {
            let (column, value) = moments.coefficient(&key, coefficient);
            sparse.add(row, column, value);
        }
        b.push((target_value(test) - initial_value(test)) as f64);
        b.push(0.0);
    }
    let mut cones = vec![Cone::Zero(2 * tests.len())];
    let mut next_row = 2 * tests.len();

    for basis in blocks.values() {
        let face = zero_cost_face(basis);
        let side = face.len();
        if side == 0 {
            continue;
        }
        for column in 0..side {
            // Clarabel and MOSEK use upper-triangular, column-major svec order:
            // (0,0), (0,1), (1,1), (0,2), ... .
            for row in 0..=column {
                let svec_scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                for &(left_index, left_weight) in &face[row] {
                    for &(right_index, right_weight) in &face[column] {
                        let left = &basis[left_index];
                        let right = &basis[right_index];
                        let phase = reflection_phase(left, BULK_VARIABLES).conjugate()
                            * reflection_phase(right, BULK_VARIABLES);
                        for (key, normal_coefficient) in
                            normal_form(&gram_entry(left, right), BULK_VARIABLES)
                        {
                            let coefficient =
                                phase * ComplexExact::real(Qsqrt2::from(normal_coefficient));
                            let (moment_column, value) = moments.coefficient(&key, coefficient);
                            // A*y+s=0 and s=M(y), hence A=-M.
                            sparse.add_f64(
                                next_row,
                                moment_column,
                                -(value * svec_scale).to_f64() * left_weight * right_weight,
                            );
                        }
                    }
                }
                b.push(0.0);
                next_row += 1;
            }
        }
        cones.push(Cone::PsdTriangle(side));
    }

    let conic = ConicProblem {
        q,
        a: SparseMatrix {
            rows: next_row,
            cols: moments.keys.len(),
            entries: sparse.finish(),
        },
        b,
        cones,
    };
    conic.validate()?;
    Ok(StationaryTorusProblem { structure, conic })
}

#[derive(Clone, Debug, Deserialize)]
pub struct IdealBlockadePulse {
    pub duration: f64,
    pub phases: Vec<f64>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct PackedPsdBlock {
    pub side: usize,
    pub lower_triangle_column_major: Vec<f64>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct StationaryDualDump {
    pub zero_cone_multipliers: Vec<f64>,
    pub psd_blocks: Vec<PackedPsdBlock>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct StationarySolutionDump {
    pub objective: f64,
    pub primal_variables: Vec<f64>,
    pub dual: StationaryDualDump,
}

#[derive(Clone, Debug, Serialize)]
pub struct MomentDistance {
    pub l1: f64,
    pub l2: f64,
    pub linf: f64,
    pub relative_l2: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SlackSample {
    pub segment: usize,
    pub fraction: f64,
    pub time: f64,
    pub slack: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct ChargeContribution {
    pub charge: (i32, i32),
    pub side: usize,
    pub value: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct ChargeProfile {
    pub location: SlackSample,
    pub total: f64,
    pub largest_blocks: Vec<ChargeContribution>,
}

#[derive(Clone, Debug, Serialize)]
pub struct StationaryTrajectoryDiagnostic {
    pub schema: &'static str,
    pub order: u8,
    pub segment_count: usize,
    pub duration: f64,
    pub trajectory_objective: f64,
    pub solver_objective: Option<f64>,
    pub objective_gap: Option<f64>,
    pub moment_basis: Vec<MixedMonomial>,
    pub trajectory_moments: Vec<f64>,
    pub moment_distance: Option<MomentDistance>,
    pub moment_distance_without_occupation_mass: Option<MomentDistance>,
    pub moment_distance_by_degree: BTreeMap<u16, MomentDistance>,
    pub moment_distance_through_degree_without_mass: BTreeMap<u16, MomentDistance>,
    pub rydberg_supported_moment_distance: Option<MomentDistance>,
    pub rydberg_supported_distance_through_degree: BTreeMap<u16, MomentDistance>,
    pub integrated_dual_slack: Option<f64>,
    pub integrated_slack_by_degree: BTreeMap<u16, f64>,
    pub minimum_slack: Option<SlackSample>,
    pub maximum_slack: Option<SlackSample>,
    pub slack_quantiles: BTreeMap<String, f64>,
    pub charge_profiles: Vec<ChargeProfile>,
    pub maximum_discarded_reflection_imaginary_part: f64,
    pub maximum_liouville_residual: f64,
}

#[derive(Clone, Copy)]
struct TrajectoryPoint {
    segment: usize,
    fraction: f64,
    time: f64,
    z: [Complex64; BULK_VARIABLES],
}

fn complex_value(value: ComplexExact) -> Complex64 {
    Complex64::new(value.re.to_f64(), value.im.to_f64())
}

fn monomial_value(key: &MixedMonomial, powers: &[[Vec<Complex64>; 2]]) -> Complex64 {
    key.anti.0.iter().zip(&key.holo.0).enumerate().fold(
        Complex64::new(1.0, 0.0),
        |value, (variable, (&anti, &holo))| {
            value * powers[variable][0][usize::from(anti)] * powers[variable][1][usize::from(holo)]
        },
    )
}

fn point_powers(z: &[Complex64; BULK_VARIABLES], degree: usize) -> Vec<[Vec<Complex64>; 2]> {
    z.iter()
        .map(|&value| {
            let mut anti = vec![Complex64::new(1.0, 0.0); degree + 1];
            let mut holo = anti.clone();
            for power in 1..=degree {
                anti[power] = anti[power - 1] * value.conj();
                holo[power] = holo[power - 1] * value;
            }
            [anti, holo]
        })
        .collect()
}

fn segment_point(
    segment: usize,
    fraction: f64,
    segment_duration: f64,
    phase: f64,
    state: &[Complex64; STATE_VARIABLES],
) -> TrajectoryPoint {
    let t = fraction * segment_duration;
    let u = Complex64::from_polar(1.0, phase);
    let minus_i = Complex64::new(0.0, -1.0);
    let evolve = |g: Complex64, r: Complex64, rate: f64| {
        let angle = rate * t;
        let (sine, cosine) = angle.sin_cos();
        (
            g * cosine + minus_i * u * r * sine,
            r * cosine + minus_i * u.conj() * g * sine,
        )
    };
    let (g1, r1) = evolve(state[0], state[1], 0.5);
    let (g2, r2) = evolve(state[2], state[3], 1.0 / 2.0_f64.sqrt());
    TrajectoryPoint {
        segment,
        fraction,
        time: (segment as f64 + fraction) * segment_duration,
        z: [u, g1, r1, g2, r2],
    }
}

fn advance_segment(
    segment: usize,
    segment_duration: f64,
    phase: f64,
    state: &mut [Complex64; STATE_VARIABLES],
) {
    let endpoint = segment_point(segment, 1.0, segment_duration, phase, state);
    state.copy_from_slice(&endpoint.z[1..]);
}

fn gauss_legendre(count: usize) -> Vec<(f64, f64)> {
    let mut result = vec![(0.0, 0.0); count];
    let half = count.div_ceil(2);
    for index in 0..half {
        let mut root = (std::f64::consts::PI * (index as f64 + 0.75) / (count as f64 + 0.5)).cos();
        let derivative = loop {
            let mut previous = 1.0;
            let mut current = root;
            for degree in 2..=count {
                let next = ((2 * degree - 1) as f64 * root * current
                    - (degree - 1) as f64 * previous)
                    / degree as f64;
                previous = current;
                current = next;
            }
            let derivative = count as f64 * (root * current - previous) / (root * root - 1.0);
            let next = root - current / derivative;
            if (next - root).abs() < 2e-16 {
                root = next;
                break derivative;
            }
            root = next;
        };
        let weight = 1.0 / ((1.0 - root * root) * derivative * derivative);
        result[index] = ((1.0 - root) / 2.0, weight);
        result[count - index - 1] = ((1.0 + root) / 2.0, weight);
    }
    result
}

fn dual_slack(
    point: &TrajectoryPoint,
    tests: &[MixedMonomial],
    multipliers: &[f64],
    maximum_degree: usize,
) -> (f64, BTreeMap<u16, f64>) {
    let powers = point_powers(&point.z, maximum_degree);
    let mut by_degree = BTreeMap::new();
    let cost = 0.5 * point.z[R1].norm_sqr() + 0.25 * point.z[R2].norm_sqr();
    by_degree.insert(2, cost);
    let mut slack = cost;
    for (index, test) in tests.iter().enumerate() {
        let multiplier = multipliers[2 * index];
        if multiplier == 0.0 {
            continue;
        }
        for (key, coefficient) in reduce_polynomial(&liouville_derivative(test)) {
            let value =
                multiplier * (complex_value(coefficient) * monomial_value(&key, &powers)).re;
            slack += value;
            *by_degree
                .entry(key.anti.degree() + key.holo.degree())
                .or_default() += value;
        }
    }
    (slack, by_degree)
}

fn charge_profile(
    point: TrajectoryPoint,
    blocks: &BTreeMap<Charge, Vec<MixedMonomial>>,
    matrices: &[PackedPsdBlock],
    maximum_degree: usize,
    slack: f64,
) -> ChargeProfile {
    let powers = point_powers(&point.z, maximum_degree);
    let mut contributions = Vec::new();
    for (((&charge, basis), matrix), side) in blocks
        .iter()
        .filter_map(|entry| {
            let side = zero_cost_face(entry.1).len();
            (side != 0).then_some((entry, side))
        })
        .zip(matrices)
        .map(|((entry, side), matrix)| ((entry, matrix), side))
    {
        assert_eq!(side, matrix.side);
        let face = zero_cost_face(basis);
        let features = face
            .iter()
            .map(|column| {
                column
                    .iter()
                    .fold(Complex64::new(0.0, 0.0), |sum, &(index, weight)| {
                        let phase = complex_value(reflection_phase(&basis[index], BULK_VARIABLES));
                        sum + weight * phase * monomial_value(&basis[index], &powers)
                    })
            })
            .collect::<Vec<_>>();
        let mut value = 0.0;
        let mut packed = 0;
        for column in 0..side {
            for row in column..side {
                let product = features[row].conj() * features[column];
                value += matrix.lower_triangle_column_major[packed]
                    * if row == column {
                        product.re
                    } else {
                        2.0 * product.re
                    };
                packed += 1;
            }
        }
        contributions.push(ChargeContribution {
            charge,
            side,
            value,
        });
    }
    let total = contributions.iter().map(|entry| entry.value).sum();
    contributions.sort_by(|left, right| right.value.abs().total_cmp(&left.value.abs()));
    contributions.truncate(12);
    ChargeProfile {
        location: SlackSample {
            segment: point.segment,
            fraction: point.fraction,
            time: point.time,
            slack,
        },
        total,
        largest_blocks: contributions,
    }
}

pub fn diagnose_ideal_blockade_pulse(
    order: u8,
    pulse: &IdealBlockadePulse,
    solution: Option<&StationarySolutionDump>,
) -> Result<StationaryTrajectoryDiagnostic, String> {
    if order < 2 || pulse.phases.is_empty() || !pulse.duration.is_finite() || pulse.duration <= 0.0
    {
        return Err("invalid order or ideal-blockade pulse".into());
    }
    let moments = MomentSpace::create(2 * u16::from(order));
    let tests =
        normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
            .collect::<Vec<_>>();
    if let Some(solution) = solution
        && (solution.primal_variables.len() != moments.keys.len()
            || solution.dual.zero_cone_multipliers.len() != 2 * tests.len())
    {
        return Err("solution dimensions do not match stationary-torus order".into());
    }

    let segment_duration = pulse.duration / pulse.phases.len() as f64;
    let quadrature = gauss_legendre(16);
    let mut state = [
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
    ];
    let mut raw_moments = vec![Complex64::new(0.0, 0.0); moments.keys.len()];
    let mut integrated_slack = 0.0;
    let mut integrated_by_degree = BTreeMap::new();
    let mut midpoint_samples = Vec::with_capacity(pulse.phases.len());
    for (segment, &phase) in pulse.phases.iter().enumerate() {
        for &(fraction, weight) in &quadrature {
            let point = segment_point(segment, fraction, segment_duration, phase, &state);
            let powers = point_powers(&point.z, usize::from(2 * order));
            for (index, key) in moments.keys.iter().enumerate() {
                raw_moments[index] += segment_duration * weight * monomial_value(key, &powers);
            }
            if let Some(solution) = solution {
                let (slack, by_degree) = dual_slack(
                    &point,
                    &tests,
                    &solution.dual.zero_cone_multipliers,
                    usize::from(2 * order),
                );
                integrated_slack += segment_duration * weight * slack;
                for (degree, value) in by_degree {
                    *integrated_by_degree.entry(degree).or_default() +=
                        segment_duration * weight * value;
                }
            }
        }
        if let Some(solution) = solution {
            let point = segment_point(segment, 0.5, segment_duration, phase, &state);
            let (slack, _) = dual_slack(
                &point,
                &tests,
                &solution.dual.zero_cone_multipliers,
                usize::from(2 * order),
            );
            midpoint_samples.push((point, slack));
        }
        advance_segment(segment, segment_duration, phase, &mut state);
    }

    let mut maximum_discarded = 0.0_f64;
    let trajectory_moments = moments
        .keys
        .iter()
        .zip(raw_moments)
        .map(|(key, value)| {
            let phase = complex_value(reflection_phase(key, BULK_VARIABLES));
            let reduced = value / phase;
            maximum_discarded = maximum_discarded.max(reduced.im.abs());
            reduced.re
        })
        .collect::<Vec<_>>();
    let trajectory_objective = moments
        .keys
        .iter()
        .zip(&trajectory_moments)
        .enumerate()
        .map(|(index, (key, &value))| {
            if key.anti == exponent_with(BULK_VARIABLES, R1)
                && key.holo == exponent_with(BULK_VARIABLES, R1)
            {
                0.5 * value
            } else if key.anti == exponent_with(BULK_VARIABLES, R2)
                && key.holo == exponent_with(BULK_VARIABLES, R2)
            {
                0.25 * value
            } else {
                let _ = index;
                0.0
            }
        })
        .sum();
    let maximum_liouville_residual = tests
        .iter()
        .map(|test| {
            let integral = reduce_polynomial(&liouville_derivative(test))
                .into_iter()
                .map(|(key, coefficient)| {
                    let (index, value) = moments.coefficient(&key, coefficient);
                    value.to_f64() * trajectory_moments[index]
                })
                .sum::<f64>();
            (integral - (target_value(test) - initial_value(test)) as f64).abs()
        })
        .fold(0.0, f64::max);
    let distance = |indices: &[usize], solution: &StationarySolutionDump| {
        let differences = indices
            .iter()
            .map(|&index| trajectory_moments[index] - solution.primal_variables[index])
            .collect::<Vec<_>>();
        let l2 = differences
            .iter()
            .map(|value| value * value)
            .sum::<f64>()
            .sqrt();
        let primal_l2 = indices
            .iter()
            .map(|&index| solution.primal_variables[index] * solution.primal_variables[index])
            .sum::<f64>()
            .sqrt();
        MomentDistance {
            l1: differences.iter().map(|value| value.abs()).sum(),
            l2,
            linf: differences
                .iter()
                .map(|value| value.abs())
                .fold(0.0, f64::max),
            relative_l2: l2 / primal_l2,
        }
    };
    let all_indices = (0..moments.keys.len()).collect::<Vec<_>>();
    let nonconstant_indices = (1..moments.keys.len()).collect::<Vec<_>>();
    let has_rydberg_factor = |key: &MixedMonomial| {
        [R1, R2]
            .iter()
            .any(|&variable| key.anti.0[variable] != 0 || key.holo.0[variable] != 0)
    };
    let rydberg_indices = moments
        .keys
        .iter()
        .enumerate()
        .filter_map(|(index, key)| has_rydberg_factor(key).then_some(index))
        .collect::<Vec<_>>();
    let moment_distance = solution.map(|solution| distance(&all_indices, solution));
    let moment_distance_without_occupation_mass =
        solution.map(|solution| distance(&nonconstant_indices, solution));
    let rydberg_supported_moment_distance =
        solution.map(|solution| distance(&rydberg_indices, solution));
    let mut moment_distance_by_degree = BTreeMap::new();
    let mut moment_distance_through_degree_without_mass = BTreeMap::new();
    let mut rydberg_supported_distance_through_degree = BTreeMap::new();
    if let Some(solution) = solution {
        for degree in 0..=2 * u16::from(order) {
            let indices = moments
                .keys
                .iter()
                .enumerate()
                .filter_map(|(index, key)| {
                    (key.anti.degree() + key.holo.degree() == degree).then_some(index)
                })
                .collect::<Vec<_>>();
            if !indices.is_empty() {
                moment_distance_by_degree.insert(degree, distance(&indices, solution));
            }
            if degree >= 2 {
                let through_indices = moments
                    .keys
                    .iter()
                    .enumerate()
                    .filter_map(|(index, key)| {
                        (index != 0 && key.anti.degree() + key.holo.degree() <= degree)
                            .then_some(index)
                    })
                    .collect::<Vec<_>>();
                moment_distance_through_degree_without_mass
                    .insert(degree, distance(&through_indices, solution));
                let rydberg_through_indices = moments
                    .keys
                    .iter()
                    .enumerate()
                    .filter_map(|(index, key)| {
                        (has_rydberg_factor(key) && key.anti.degree() + key.holo.degree() <= degree)
                            .then_some(index)
                    })
                    .collect::<Vec<_>>();
                rydberg_supported_distance_through_degree
                    .insert(degree, distance(&rydberg_through_indices, solution));
            }
        }
    }

    let minimum = midpoint_samples
        .iter()
        .min_by(|left, right| left.1.total_cmp(&right.1))
        .copied();
    let maximum = midpoint_samples
        .iter()
        .max_by(|left, right| left.1.total_cmp(&right.1))
        .copied();
    let sample = |entry: (TrajectoryPoint, f64)| SlackSample {
        segment: entry.0.segment,
        fraction: entry.0.fraction,
        time: entry.0.time,
        slack: entry.1,
    };
    let mut sorted_slack = midpoint_samples
        .iter()
        .map(|entry| entry.1)
        .collect::<Vec<_>>();
    sorted_slack.sort_by(f64::total_cmp);
    let mut quantiles = BTreeMap::new();
    for (name, numerator) in [
        ("p00", 0),
        ("p10", 10),
        ("p50", 50),
        ("p90", 90),
        ("p100", 100),
    ] {
        if !sorted_slack.is_empty() {
            let index = numerator * (sorted_slack.len() - 1) / 100;
            quantiles.insert(name.to_string(), sorted_slack[index]);
        }
    }
    let mut charge_profiles = Vec::new();
    if let (Some(solution), Some(minimum), Some(maximum)) = (solution, minimum, maximum) {
        let blocks = normal_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES);
        if solution.dual.psd_blocks.len()
            == blocks
                .values()
                .filter(|basis| !zero_cost_face(basis).is_empty())
                .count()
        {
            charge_profiles.push(charge_profile(
                minimum.0,
                &blocks,
                &solution.dual.psd_blocks,
                order.into(),
                minimum.1,
            ));
            if maximum.0.segment != minimum.0.segment {
                charge_profiles.push(charge_profile(
                    maximum.0,
                    &blocks,
                    &solution.dual.psd_blocks,
                    order.into(),
                    maximum.1,
                ));
            }
        }
    }

    Ok(StationaryTrajectoryDiagnostic {
        schema: "minexposure/stationary-trajectory-diagnostic-v1",
        order,
        segment_count: pulse.phases.len(),
        duration: pulse.duration,
        trajectory_objective,
        solver_objective: solution.map(|value| value.objective),
        objective_gap: solution.map(|value| trajectory_objective - value.objective),
        moment_basis: moments.keys,
        trajectory_moments,
        moment_distance,
        moment_distance_without_occupation_mass,
        moment_distance_by_degree,
        moment_distance_through_degree_without_mass,
        rydberg_supported_moment_distance,
        rydberg_supported_distance_through_degree,
        integrated_dual_slack: solution.map(|_| integrated_slack),
        integrated_slack_by_degree: integrated_by_degree,
        minimum_slack: minimum.map(sample),
        maximum_slack: maximum.map(sample),
        slack_quantiles: quantiles,
        charge_profiles,
        maximum_discarded_reflection_imaginary_part: maximum_discarded,
        maximum_liouville_residual,
    })
}

/// Add valid cost-weighted moment caps using the exact upper bound 147/50.
///
/// Every retained mixed monomial has modulus at most one on the three sphere
/// factors. Thus `|∫ L m dμ| ≤ ∫ L dμ ≤ 147/50` for the true optimal
/// occupation measure. Both signs are included because reflection makes these
/// invariant moments real. No occupation-mass cap is asserted.
pub fn assemble_strengthened(order: u8) -> Result<StrengthenedStationaryTorusProblem, String> {
    let StationaryTorusProblem {
        structure: base,
        conic,
    } = assemble(order)?;
    let moments = MomentSpace::create(2 * u16::from(order));
    let cap_degree = 2 * u16::from(order) - 2;
    let cap_keys = moments
        .keys
        .iter()
        .filter(|key| key.anti.degree() + key.holo.degree() <= cap_degree)
        .cloned()
        .collect::<Vec<_>>();

    let mut sparse = SparseBuilder::default();
    for (row, column, value) in conic.a.entries {
        sparse.add_f64(row, column, value);
    }
    let mut b = conic.b;
    let mut next_row = conic.a.rows;
    let upper_bound = Rational::new(147, 50);
    for key in cap_keys {
        let mut weighted = Polynomial::new();
        let realification = reflection_phase(&key, BULK_VARIABLES).conjugate();
        for (variable, coefficient) in [(R1, Rational::new(1, 2)), (R2, Rational::new(1, 4))] {
            let exponent = exponent_with(BULK_VARIABLES, variable);
            let cost_term = MixedMonomial {
                anti: exponent.clone(),
                holo: exponent,
            };
            add_term(
                &mut weighted,
                shift(&key, &cost_term),
                realification * ComplexExact::real(Qsqrt2::new(coefficient, Rational::ZERO)),
            );
        }
        let coefficients = reduce_polynomial(&weighted)
            .into_iter()
            .map(|(term, coefficient)| moments.coefficient(&term, coefficient))
            .collect::<Vec<_>>();
        for sign in [-1_i64, 1] {
            for &(column, coefficient) in &coefficients {
                sparse.add(next_row, column, coefficient * Qsqrt2::from(sign));
            }
            b.push(Qsqrt2::new(upper_bound, Rational::ZERO).to_f64());
            next_row += 1;
        }
    }
    let cap_count = next_row - conic.a.rows;
    let mut cones = conic.cones;
    cones.push(Cone::Nonnegative(cap_count));
    let conic = ConicProblem {
        q: conic.q,
        a: SparseMatrix {
            rows: next_row,
            cols: moments.keys.len(),
            entries: sparse.finish(),
        },
        b,
        cones,
    };
    conic.validate()?;
    Ok(StrengthenedStationaryTorusProblem {
        structure: StrengthenedStationaryTorusStructure {
            base,
            cost_cap: upper_bound,
            cost_weighted_moment_cap_count: cap_count,
            strengthening: "exact cost-weighted moment caps; occupation quotient unchanged",
        },
        conic,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotient_normal_form_is_exact() {
        let key = MixedMonomial {
            anti: Exponent(vec![1, 2, 0, 1, 0]),
            holo: Exponent(vec![1, 2, 0, 1, 0]),
        };
        let reduced = normal_form(&key, BULK_VARIABLES);
        assert_eq!(reduced.values().sum::<i64>(), 0);
        assert!(reduced.keys().all(|term| is_normal(term, BULK_VARIABLES)));
    }

    #[test]
    fn matches_committed_finite_repository_counts() {
        let expected = [
            (2, 14, 5, 13, 2, 34, 62),
            (3, 45, 14, 29, 8, 473, 2667),
            (4, 118, 32, 51, 19, 3900, 52788),
            (5, 273, 66, 79, 39, 22883, 644133),
            (6, 561, 120, 113, 75, 105706, 5612552),
            (7, 1054, 203, 153, 131, 406755, 37713285),
            (8, 1854, 326, 199, 216, 1359513, 207692321),
            (9, 3080, 495, 251, 342, 4058836, 975439026),
            (10, 4882, 724, 309, 518, 11039011, 4015916019),
            (11, 7454, 1028, 373, 758, 27768269, 14808151601),
        ];
        for (order, moments, equalities, blocks, largest, squares, cubes) in expected {
            let structure = structure(order).unwrap();
            assert_eq!(structure.moment_count, moments, "order {order}");
            assert_eq!(
                structure.liouville_equality_count, equalities,
                "order {order}"
            );
            assert_eq!(structure.psd_block_sides.len(), blocks, "order {order}");
            assert_eq!(structure.largest_psd_side, largest, "order {order}");
            assert_eq!(structure.sum_psd_squares, squares, "order {order}");
            assert_eq!(structure.sum_psd_cubes, cubes, "order {order}");
        }
        assert_eq!(
            archived_mosek_result(11).unwrap().objective,
            2.904_745_260_134_998_6
        );
    }

    #[test]
    fn archived_mosek_reference_matches_native_structure() {
        let reference: serde_json::Value = serde_json::from_str(include_str!(
            "../../../golden/stationary-torus-mosek-o6-o11.json"
        ))
        .unwrap();
        for result in reference["results"].as_array().unwrap() {
            let order = result["order"].as_u64().unwrap() as u8;
            let structure = structure(order).unwrap();
            assert_eq!(
                structure.moment_count as u64,
                result["moments"].as_u64().unwrap()
            );
            assert_eq!(
                structure.liouville_equality_count as u64,
                result["liouville_equalities"].as_u64().unwrap()
            );
            assert_eq!(
                structure.psd_block_sides.len() as u64,
                result["psd_blocks"].as_u64().unwrap()
            );
            assert_eq!(
                structure.largest_psd_side as u64,
                result["largest_psd_side"].as_u64().unwrap()
            );
            assert_eq!(
                archived_mosek_result(order).unwrap().objective,
                result["objective"].as_f64().unwrap()
            );
        }
    }

    #[test]
    fn assembles_a_scientific_order_two_sdp() {
        let problem = assemble(2).unwrap();
        assert_eq!(problem.conic.q.len(), 14);
        assert_eq!(problem.conic.cones.len(), 14);
        assert_eq!(problem.conic.cones[0], Cone::Zero(10));
        assert_eq!(problem.conic.b.len(), 37);
        assert!(
            problem.conic.b[..10]
                .iter()
                .skip(1)
                .step_by(2)
                .all(|&value| value == 0.0)
        );
        assert!(
            problem
                .conic
                .a
                .entries
                .iter()
                .filter(|&&(row, _, _)| row < 10)
                .all(|&(row, _, _)| row.is_multiple_of(2))
        );
        assert!(problem.conic.a.entries.len() > 30);
        assert_eq!(
            gram_block_metadata(2)
                .unwrap()
                .into_iter()
                .map(|block| block.side)
                .collect::<Vec<_>>(),
            problem
                .conic
                .cones
                .iter()
                .filter_map(|cone| match cone {
                    Cone::PsdTriangle(side) => Some(*side),
                    _ => None,
                })
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn integrates_the_certified_396_segment_witness() {
        let pulse: IdealBlockadePulse = serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap();
        let report = diagnose_ideal_blockade_pulse(2, &pulse, None).unwrap();
        assert_eq!(report.segment_count, 396);
        assert_eq!(report.trajectory_moments.len(), 14);
        assert!((report.trajectory_objective - 2.935_885_902_112_585_4).abs() < 2e-14);
    }

    #[test]
    fn strengthened_lane_only_appends_valid_scalar_caps() {
        let baseline = assemble(2).unwrap();
        let strengthened = assemble_strengthened(2).unwrap();
        assert_eq!(strengthened.conic.q, baseline.conic.q);
        assert_eq!(strengthened.structure.base, baseline.structure);
        assert!(strengthened.structure.cost_weighted_moment_cap_count > 0);
        assert_eq!(
            strengthened.conic.cones.last(),
            Some(&Cone::Nonnegative(
                strengthened.structure.cost_weighted_moment_cap_count
            ))
        );
    }

    #[test]
    fn phase_bearing_invariants_are_already_in_the_amplitude_quotient() {
        let moments = MomentSpace::create(4);
        let j = MixedMonomial {
            anti: Exponent(vec![0, 1, 0, 0, 1]),
            holo: Exponent(vec![0, 0, 1, 1, 0]),
        };
        let c = MixedMonomial {
            anti: Exponent(vec![0, 2, 0, 0, 0]),
            holo: Exponent(vec![0, 0, 0, 1, 0]),
        };
        assert!(moments.index.contains_key(&j.clone().min(j.conjugate())));
        assert!(moments.index.contains_key(&c.clone().min(c.conjugate())));

        // Their modulus syzygies are precisely the existing sphere expansion.
        let c_squared = gram_entry(&c, &c);
        let j_squared = gram_entry(&j, &j);
        assert_eq!(normal_form(&c_squared, BULK_VARIABLES).len(), 6);
        assert_eq!(normal_form(&j_squared, BULK_VARIABLES).len(), 4);
    }
}
