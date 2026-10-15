//! Normalized cumulative-cost Hausdorff lift of the JAN22 stationary torus.
//!
//! The additional real coordinate is `x=C/U`, with exact
//! `U=2935887/1000000`.  Rust owns the mixed state-cost Liouville operator,
//! terminal moments, and occupation/terminal Hausdorff matrices.  The archived
//! Python files are provenance references only and are never used at solve time.

use crate::algebra::{Qsqrt2, Rational};
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::monomial::{Exponent, monomials};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
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
pub(crate) const EXPOSURE_UPPER: Rational = Rational {
    numerator: 2_935_887,
    denominator: 1_000_000,
};

const BULK_CHARGES: [(i32, i32); BULK_VARIABLES] = [(1, 0), (0, 1), (-1, 1), (0, 2), (-1, 2)];
const STATE_CHARGES: [(i32, i32); STATE_VARIABLES] = [(0, 1), (-1, 1), (0, 2), (-1, 2)];

type Charge = (i32, i32);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ChargeEnrichment {
    pub charges: Vec<Charge>,
    pub extra_degree: u8,
}

impl ChargeEnrichment {
    pub fn new(charges: Vec<Charge>, extra_degree: u8) -> Result<Self, String> {
        if !(1..=2).contains(&extra_degree) {
            return Err("charge enrichment degree must be 1 or 2".into());
        }
        if charges.is_empty() {
            return Err("charge enrichment requires at least one charge sector".into());
        }
        let mut charges = charges
            .into_iter()
            .map(canonical_charge)
            .collect::<Result<Vec<_>, _>>()?;
        charges.sort_unstable();
        charges.dedup();
        Ok(Self {
            charges,
            extra_degree,
        })
    }

    pub fn parse(charges: &str, extra_degree: u8) -> Result<Self, String> {
        let charges = charges
            .split(',')
            .enumerate()
            .map(|(index, sector)| {
                let (first, second) = sector.trim().split_once(':').ok_or_else(|| {
                    format!("charge sector {} must use FIRST:SECOND syntax", index + 1)
                })?;
                let first = first.trim().parse::<i32>().map_err(|error| {
                    format!(
                        "invalid first component in charge sector {}: {error}",
                        index + 1
                    )
                })?;
                let second = second.trim().parse::<i32>().map_err(|error| {
                    format!(
                        "invalid second component in charge sector {}: {error}",
                        index + 1
                    )
                })?;
                Ok((first, second))
            })
            .collect::<Result<Vec<_>, String>>()?;
        Self::new(charges, extra_degree)
    }
}

fn canonical_charge(charge: Charge) -> Result<Charge, String> {
    let opposite = (
        charge
            .0
            .checked_neg()
            .ok_or("charge component is outside the supported range")?,
        charge
            .1
            .checked_neg()
            .ok_or("charge component is outside the supported range")?,
    );
    Ok(charge.min(opposite))
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct CostMonomial {
    pub cost_power: u16,
    pub anti: Exponent,
    pub holo: Exponent,
}

impl CostMonomial {
    pub(crate) fn conjugate(&self) -> Self {
        Self {
            cost_power: self.cost_power,
            anti: self.holo.clone(),
            holo: self.anti.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ComplexExact {
    re: Qsqrt2,
    im: Qsqrt2,
}

impl ComplexExact {
    const ZERO: Self = Self {
        re: Qsqrt2::ZERO,
        im: Qsqrt2::ZERO,
    };
    const ONE: Self = Self {
        re: Qsqrt2 {
            rational: Rational::ONE,
            sqrt2: Rational::ZERO,
        },
        im: Qsqrt2::ZERO,
    };
    const I: Self = Self {
        re: Qsqrt2::ZERO,
        im: Qsqrt2 {
            rational: Rational::ONE,
            sqrt2: Rational::ZERO,
        },
    };

    fn real(value: Qsqrt2) -> Self {
        Self {
            re: value,
            im: Qsqrt2::ZERO,
        }
    }

    fn conjugate(self) -> Self {
        Self {
            re: self.re,
            im: -self.im,
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

type Polynomial = BTreeMap<CostMonomial, ComplexExact>;

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct StationaryHausdorffStructure {
    pub order: u8,
    pub maximum_moment_degree: u8,
    pub occupation_moment_count: usize,
    pub terminal_moment_count: usize,
    pub liouville_equality_count: usize,
    pub occupation_moment_block_count: usize,
    pub occupation_interval_block_count: usize,
    pub occupation_interval_diagonal_count: usize,
    pub terminal_block_sides: [usize; 2],
    pub psd_block_sides: Vec<usize>,
    pub largest_psd_side: usize,
    pub sum_psd_squares: usize,
    pub sum_psd_cubes: usize,
    pub occupation_basis_hash: String,
    pub terminal_basis_hash: String,
    pub liouville_basis_hash: String,
    pub formulation_hash: String,
    pub exposure_upper: Rational,
    pub source_thread: &'static str,
    pub source_path: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct ArchivedHausdorffResult {
    pub objective: f64,
    pub reproduction_tolerance: f64,
    pub rigor: &'static str,
    pub source_path: &'static str,
}

#[derive(Clone, Debug)]
pub struct StationaryHausdorffProblem {
    pub structure: StationaryHausdorffStructure,
    pub conic: ConicProblem,
}

pub fn archived_mosek_result(order: u8) -> Option<ArchivedHausdorffResult> {
    let objective = match order {
        5 => 2.893_057_555_901_145_3,
        6 => 2.910_891_016_883_552,
        _ => return None,
    };
    Some(ArchivedHausdorffResult {
        objective,
        reproduction_tolerance: 1e-7,
        rigor: "exploratory",
        source_path: "verification_results/jan22_constraint_tightening/result.json",
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

fn shift(left: &CostMonomial, right: &CostMonomial) -> CostMonomial {
    CostMonomial {
        cost_power: left.cost_power + right.cost_power,
        anti: add_exponents(&left.anti, &right.anti),
        holo: add_exponents(&left.holo, &right.holo),
    }
}

fn is_normal(key: &CostMonomial, variables: usize) -> bool {
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

fn normal_form(key: &CostMonomial, variables: usize) -> BTreeMap<CostMonomial, i64> {
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
        CostMonomial {
            cost_power: key.cost_power,
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
                let sign = if power.is_multiple_of(2) { 1 } else { -1 };
                *expanded.entry(next).or_insert(0) += coefficient * sign * binomial(pairs, power);
            }
        }
        result = expanded;
    }
    result.retain(|_, coefficient| *coefficient != 0);
    result
}

fn cost_normal_invariant_monomials(
    variables: usize,
    maximum_degree: u16,
    charges: &[Charge],
) -> Vec<CostMonomial> {
    let mut result = Vec::new();
    for cost_power in 0..=maximum_degree {
        let complex_degree = maximum_degree - cost_power;
        let through_degree = monomials(variables, complex_degree);
        for anti in &through_degree {
            let remaining = complex_degree - anti.degree();
            let anti_charge = charge(anti, charges);
            for holo in monomials(variables, remaining) {
                let key = CostMonomial {
                    cost_power,
                    anti: anti.clone(),
                    holo,
                };
                if charge(&key.holo, charges) == anti_charge && is_normal(&key, variables) {
                    result.push(key);
                }
            }
        }
    }
    result
}

fn cost_normal_invariant_monomials_with_caps(
    variables: usize,
    maximum_cost_power: u16,
    charges: &[Charge],
    maximum_state_degree: impl Fn(u16) -> Option<u16>,
) -> Vec<CostMonomial> {
    let mut result = Vec::new();
    for cost_power in 0..=maximum_cost_power {
        let Some(complex_degree) = maximum_state_degree(cost_power) else {
            continue;
        };
        let through_degree = monomials(variables, complex_degree);
        for anti in &through_degree {
            let remaining = complex_degree - anti.degree();
            let anti_charge = charge(anti, charges);
            for holo in monomials(variables, remaining) {
                let key = CostMonomial {
                    cost_power,
                    anti: anti.clone(),
                    holo,
                };
                if charge(&key.holo, charges) == anti_charge && is_normal(&key, variables) {
                    result.push(key);
                }
            }
        }
    }
    result
}

fn weighted_state_degree(
    maximum_state_degree: u16,
    maximum_cost_power: u16,
    cost_power: u16,
) -> u16 {
    debug_assert!(maximum_cost_power > 0);
    debug_assert!(cost_power <= maximum_cost_power);
    let numerator = u32::from(maximum_state_degree) * u32::from(maximum_cost_power - cost_power);
    (numerator / u32::from(maximum_cost_power)) as u16
}

fn source_order_cost_mixed_basis(
    variables: usize,
    maximum_degree: u16,
    charges: &[Charge],
) -> Vec<(Charge, Vec<CostMonomial>)> {
    let mut positions = BTreeMap::new();
    let mut blocks: Vec<(Charge, Vec<CostMonomial>)> = Vec::new();
    for cost_power in 0..=maximum_degree {
        let complex_degree = maximum_degree - cost_power;
        let through_degree = monomials(variables, complex_degree);
        for anti in &through_degree {
            let remaining = complex_degree - anti.degree();
            let anti_charge = charge(anti, charges);
            for holo in monomials(variables, remaining) {
                let key = CostMonomial {
                    cost_power,
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
    }
    blocks
}

fn source_order_cost_mixed_basis_with_caps(
    variables: usize,
    maximum_cost_power: u16,
    charges: &[Charge],
    maximum_state_degree: impl Fn(u16) -> Option<u16>,
) -> Vec<(Charge, Vec<CostMonomial>)> {
    let mut positions = BTreeMap::new();
    let mut blocks: Vec<(Charge, Vec<CostMonomial>)> = Vec::new();
    for cost_power in 0..=maximum_cost_power {
        let Some(complex_degree) = maximum_state_degree(cost_power) else {
            continue;
        };
        let through_degree = monomials(variables, complex_degree);
        for anti in &through_degree {
            let remaining = complex_degree - anti.degree();
            let anti_charge = charge(anti, charges);
            for holo in monomials(variables, remaining) {
                let key = CostMonomial {
                    cost_power,
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
    }
    blocks
}

fn source_order_control_anisotropic_basis(
    order: u8,
    control_degree: u8,
    interval_localizer: bool,
) -> Vec<(Charge, Vec<CostMonomial>)> {
    let order = u16::from(order);
    let control_degree = u16::from(control_degree);
    let maximum_degree = order.max(control_degree);
    let mut positions = BTreeMap::new();
    let mut blocks: Vec<(Charge, Vec<CostMonomial>)> = Vec::new();
    for cost_power in 0..=order {
        let through_degree = monomials(BULK_VARIABLES, maximum_degree);
        for anti in &through_degree {
            let remaining = maximum_degree - anti.degree();
            let anti_charge = charge(anti, &BULK_CHARGES);
            for holo in monomials(BULK_VARIABLES, remaining) {
                let key = CostMonomial {
                    cost_power,
                    anti: anti.clone(),
                    holo,
                };
                if !is_normal(&key, BULK_VARIABLES) {
                    continue;
                }
                let u_degree = key.anti.0[U] + key.holo.0[U];
                let state_degree = key.anti.degree() + key.holo.degree() - u_degree;
                let support_degree = u16::from(interval_localizer);
                if u32::from(cost_power + state_degree + support_degree) * u32::from(control_degree)
                    + u32::from(u_degree) * u32::from(order)
                    > u32::from(order) * u32::from(control_degree)
                {
                    continue;
                }
                let holo_charge = charge(&key.holo, &BULK_CHARGES);
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
    }
    blocks
}

fn reflection_phase(key: &CostMonomial, variables: usize) -> ComplexExact {
    if variables == STATE_VARIABLES || (key.anti.0[U] + key.holo.0[U]).is_multiple_of(2) {
        ComplexExact::ONE
    } else {
        ComplexExact::I
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MomentSpace {
    pub(crate) keys: Vec<CostMonomial>,
    index: BTreeMap<CostMonomial, usize>,
}

impl MomentSpace {
    fn create(maximum_degree: u16) -> Self {
        Self::create_for(BULK_VARIABLES, maximum_degree, &BULK_CHARGES)
    }

    fn create_anisotropic(state_order: u8, xi_degree: u8) -> Self {
        if state_order == xi_degree {
            return Self::create(2 * u16::from(state_order));
        }
        let maximum_state_degree = 2 * u16::from(state_order);
        let maximum_cost_power = 2 * u16::from(xi_degree);
        let canonical = cost_normal_invariant_monomials_with_caps(
            BULK_VARIABLES,
            maximum_cost_power,
            &BULK_CHARGES,
            |cost_power| {
                Some(weighted_state_degree(
                    maximum_state_degree,
                    maximum_cost_power,
                    cost_power,
                ))
            },
        )
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

    fn create_for(variables: usize, maximum_degree: u16, charges: &[Charge]) -> Self {
        let canonical = cost_normal_invariant_monomials(variables, maximum_degree, charges)
            .into_iter()
            .map(|key| key.clone().min(key.conjugate()))
            .collect::<BTreeSet<_>>();
        Self::from_canonical(canonical)
    }

    fn from_canonical(canonical: BTreeSet<CostMonomial>) -> Self {
        let keys = canonical.into_iter().collect::<Vec<_>>();
        let index = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(position, key)| (key, position))
            .collect();
        Self { keys, index }
    }

    pub(crate) fn interface(order: u8) -> Self {
        let canonical =
            cost_normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order), &STATE_CHARGES)
                .into_iter()
                .filter(|key| key.cost_power == 0)
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

    pub(crate) fn position(&self, key: &CostMonomial) -> usize {
        self.index[&key.clone().min(key.conjugate())]
    }

    fn coefficient(&self, key: &CostMonomial, coefficient: ComplexExact) -> (usize, Qsqrt2) {
        let canonical = key.clone().min(key.conjugate());
        let position = self.index[&canonical];
        let phase = reflection_phase(&canonical, BULK_VARIABLES);
        let phase = if *key == canonical {
            phase
        } else {
            phase.conjugate()
        };
        let value = coefficient * phase;
        assert_eq!(value.im, Qsqrt2::ZERO);
        (position, value.re)
    }
}

fn gram_entry(left: &CostMonomial, right: &CostMonomial) -> CostMonomial {
    CostMonomial {
        cost_power: left.cost_power + right.cost_power,
        anti: add_exponents(&left.holo, &right.anti),
        holo: add_exponents(&left.anti, &right.holo),
    }
}

type ZeroCostCharacter = (u16, i32, i32, i32);
type ZeroCostGroup = (ZeroCostCharacter, Vec<usize>);

fn integer_zero_cost_face(basis: &[CostMonomial]) -> Vec<Vec<(usize, i64)>> {
    let mut columns = Vec::new();
    let mut group_positions = BTreeMap::new();
    let mut groups: Vec<ZeroCostGroup> = Vec::new();
    for (index, key) in basis.iter().enumerate() {
        if key.anti.0[R1] != 0 || key.holo.0[R1] != 0 || key.anti.0[R2] != 0 || key.holo.0[R2] != 0
        {
            columns.push(vec![(index, 1)]);
        } else {
            let character = (
                key.cost_power,
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

fn identity_face(size: usize) -> Vec<Vec<(usize, i64)>> {
    (0..size).map(|index| vec![(index, 1)]).collect()
}

fn state_to_bulk(key: &CostMonomial) -> CostMonomial {
    let mut anti = vec![0];
    anti.extend(&key.anti.0);
    let mut holo = vec![0];
    holo.extend(&key.holo.0);
    CostMonomial {
        cost_power: key.cost_power,
        anti: Exponent(anti),
        holo: Exponent(holo),
    }
}

fn exponent_with(variables: usize, index: usize) -> Exponent {
    let mut exponent = vec![0; variables];
    exponent[index] = 1;
    Exponent(exponent)
}

fn add_term(polynomial: &mut Polynomial, key: CostMonomial, coefficient: ComplexExact) {
    let value = polynomial.get(&key).copied().unwrap_or(ComplexExact::ZERO) + coefficient;
    if value == ComplexExact::ZERO {
        polynomial.remove(&key);
    } else {
        polynomial.insert(key, value);
    }
}

fn state_liouville_derivative(test: &CostMonomial) -> Polynomial {
    let mut derivative = Polynomial::new();
    for (ground, rydberg, kappa) in [
        (0, 1, Qsqrt2::new(Rational::new(1, 2), Rational::ZERO)),
        (2, 3, Qsqrt2::new(Rational::ZERO, Rational::new(1, 2))),
    ] {
        if test.holo.0[ground] != 0 {
            let mut reduced = test.clone();
            reduced.holo.0[ground] -= 1;
            let base = state_to_bulk(&reduced);
            let mut factor = zero_key(BULK_VARIABLES);
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
            let factor = CostMonomial {
                cost_power: 0,
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
            let mut factor = zero_key(BULK_VARIABLES);
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
            let factor = CostMonomial {
                cost_power: 0,
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

fn zero_key(variables: usize) -> CostMonomial {
    CostMonomial {
        cost_power: 0,
        anti: Exponent(vec![0; variables]),
        holo: Exponent(vec![0; variables]),
    }
}

fn running_cost() -> [(CostMonomial, Qsqrt2); 2] {
    [(R1, Rational::new(1, 2)), (R2, Rational::new(1, 4))].map(|(variable, coefficient)| {
        let exponent = exponent_with(BULK_VARIABLES, variable);
        (
            CostMonomial {
                cost_power: 0,
                anti: exponent.clone(),
                holo: exponent,
            },
            Qsqrt2::new(coefficient, Rational::ZERO),
        )
    })
}

fn cost_liouville_derivative(test: &CostMonomial) -> Polynomial {
    let mut derivative = state_liouville_derivative(test);
    if test.cost_power != 0 {
        let mut state_factor = state_to_bulk(test);
        state_factor.cost_power -= 1;
        for (cost_key, coefficient) in running_cost() {
            add_term(
                &mut derivative,
                shift(&state_factor, &cost_key),
                ComplexExact::real(
                    Qsqrt2::from(i64::from(test.cost_power))
                        * coefficient
                        * Qsqrt2::new(
                            Rational::new(EXPOSURE_UPPER.denominator, EXPOSURE_UPPER.numerator),
                            Rational::ZERO,
                        ),
                ),
            );
        }
    }
    reduce_polynomial(&derivative)
}

pub(crate) fn scaled_liouville_coefficients(
    test: &CostMonomial,
    inverse_cell_width: Rational,
    moments: &MomentSpace,
) -> Vec<(usize, Qsqrt2)> {
    let mut derivative = state_liouville_derivative(test);
    if test.cost_power != 0 {
        let mut state_factor = state_to_bulk(test);
        state_factor.cost_power -= 1;
        for (cost_key, coefficient) in running_cost() {
            add_term(
                &mut derivative,
                shift(&state_factor, &cost_key),
                ComplexExact::real(
                    Qsqrt2::from(i64::from(test.cost_power))
                        * coefficient
                        * Qsqrt2::new(
                            Rational::new(EXPOSURE_UPPER.denominator, EXPOSURE_UPPER.numerator),
                            Rational::ZERO,
                        )
                        * Qsqrt2::new(inverse_cell_width, Rational::ZERO),
                ),
            );
        }
    }
    reduce_polynomial(&derivative)
        .into_iter()
        .map(|(key, coefficient)| moments.coefficient(&key, coefficient))
        .collect()
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

pub(crate) fn initial_value(test: &CostMonomial) -> i64 {
    if test.cost_power != 0
        || [1, 3]
            .iter()
            .any(|&index| test.anti.0[index] != 0 || test.holo.0[index] != 0)
    {
        0
    } else {
        1
    }
}

pub(crate) fn target_value(test: &CostMonomial) -> i64 {
    if [1, 3]
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BlockFamily {
    Occupation,
    TerminalMoment,
    TerminalInterval,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum HausdorffGramFamily {
    OccupationMoment,
    OccupationXiOneMinusXi,
    OccupationIntervalDiagonal,
    TerminalMoment,
    TerminalXiOneMinusXi,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum HausdorffBasisBound {
    RydbergCostRelativeOccupationMonomials,
    UnitIntervalTerminalMonomials,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum HausdorffLocalizer {
    One,
    XiOneMinusXi,
}

#[derive(Clone, Debug)]
pub(crate) struct ExactGramShiftMetadata {
    pub(crate) family: HausdorffGramFamily,
    pub(crate) basis_bound: HausdorffBasisBound,
    pub(crate) localizer: HausdorffLocalizer,
    pub(crate) basis_size: usize,
    /// Exact pre-transform basis in native assembly order.
    pub(crate) basis: Vec<CostMonomial>,
    /// `None` means the basis monomial can remain nonzero when c=0.
    pub(crate) basis_cost_ratios: Vec<Option<Rational>>,
    /// Rows are Gram coordinates: row i is sum_j weight(i,j) z_j.
    pub(crate) transform_rows: Vec<Vec<(usize, i64)>>,
}

fn monomial_cost_ratio(key: &CostMonomial) -> Option<Rational> {
    if key.anti.0[R1] != 0 || key.holo.0[R1] != 0 {
        // |z|^2 <= |r1|^2 <= 2c.
        Some(Rational::new(2, 1))
    } else if key.anti.0[R2] != 0 || key.holo.0[R2] != 0 {
        // |z|^2 <= |r2|^2 <= 4c.
        Some(Rational::new(4, 1))
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OccupationBlockKind {
    Moment,
    Interval,
    IntervalDiagonal,
}

#[derive(Clone, Debug)]
pub(crate) struct ExactGramBlock {
    family: BlockFamily,
    pub(crate) kind: Option<OccupationBlockKind>,
    pub(crate) charge: Charge,
    pub(crate) basis: Vec<CostMonomial>,
    pub(crate) face: Vec<Vec<(usize, i64)>>,
    pub(crate) support: Vec<(u16, i64)>,
    terminal_side: usize,
}

fn occupation_blocks(order: u8) -> (Vec<ExactGramBlock>, [usize; 3]) {
    occupation_blocks_with_active_time_cap(order, false)
}

fn active_time_capped_occupation_blocks(order: u8) -> (Vec<ExactGramBlock>, [usize; 3]) {
    occupation_blocks_with_active_time_cap(order, true)
}

fn occupation_blocks_with_active_time_cap(
    order: u8,
    active_time_capped: bool,
) -> (Vec<ExactGramBlock>, [usize; 3]) {
    let base = source_order_cost_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES);
    let support =
        source_order_cost_mixed_basis(BULK_VARIABLES, u16::from(order) - 1, &BULK_CHARGES);
    let mut blocks = base
        .into_iter()
        .filter_map(|(charge, basis)| {
            let face = if active_time_capped {
                identity_face(basis.len())
            } else {
                integer_zero_cost_face(&basis)
            };
            (!face.is_empty()).then_some(ExactGramBlock {
                family: BlockFamily::Occupation,
                kind: Some(OccupationBlockKind::Moment),
                charge,
                basis,
                face,
                support: vec![(0, 1)],
                terminal_side: 0,
            })
        })
        .collect::<Vec<_>>();
    let base_count = blocks.len();
    for (charge, basis) in &support {
        blocks.push(ExactGramBlock {
            family: BlockFamily::Occupation,
            kind: Some(OccupationBlockKind::Interval),
            charge: *charge,
            face: identity_face(basis.len()),
            basis: basis.clone(),
            support: vec![(1, 1), (2, -1)],
            terminal_side: 0,
        });
    }
    let support_count = blocks.len() - base_count;

    let mut signatures = BTreeSet::new();
    for (charge, basis) in support {
        for monomial in basis {
            let signature = interval_diagonal_signature(&monomial);
            if signatures.insert(signature) {
                blocks.push(ExactGramBlock {
                    family: BlockFamily::Occupation,
                    kind: Some(OccupationBlockKind::IntervalDiagonal),
                    charge,
                    basis: vec![monomial],
                    face: vec![vec![(0, 1)]],
                    support: vec![(1, 1), (2, -1)],
                    terminal_side: 0,
                });
            }
        }
    }
    let diagonal_count = blocks.len() - base_count - support_count;
    (blocks, [base_count, support_count, diagonal_count])
}

fn anisotropic_occupation_blocks(
    state_order: u8,
    xi_degree: u8,
) -> (Vec<ExactGramBlock>, [usize; 3]) {
    if state_order == xi_degree {
        return occupation_blocks(state_order);
    }
    let state_order = u16::from(state_order);
    let xi_degree = u16::from(xi_degree);
    let base = source_order_cost_mixed_basis_with_caps(
        BULK_VARIABLES,
        xi_degree,
        &BULK_CHARGES,
        |cost_power| Some(weighted_state_degree(state_order, xi_degree, cost_power)),
    );
    let support = source_order_cost_mixed_basis_with_caps(
        BULK_VARIABLES,
        xi_degree - 1,
        &BULK_CHARGES,
        |cost_power| {
            Some(weighted_state_degree(
                state_order,
                xi_degree,
                cost_power + 1,
            ))
        },
    );
    let mut blocks = base
        .into_iter()
        .filter_map(|(charge, basis)| {
            let face = integer_zero_cost_face(&basis);
            (!face.is_empty()).then_some(ExactGramBlock {
                family: BlockFamily::Occupation,
                kind: Some(OccupationBlockKind::Moment),
                charge,
                basis,
                face,
                support: vec![(0, 1)],
                terminal_side: 0,
            })
        })
        .collect::<Vec<_>>();
    let base_count = blocks.len();
    for (charge, basis) in &support {
        blocks.push(ExactGramBlock {
            family: BlockFamily::Occupation,
            kind: Some(OccupationBlockKind::Interval),
            charge: *charge,
            face: identity_face(basis.len()),
            basis: basis.clone(),
            support: vec![(1, 1), (2, -1)],
            terminal_side: 0,
        });
    }
    let support_count = blocks.len() - base_count;

    let mut signatures = BTreeSet::new();
    for (charge, basis) in support {
        for monomial in basis {
            let signature = interval_diagonal_signature(&monomial);
            if signatures.insert(signature) {
                blocks.push(ExactGramBlock {
                    family: BlockFamily::Occupation,
                    kind: Some(OccupationBlockKind::IntervalDiagonal),
                    charge,
                    basis: vec![monomial],
                    face: vec![vec![(0, 1)]],
                    support: vec![(1, 1), (2, -1)],
                    terminal_side: 0,
                });
            }
        }
    }
    let diagonal_count = blocks.len() - base_count - support_count;
    (blocks, [base_count, support_count, diagonal_count])
}

fn control_anisotropic_occupation_blocks(
    order: u8,
    control_degree: u8,
) -> Result<(Vec<ExactGramBlock>, [usize; 3]), String> {
    if control_degree < order {
        return Err(format!(
            "split --u-degree {control_degree} must be at least the state/cost order {order}"
        ));
    }
    if control_degree == order {
        return Ok(occupation_blocks(order));
    }
    let base = source_order_control_anisotropic_basis(order, control_degree, false);
    let support = source_order_control_anisotropic_basis(order, control_degree, true);
    let mut blocks = base
        .into_iter()
        .filter_map(|(charge, basis)| {
            let face = integer_zero_cost_face(&basis);
            (!face.is_empty()).then_some(ExactGramBlock {
                family: BlockFamily::Occupation,
                kind: Some(OccupationBlockKind::Moment),
                charge,
                basis,
                face,
                support: vec![(0, 1)],
                terminal_side: 0,
            })
        })
        .collect::<Vec<_>>();
    let base_count = blocks.len();
    for (charge, basis) in &support {
        blocks.push(ExactGramBlock {
            family: BlockFamily::Occupation,
            kind: Some(OccupationBlockKind::Interval),
            charge: *charge,
            face: identity_face(basis.len()),
            basis: basis.clone(),
            support: vec![(1, 1), (2, -1)],
            terminal_side: 0,
        });
    }
    let support_count = blocks.len() - base_count;
    let mut signatures = BTreeSet::new();
    for (charge, basis) in support {
        for monomial in basis {
            let signature = interval_diagonal_signature(&monomial);
            if signatures.insert(signature) {
                blocks.push(ExactGramBlock {
                    family: BlockFamily::Occupation,
                    kind: Some(OccupationBlockKind::IntervalDiagonal),
                    charge,
                    basis: vec![monomial],
                    face: vec![vec![(0, 1)]],
                    support: vec![(1, 1), (2, -1)],
                    terminal_side: 0,
                });
            }
        }
    }
    let diagonal_count = blocks.len() - base_count - support_count;
    Ok((blocks, [base_count, support_count, diagonal_count]))
}

fn append_rydberg_localizer_blocks(
    order: u8,
    charges: &[Charge],
    blocks: &mut Vec<ExactGramBlock>,
) -> Result<(), String> {
    let source = source_order_cost_mixed_basis(BULK_VARIABLES, order.into(), &BULK_CHARGES)
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    for &charge in charges {
        let charge = canonical_charge(charge)?;
        let basis = source
            .get(&charge)
            .ok_or_else(|| format!("charge sector {charge:?} is absent at order {order}"))?;
        for (rydberg, rydberg_charge) in [(R1, BULK_CHARGES[R1]), (R2, BULK_CHARGES[R2])] {
            let shifted = basis
                .iter()
                .cloned()
                .map(|mut key| {
                    key.holo.0[rydberg] += 1;
                    key
                })
                .collect::<Vec<_>>();
            let shifted_charge =
                canonical_charge((charge.0 + rydberg_charge.0, charge.1 + rydberg_charge.1))?;
            blocks.push(ExactGramBlock {
                family: BlockFamily::Occupation,
                kind: Some(OccupationBlockKind::Moment),
                charge: shifted_charge,
                face: identity_face(shifted.len()),
                basis: shifted,
                support: vec![(0, 1)],
                terminal_side: 0,
            });
        }
    }
    Ok(())
}

fn enriched_occupation_blocks(
    order: u8,
    enrichment: &ChargeEnrichment,
) -> Result<(Vec<ExactGramBlock>, [usize; 3]), String> {
    let (mut blocks, mut counts) = occupation_blocks(order);
    append_charge_enrichment(order, enrichment, &mut blocks, &mut counts)?;
    Ok((blocks, counts))
}

fn append_charge_enrichment(
    order: u8,
    enrichment: &ChargeEnrichment,
    blocks: &mut Vec<ExactGramBlock>,
    counts: &mut [usize; 3],
) -> Result<(), String> {
    let enriched_order = order
        .checked_add(enrichment.extra_degree)
        .ok_or("enriched order overflows u8")?;
    let enriched_moment =
        source_order_cost_mixed_basis(BULK_VARIABLES, u16::from(enriched_order), &BULK_CHARGES)
            .into_iter()
            .collect::<BTreeMap<_, _>>();
    let enriched_interval =
        source_order_cost_mixed_basis(BULK_VARIABLES, u16::from(enriched_order) - 1, &BULK_CHARGES)
            .into_iter()
            .collect::<BTreeMap<_, _>>();
    let baseline_charges = blocks
        .iter()
        .filter(|block| block.kind == Some(OccupationBlockKind::Moment))
        .map(|block| block.charge)
        .collect::<BTreeSet<_>>();
    for &charge in &enrichment.charges {
        if !baseline_charges.contains(&charge) {
            return Err(format!(
                "charge sector {charge:?} is absent from the order-{order} occupation moment blocks"
            ));
        }
        let basis = enriched_moment
            .get(&charge)
            .ok_or_else(|| format!("charge sector {charge:?} has no enriched moment basis"))?;
        let face = integer_zero_cost_face(basis)
            .into_iter()
            .filter(|column| {
                column
                    .iter()
                    .any(|&(position, _)| total_degree(&basis[position]) > u16::from(order))
            })
            .collect::<Vec<_>>();
        if face.is_empty() {
            return Err(format!(
                "charge sector {charge:?} has no new enriched facial directions"
            ));
        }
        blocks.push(ExactGramBlock {
            family: BlockFamily::Occupation,
            kind: Some(OccupationBlockKind::Moment),
            charge,
            basis: basis.clone(),
            face,
            support: vec![(0, 1)],
            terminal_side: 0,
        });
        counts[0] += 1;

        let basis = enriched_interval
            .get(&charge)
            .ok_or_else(|| format!("charge sector {charge:?} has no enriched interval basis"))?;
        let basis = basis
            .iter()
            .filter(|key| total_degree(key) > u16::from(order) - 1)
            .cloned()
            .collect::<Vec<_>>();
        if basis.is_empty() {
            return Err(format!(
                "charge sector {charge:?} has no new enriched interval directions"
            ));
        }
        blocks.push(ExactGramBlock {
            family: BlockFamily::Occupation,
            kind: Some(OccupationBlockKind::Interval),
            charge,
            basis: basis.clone(),
            face: identity_face(basis.len()),
            support: vec![(1, 1), (2, -1)],
            terminal_side: 0,
        });
        counts[1] += 1;
    }
    Ok(())
}

fn merge_charge_enrichment(
    order: u8,
    enrichment: &ChargeEnrichment,
    blocks: &mut Vec<ExactGramBlock>,
) -> Result<(), String> {
    let original_len = blocks.len();
    let mut ignored_counts = [0; 3];
    append_charge_enrichment(order, enrichment, blocks, &mut ignored_counts)?;
    let candidates = blocks.drain(original_len..).collect::<Vec<_>>();
    for candidate in candidates {
        let matches = blocks
            .iter()
            .enumerate()
            .filter(|(_, block)| block.kind == candidate.kind && block.charge == candidate.charge)
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let [target] = matches.as_slice() else {
            return Err(format!(
                "charge sector {:?} has {} matching {:?} anisotropic blocks; expected exactly one",
                candidate.charge,
                matches.len(),
                candidate.kind
            ));
        };
        merge_gram_face_span(&mut blocks[*target], &candidate)?;
    }
    Ok(())
}

fn merge_gram_face_span(
    target: &mut ExactGramBlock,
    candidate: &ExactGramBlock,
) -> Result<(), String> {
    if target.family != candidate.family
        || target.kind != candidate.kind
        || target.charge != candidate.charge
        || target.support != candidate.support
    {
        return Err("cannot merge incompatible Gram blocks".into());
    }

    let mut positions = target
        .basis
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, key)| (key, index))
        .collect::<BTreeMap<_, _>>();
    let mut candidate_to_target = Vec::with_capacity(candidate.basis.len());
    for key in &candidate.basis {
        let position = match positions.get(key) {
            Some(&position) => position,
            None => {
                let position = target.basis.len();
                target.basis.push(key.clone());
                positions.insert(key.clone(), position);
                position
            }
        };
        candidate_to_target.push(position);
    }

    let mut span = ExactColumnSpan::default();
    for column in &target.face {
        if !span.insert(column) {
            return Err("anisotropic Gram face contains dependent columns".into());
        }
    }
    for column in &candidate.face {
        let remapped = column
            .iter()
            .map(|&(position, coefficient)| (candidate_to_target[position], coefficient))
            .collect::<Vec<_>>();
        if span.insert(&remapped) {
            target.face.push(remapped);
        }
    }
    Ok(())
}

#[derive(Default)]
struct ExactColumnSpan {
    pivots: BTreeMap<usize, BTreeMap<usize, BigRational>>,
}

impl ExactColumnSpan {
    fn insert(&mut self, column: &[(usize, i64)]) -> bool {
        let mut reduced = column
            .iter()
            .map(|&(position, coefficient)| {
                (
                    position,
                    BigRational::from_integer(BigInt::from(coefficient)),
                )
            })
            .collect::<BTreeMap<_, _>>();
        reduced.retain(|_, coefficient| !coefficient.is_zero());
        while let Some((&pivot, coefficient)) = reduced.first_key_value() {
            let coefficient = coefficient.clone();
            let Some(existing) = self.pivots.get(&pivot) else {
                for value in reduced.values_mut() {
                    *value /= coefficient.clone();
                }
                self.pivots.insert(pivot, reduced);
                return true;
            };
            for (&position, value) in existing {
                let entry = reduced.entry(position).or_default();
                *entry -= coefficient.clone() * value;
            }
            reduced.retain(|_, value| !value.is_zero());
        }
        false
    }
}

fn total_degree(key: &CostMonomial) -> u16 {
    key.cost_power + key.anti.degree() + key.holo.degree()
}

fn moment_space_for_blocks(order: u8, blocks: &[ExactGramBlock]) -> MomentSpace {
    moment_space_extending(MomentSpace::create(2 * u16::from(order)), blocks)
}

fn moment_space_extending(base: MomentSpace, blocks: &[ExactGramBlock]) -> MomentSpace {
    let mut keys = base.keys.into_iter().collect::<BTreeSet<_>>();
    keys.extend(gram_moment_keys(blocks));
    MomentSpace::from_canonical(keys)
}

fn gram_moment_keys(blocks: &[ExactGramBlock]) -> BTreeSet<CostMonomial> {
    let mut keys = BTreeSet::new();
    for block in blocks {
        for left_face in &block.face {
            for right_face in &block.face {
                for &(left_index, _) in left_face {
                    for &(right_index, _) in right_face {
                        for &(cost_shift, _) in &block.support {
                            let mut entry =
                                gram_entry(&block.basis[left_index], &block.basis[right_index]);
                            entry.cost_power += cost_shift;
                            keys.extend(
                                normal_form(&entry, BULK_VARIABLES)
                                    .into_keys()
                                    .map(|key| key.clone().min(key.conjugate())),
                            );
                        }
                    }
                }
            }
        }
    }
    keys
}

fn interval_diagonal_signature(monomial: &CostMonomial) -> Vec<(CostMonomial, i64)> {
    let entry = gram_entry(monomial, monomial);
    let mut polynomial = BTreeMap::new();
    for (power, weight) in [(1, 1_i64), (2, -1_i64)] {
        let mut shifted = entry.clone();
        shifted.cost_power += power;
        for (key, coefficient) in normal_form(&shifted, BULK_VARIABLES) {
            *polynomial.entry(key).or_insert(0) += weight * coefficient;
        }
    }
    polynomial.retain(|_, coefficient| *coefficient != 0);
    polynomial.into_iter().collect()
}

#[derive(Clone, Debug)]
pub(crate) struct ExactLiouvilleRow {
    pub(crate) initial: i64,
    pub(crate) coefficients: Vec<(usize, Qsqrt2)>,
}

#[derive(Clone, Debug)]
pub(crate) struct ExactCertificateModel {
    moments: MomentSpace,
    pub(crate) cost: Vec<(usize, Qsqrt2)>,
    pub(crate) equalities: Vec<ExactLiouvilleRow>,
    pub(crate) normalization_position: usize,
    blocks: Vec<ExactGramBlock>,
    coefficient_count: usize,
}

impl ExactCertificateModel {
    pub(crate) fn moments(&self) -> &MomentSpace {
        &self.moments
    }

    pub(crate) fn coefficient_count(&self) -> usize {
        self.coefficient_count
    }

    pub(crate) fn gram_dimensions(&self) -> Vec<usize> {
        self.blocks
            .iter()
            .map(|block| match block.family {
                BlockFamily::Occupation => block.face.len(),
                BlockFamily::TerminalMoment | BlockFamily::TerminalInterval => block.terminal_side,
            })
            .collect()
    }

    pub(crate) fn occupation_gram_count(&self) -> usize {
        self.blocks
            .iter()
            .take_while(|block| block.family == BlockFamily::Occupation)
            .count()
    }

    pub(crate) fn occupation_gram_dimensions(&self) -> Vec<usize> {
        self.gram_dimensions()[..self.occupation_gram_count()].to_vec()
    }

    pub(crate) fn gram_shift_metadata(&self) -> Vec<ExactGramShiftMetadata> {
        self.blocks
            .iter()
            .map(|block| match block.family {
                BlockFamily::Occupation => {
                    let (family, localizer) = match block.kind.expect("occupation block has a kind")
                    {
                        OccupationBlockKind::Moment => (
                            HausdorffGramFamily::OccupationMoment,
                            HausdorffLocalizer::One,
                        ),
                        OccupationBlockKind::Interval => (
                            HausdorffGramFamily::OccupationXiOneMinusXi,
                            HausdorffLocalizer::XiOneMinusXi,
                        ),
                        OccupationBlockKind::IntervalDiagonal => (
                            HausdorffGramFamily::OccupationIntervalDiagonal,
                            HausdorffLocalizer::XiOneMinusXi,
                        ),
                    };
                    ExactGramShiftMetadata {
                        family,
                        basis_bound: HausdorffBasisBound::RydbergCostRelativeOccupationMonomials,
                        localizer,
                        basis_size: block.basis.len(),
                        basis: block.basis.clone(),
                        basis_cost_ratios: block.basis.iter().map(monomial_cost_ratio).collect(),
                        transform_rows: block.face.clone(),
                    }
                }
                BlockFamily::TerminalMoment | BlockFamily::TerminalInterval => {
                    ExactGramShiftMetadata {
                        family: if block.family == BlockFamily::TerminalMoment {
                            HausdorffGramFamily::TerminalMoment
                        } else {
                            HausdorffGramFamily::TerminalXiOneMinusXi
                        },
                        basis_bound: HausdorffBasisBound::UnitIntervalTerminalMonomials,
                        localizer: if block.family == BlockFamily::TerminalMoment {
                            HausdorffLocalizer::One
                        } else {
                            HausdorffLocalizer::XiOneMinusXi
                        },
                        basis_size: block.terminal_side,
                        basis: (0..block.terminal_side)
                            .map(|power| {
                                let mut key = zero_key(BULK_VARIABLES);
                                key.cost_power = power as u16;
                                key
                            })
                            .collect(),
                        basis_cost_ratios: vec![Some(Rational::ONE); block.terminal_side],
                        transform_rows: identity_face(block.terminal_side),
                    }
                }
            })
            .collect()
    }

    pub(crate) fn occupation_blocks(&self) -> &[ExactGramBlock] {
        &self.blocks[..self.occupation_gram_count()]
    }

    pub(crate) fn occupation_block_counts(&self) -> [usize; 3] {
        let mut counts = [0; 3];
        for block in self.occupation_blocks() {
            match block.kind.expect("occupation block has a kind") {
                OccupationBlockKind::Moment => counts[0] += 1,
                OccupationBlockKind::Interval => counts[1] += 1,
                OccupationBlockKind::IntervalDiagonal => counts[2] += 1,
            }
        }
        counts
    }

    pub(crate) fn for_each_gram_entry_coefficient(
        &self,
        block_index: usize,
        row: usize,
        column: usize,
        mut visit: impl FnMut(usize, Qsqrt2),
    ) {
        let block = &self.blocks[block_index];
        match block.family {
            BlockFamily::Occupation => {
                for &(left_index, left_weight) in &block.face[row] {
                    for &(right_index, right_weight) in &block.face[column] {
                        let left = &block.basis[left_index];
                        let right = &block.basis[right_index];
                        let phase = reflection_phase(left, BULK_VARIABLES).conjugate()
                            * reflection_phase(right, BULK_VARIABLES);
                        for &(cost_shift, support_weight) in &block.support {
                            let mut entry = gram_entry(left, right);
                            entry.cost_power += cost_shift;
                            for (key, normal_coefficient) in normal_form(&entry, BULK_VARIABLES) {
                                let integer = normal_coefficient
                                    * left_weight
                                    * right_weight
                                    * support_weight;
                                let coefficient = phase * ComplexExact::real(Qsqrt2::from(integer));
                                let (position, value) = self.moments.coefficient(&key, coefficient);
                                visit(position, value);
                            }
                        }
                    }
                }
            }
            BlockFamily::TerminalMoment => {
                visit(self.moments.keys.len() + row + column, Qsqrt2::from(1));
            }
            BlockFamily::TerminalInterval => {
                let offset = self.moments.keys.len() + row + column;
                visit(offset + 1, Qsqrt2::from(1));
                visit(offset + 2, Qsqrt2::from(-1));
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct AnisotropicOccupationModel {
    moments: MomentSpace,
    cost: Vec<(usize, Qsqrt2)>,
    blocks: Vec<ExactGramBlock>,
    block_counts: [usize; 3],
}

impl AnisotropicOccupationModel {
    pub(crate) fn create_with_enrichment(
        state_order: u8,
        xi_degree: u8,
        enrichment: Option<&ChargeEnrichment>,
    ) -> Result<Self, String> {
        if state_order < 2 {
            return Err("stationary-torus Hausdorff-lift order must be at least two".into());
        }
        if xi_degree < state_order {
            return Err(format!(
                "split --xi-degree {xi_degree} must be at least the state order {state_order}"
            ));
        }
        let base_moments = MomentSpace::create_anisotropic(state_order, xi_degree);
        let (mut blocks, block_counts) = anisotropic_occupation_blocks(state_order, xi_degree);
        if let Some(enrichment) = enrichment {
            merge_charge_enrichment(state_order, enrichment, &mut blocks)?;
        }
        let moments = if enrichment.is_some() {
            moment_space_extending(base_moments, &blocks)
        } else {
            base_moments
        };
        let cost = running_cost()
            .into_iter()
            .map(|(key, coefficient)| (moments.index[&key], coefficient))
            .collect();
        Ok(Self {
            moments,
            cost,
            blocks,
            block_counts,
        })
    }

    pub(crate) fn moments(&self) -> &MomentSpace {
        &self.moments
    }

    pub(crate) fn cost(&self) -> &[(usize, Qsqrt2)] {
        &self.cost
    }

    pub(crate) fn gram_dimensions(&self) -> Vec<usize> {
        self.blocks.iter().map(|block| block.face.len()).collect()
    }

    pub(crate) fn block_counts(&self) -> [usize; 3] {
        self.block_counts
    }

    pub(crate) fn for_each_gram_entry_coefficient(
        &self,
        block_index: usize,
        row: usize,
        column: usize,
        mut visit: impl FnMut(usize, Qsqrt2),
    ) {
        let block = &self.blocks[block_index];
        debug_assert_eq!(block.family, BlockFamily::Occupation);
        for &(left_index, left_weight) in &block.face[row] {
            for &(right_index, right_weight) in &block.face[column] {
                let left = &block.basis[left_index];
                let right = &block.basis[right_index];
                let phase = reflection_phase(left, BULK_VARIABLES).conjugate()
                    * reflection_phase(right, BULK_VARIABLES);
                for &(cost_shift, support_weight) in &block.support {
                    let mut entry = gram_entry(left, right);
                    entry.cost_power += cost_shift;
                    for (key, normal_coefficient) in normal_form(&entry, BULK_VARIABLES) {
                        let integer =
                            normal_coefficient * left_weight * right_weight * support_weight;
                        let coefficient = phase * ComplexExact::real(Qsqrt2::from(integer));
                        let (position, value) = self.moments.coefficient(&key, coefficient);
                        visit(position, value);
                    }
                }
            }
        }
    }
}

pub(crate) fn liouville_tests(order: u8) -> Vec<CostMonomial> {
    cost_normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
        .into_iter()
        .filter(|key| *key <= key.conjugate())
        .collect()
}

pub(crate) fn anisotropic_liouville_tests(
    state_order: u8,
    xi_degree: u8,
) -> Result<Vec<CostMonomial>, String> {
    if state_order < 2 {
        return Err("stationary-torus Hausdorff-lift order must be at least two".into());
    }
    if xi_degree < state_order {
        return Err(format!(
            "split --xi-degree {xi_degree} must be at least the state order {state_order}"
        ));
    }
    if xi_degree == state_order {
        return Ok(liouville_tests(state_order));
    }
    let maximum_state_degree = 2 * u16::from(state_order);
    let maximum_cost_power = 2 * u16::from(xi_degree);
    Ok(cost_normal_invariant_monomials_with_caps(
        STATE_VARIABLES,
        maximum_cost_power,
        &STATE_CHARGES,
        |cost_power| {
            let state_derivative_cap =
                weighted_state_degree(maximum_state_degree, maximum_cost_power, cost_power)
                    .checked_sub(1)?;
            if cost_power == 0 {
                Some(state_derivative_cap)
            } else {
                let cost_derivative_cap =
                    weighted_state_degree(maximum_state_degree, maximum_cost_power, cost_power - 1)
                        .checked_sub(2)?;
                Some(state_derivative_cap.min(cost_derivative_cap))
            }
        },
    )
    .into_iter()
    .filter(|key| *key <= key.conjugate())
    .collect())
}

pub(crate) fn interface_gram_bases(order: u8) -> Vec<Vec<CostMonomial>> {
    source_order_cost_mixed_basis(STATE_VARIABLES, order.into(), &STATE_CHARGES)
        .into_iter()
        .filter_map(|(_, basis)| {
            let basis = basis
                .into_iter()
                .filter(|key| key.cost_power == 0)
                .collect::<Vec<_>>();
            (!basis.is_empty()).then_some(basis)
        })
        .collect()
}

pub(crate) fn interface_gram_entry_coefficients(
    moments: &MomentSpace,
    left: &CostMonomial,
    right: &CostMonomial,
) -> Vec<(usize, Qsqrt2)> {
    normal_form(&gram_entry(left, right), STATE_VARIABLES)
        .into_iter()
        .map(|(key, coefficient)| (moments.position(&key), Qsqrt2::from(coefficient)))
        .collect()
}

pub(crate) fn rate_localizer_gram_bases(order: u8, variables: usize) -> Vec<Vec<CostMonomial>> {
    assert!(variables == BULK_VARIABLES || variables == STATE_VARIABLES);
    let charges = if variables == BULK_VARIABLES {
        &BULK_CHARGES[..]
    } else {
        &STATE_CHARGES[..]
    };
    source_order_cost_mixed_basis(variables, u16::from(order.saturating_sub(2)), charges)
        .into_iter()
        .filter_map(|(_, basis)| {
            let basis = if variables == STATE_VARIABLES {
                basis
                    .into_iter()
                    .filter(|key| key.cost_power == 0)
                    .collect()
            } else {
                basis
            };
            (!basis.is_empty()).then_some(basis)
        })
        .collect()
}

pub(crate) fn rate_localizer_gram_entry_coefficients(
    moments: &MomentSpace,
    left: &CostMonomial,
    right: &CostMonomial,
    lower: Rational,
    upper: Rational,
    variables: usize,
) -> Vec<(usize, Qsqrt2)> {
    assert!(variables == BULK_VARIABLES || variables == STATE_VARIABLES);
    let width = upper - lower;
    assert!(width.numerator > 0);
    let inverse_width = Rational::new(width.denominator, width.numerator);
    let normalization = Qsqrt2::new(inverse_width * inverse_width, Rational::ZERO);
    let mut polynomial = BTreeMap::<CostMonomial, Qsqrt2>::new();
    let entry = gram_entry(left, right);
    let add = |polynomial: &mut BTreeMap<CostMonomial, Qsqrt2>,
               key: CostMonomial,
               coefficient: Qsqrt2| {
        let value = polynomial.get(&key).copied().unwrap_or(Qsqrt2::ZERO) + coefficient;
        if value == Qsqrt2::ZERO {
            polynomial.remove(&key);
        } else {
            polynomial.insert(key, value);
        }
    };
    add(
        &mut polynomial,
        entry.clone(),
        Qsqrt2::new(-(lower * upper), Rational::ZERO),
    );
    let cost = if variables == BULK_VARIABLES {
        running_cost().to_vec()
    } else {
        [(1, Rational::new(1, 2)), (3, Rational::new(1, 4))]
            .map(|(variable, coefficient)| {
                let exponent = exponent_with(STATE_VARIABLES, variable);
                (
                    CostMonomial {
                        cost_power: 0,
                        anti: exponent.clone(),
                        holo: exponent,
                    },
                    Qsqrt2::new(coefficient, Rational::ZERO),
                )
            })
            .to_vec()
    };
    for (cost_key, coefficient) in &cost {
        add(
            &mut polynomial,
            shift(&entry, cost_key),
            Qsqrt2::new(lower + upper, Rational::ZERO) * *coefficient,
        );
        for (second_key, second_coefficient) in &cost {
            add(
                &mut polynomial,
                shift(&shift(&entry, cost_key), second_key),
                -(*coefficient * *second_coefficient),
            );
        }
    }

    let phase = reflection_phase(left, variables).conjugate() * reflection_phase(right, variables);
    let mut result = Vec::new();
    for (key, coefficient) in polynomial {
        for (normal, integer) in normal_form(&key, variables) {
            let coefficient = coefficient * Qsqrt2::from(integer) * normalization;
            if variables == BULK_VARIABLES {
                let (position, value) =
                    moments.coefficient(&normal, phase * ComplexExact::real(coefficient));
                result.push((position, value));
            } else {
                result.push((moments.position(&normal), coefficient));
            }
        }
    }
    result
}

#[derive(Clone, Debug)]
pub(crate) struct RateInterfaceMomentSpace {
    pub(crate) keys: Vec<CostMonomial>,
    index: BTreeMap<CostMonomial, usize>,
    rate: Rational,
}

impl RateInterfaceMomentSpace {
    pub(crate) fn create(order: u8, rate: Rational) -> Self {
        let keys =
            MomentSpace::create_for(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
                .keys
                .into_iter()
                .filter(|key| key.anti.0[3] == 0 || key.holo.0[3] == 0)
                .collect::<Vec<_>>();
        let index = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(position, key)| (key, position))
            .collect();
        Self { keys, index, rate }
    }

    pub(crate) fn coefficients(&self, key: &CostMonomial) -> Vec<(usize, Qsqrt2)> {
        let mut result = BTreeMap::<usize, Qsqrt2>::new();
        for (normal, coefficient) in rate_interface_normal_form(key, self.rate) {
            let canonical = normal.clone().min(normal.conjugate());
            let position = self.index[&canonical];
            let value = result.get(&position).copied().unwrap_or(Qsqrt2::ZERO) + coefficient;
            if value == Qsqrt2::ZERO {
                result.remove(&position);
            } else {
                result.insert(position, value);
            }
        }
        result.into_iter().collect()
    }
}

fn rate_interface_normal_form(
    key: &CostMonomial,
    rate: Rational,
) -> BTreeMap<CostMonomial, Qsqrt2> {
    let mut result = BTreeMap::new();
    for (mut normal, integer) in normal_form(key, STATE_VARIABLES) {
        let paired_r2 = normal.anti.0[3].min(normal.holo.0[3]);
        normal.anti.0[3] -= paired_r2;
        normal.holo.0[3] -= paired_r2;
        let mut expansion = BTreeMap::from([(normal, Qsqrt2::from(integer))]);
        for _ in 0..paired_r2 {
            let mut next = BTreeMap::new();
            for (term, coefficient) in expansion {
                let constant =
                    coefficient * Qsqrt2::new(Rational::new(4, 1) * rate, Rational::ZERO);
                *next.entry(term.clone()).or_insert(Qsqrt2::ZERO) += constant;
                let mut r1_term = term;
                r1_term.anti.0[1] += 1;
                r1_term.holo.0[1] += 1;
                *next.entry(r1_term).or_insert(Qsqrt2::ZERO) += coefficient * Qsqrt2::from(-2);
            }
            expansion = next;
        }
        for (term, coefficient) in expansion {
            *result.entry(term).or_insert(Qsqrt2::ZERO) += coefficient;
        }
    }
    result.retain(|_, coefficient| *coefficient != Qsqrt2::ZERO);
    result
}

pub(crate) fn boundary_moment_position(moments: &MomentSpace, test: &CostMonomial) -> usize {
    let mut state = test.clone();
    state.cost_power = 0;
    moments.position(&state)
}

pub(crate) fn reflection_phase_is_i(key: &CostMonomial, variables: usize) -> bool {
    reflection_phase(key, variables) == ComplexExact::I
}

pub(crate) fn exact_certificate_model(order: u8) -> Result<ExactCertificateModel, String> {
    certificate_model(order, None)
}

pub(crate) fn active_time_capped_certificate_model(
    order: u8,
) -> Result<ExactCertificateModel, String> {
    if order < 2 {
        return Err("stationary-torus Hausdorff-lift order must be at least two".into());
    }
    let (blocks, _) = active_time_capped_occupation_blocks(order);
    certificate_model_from_blocks(order, blocks, false)
}

pub(crate) fn enriched_certificate_model(
    order: u8,
    enrichment: &ChargeEnrichment,
) -> Result<ExactCertificateModel, String> {
    certificate_model(order, Some(enrichment))
}

pub(crate) fn control_enriched_certificate_model(
    order: u8,
    control_degree: u8,
) -> Result<ExactCertificateModel, String> {
    if order < 2 {
        return Err("stationary-torus Hausdorff-lift order must be at least two".into());
    }
    let (blocks, _) = control_anisotropic_occupation_blocks(order, control_degree)?;
    certificate_model_from_occupation_blocks(order, blocks)
}

pub(crate) fn rydberg_localized_certificate_model(
    order: u8,
    charges: &[Charge],
) -> Result<ExactCertificateModel, String> {
    if order < 2 {
        return Err("stationary-torus Hausdorff-lift order must be at least two".into());
    }
    if charges.is_empty() {
        return Err("Rydberg product localizers require at least one charge sector".into());
    }
    let (mut blocks, _) = occupation_blocks(order);
    append_rydberg_localizer_blocks(order, charges, &mut blocks)?;
    certificate_model_from_occupation_blocks(order, blocks)
}

fn certificate_model(
    order: u8,
    enrichment: Option<&ChargeEnrichment>,
) -> Result<ExactCertificateModel, String> {
    if order < 2 {
        return Err("stationary-torus Hausdorff-lift order must be at least two".into());
    }
    let (blocks, _) = match enrichment {
        Some(enrichment) => enriched_occupation_blocks(order, enrichment)?,
        None => occupation_blocks(order),
    };
    certificate_model_from_blocks(order, blocks, enrichment.is_some())
}

fn certificate_model_from_occupation_blocks(
    order: u8,
    blocks: Vec<ExactGramBlock>,
) -> Result<ExactCertificateModel, String> {
    certificate_model_from_blocks(order, blocks, true)
}

fn certificate_model_from_blocks(
    order: u8,
    mut blocks: Vec<ExactGramBlock>,
    extend_moment_space: bool,
) -> Result<ExactCertificateModel, String> {
    let moments = if extend_moment_space {
        moment_space_for_blocks(order, &blocks)
    } else {
        MomentSpace::create(2 * u16::from(order))
    };
    let tests =
        cost_normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
            .collect::<Vec<_>>();
    let terminal_offset = moments.keys.len();
    let cost = running_cost()
        .into_iter()
        .map(|(key, coefficient)| (moments.index[&key], coefficient))
        .collect();
    let equalities = tests
        .iter()
        .map(|test| {
            let mut coefficients = cost_liouville_derivative(test)
                .into_iter()
                .map(|(key, coefficient)| moments.coefficient(&key, coefficient))
                .collect::<Vec<_>>();
            let target = target_value(test);
            if target != 0 {
                coefficients.push((
                    terminal_offset + usize::from(test.cost_power),
                    Qsqrt2::from(-target),
                ));
            }
            ExactLiouvilleRow {
                initial: initial_value(test),
                coefficients,
            }
        })
        .collect();
    blocks.push(ExactGramBlock {
        family: BlockFamily::TerminalMoment,
        kind: None,
        charge: (0, 0),
        basis: Vec::new(),
        face: Vec::new(),
        support: Vec::new(),
        terminal_side: usize::from(order) + 1,
    });
    blocks.push(ExactGramBlock {
        family: BlockFamily::TerminalInterval,
        kind: None,
        charge: (0, 0),
        basis: Vec::new(),
        face: Vec::new(),
        support: Vec::new(),
        terminal_side: usize::from(order),
    });
    Ok(ExactCertificateModel {
        coefficient_count: terminal_offset + 2 * usize::from(order) + 1,
        normalization_position: terminal_offset,
        moments,
        cost,
        equalities,
        blocks,
    })
}

pub fn structure(order: u8) -> Result<StationaryHausdorffStructure, String> {
    let model = exact_certificate_model(order)?;
    let tests =
        cost_normal_invariant_monomials(STATE_VARIABLES, 2 * u16::from(order) - 1, &STATE_CHARGES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
            .collect::<Vec<_>>();
    let (occupation, counts) = occupation_blocks(order);
    let terminal_block_sides = [usize::from(order) + 1, usize::from(order)];
    let mut psd_block_sides = occupation
        .iter()
        .map(|block| block.face.len())
        .collect::<Vec<_>>();
    psd_block_sides.extend(terminal_block_sides);
    let terminal_keys = (0..=2 * order).collect::<Vec<_>>();
    let occupation_basis_hash = hash_json(&model.moments.keys);
    let terminal_basis_hash = hash_json(&terminal_keys);
    let liouville_basis_hash = hash_json(&tests);
    let formulation_hash = hash_json(&serde_json::json!({
        "schema": "minexposure/stationary-torus-hausdorff-lift-v1",
        "order": order,
        "occupation_basis_hash": &occupation_basis_hash,
        "terminal_basis_hash": &terminal_basis_hash,
        "liouville_basis_hash": &liouville_basis_hash,
        "psd_block_sides": &psd_block_sides,
        "exposure_upper": EXPOSURE_UPPER,
        "field": "Q(sqrt(2))",
        "support": "x(1-x)>=0",
        "source_thread": "T-01a05237-5227-7349-a984-0ef443933c9c"
    }));
    Ok(StationaryHausdorffStructure {
        order,
        maximum_moment_degree: 2 * order,
        occupation_moment_count: model.moments.keys.len(),
        terminal_moment_count: 2 * usize::from(order) + 1,
        liouville_equality_count: tests.len(),
        occupation_moment_block_count: counts[0],
        occupation_interval_block_count: counts[1],
        occupation_interval_diagonal_count: counts[2],
        terminal_block_sides,
        largest_psd_side: psd_block_sides.iter().copied().max().unwrap_or(0),
        sum_psd_squares: psd_block_sides.iter().map(|side| side * side).sum(),
        sum_psd_cubes: psd_block_sides.iter().map(|side| side * side * side).sum(),
        psd_block_sides,
        occupation_basis_hash,
        terminal_basis_hash,
        liouville_basis_hash,
        formulation_hash,
        exposure_upper: EXPOSURE_UPPER,
        source_thread: "T-01a05237-5227-7349-a984-0ef443933c9c",
        source_path: "verification/jan22_cz_exposure_cost_lifted_sdp.py",
    })
}

fn hash_json(value: &impl Serialize) -> String {
    format!(
        "sha256:{:x}",
        Sha256::digest(serde_json::to_vec(value).expect("hash input serializes"))
    )
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

pub fn assemble(order: u8) -> Result<StationaryHausdorffProblem, String> {
    let structure = structure(order)?;
    let model = exact_certificate_model(order)?;
    let mut q = vec![0.0; model.coefficient_count()];
    for &(position, coefficient) in &model.cost {
        q[position] = coefficient.to_f64();
    }
    let mut sparse = SparseBuilder::default();
    let mut b = Vec::new();
    for (row_index, equality) in model.equalities.iter().enumerate() {
        for &(column, coefficient) in &equality.coefficients {
            sparse.add(row_index, column, coefficient);
        }
        b.push(-(equality.initial as f64));
    }
    let normalization_row = b.len();
    sparse.add(
        normalization_row,
        model.normalization_position,
        Qsqrt2::from(1),
    );
    b.push(1.0);
    let mut cones = vec![Cone::Zero(b.len())];
    let mut next_row = b.len();
    for (block_index, &side) in model.gram_dimensions().iter().enumerate() {
        for column in 0..side {
            for row in 0..=column {
                let svec_scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                model.for_each_gram_entry_coefficient(
                    block_index,
                    row,
                    column,
                    |position, coefficient| {
                        sparse.add(next_row, position, -(coefficient * svec_scale));
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
    Ok(StationaryHausdorffProblem { structure, conic })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rate_interface_quotient_eliminates_the_exact_cost_ideal() {
        let moments = RateInterfaceMomentSpace::create(3, Rational::new(1, 8));
        let constant = zero_key(STATE_VARIABLES);
        let mut r1_population = constant.clone();
        r1_population.anti.0[1] = 1;
        r1_population.holo.0[1] = 1;
        let mut r2_population = constant.clone();
        r2_population.anti.0[3] = 1;
        r2_population.holo.0[3] = 1;

        assert_eq!(
            moments.coefficients(&r2_population),
            vec![
                (
                    moments.index[&constant],
                    Qsqrt2::new(Rational::new(1, 2), Rational::ZERO)
                ),
                (moments.index[&r1_population], Qsqrt2::from(-2)),
            ]
        );
        assert!(
            moments
                .keys
                .iter()
                .all(|key| key.anti.0[3] == 0 || key.holo.0[3] == 0)
        );
    }

    #[test]
    fn charge_enrichment_parses_canonical_sectors_and_validates_degree() {
        let enrichment = ChargeEnrichment::parse("0:2, -1:1, 0:-2", 1).unwrap();
        assert_eq!(enrichment.charges, vec![(-1, 1), (0, -2)]);
        assert!(ChargeEnrichment::parse("0,-2", 1).is_err());
        assert!(ChargeEnrichment::parse("0:-2", 0).is_err());
        assert!(ChargeEnrichment::parse("0:-2", 3).is_err());
    }

    #[test]
    fn enriched_model_only_expands_selected_occupation_blocks() {
        let enrichment = ChargeEnrichment::new(vec![(0, -1), (0, 0)], 1).unwrap();
        let baseline = exact_certificate_model(3).unwrap();
        let enriched = enriched_certificate_model(3, &enrichment).unwrap();
        assert_eq!(baseline.equalities.len(), enriched.equalities.len());
        assert!(enriched.moments.keys.len() > baseline.moments.keys.len());
        assert!(
            baseline
                .moments
                .keys
                .iter()
                .all(|key| enriched.moments.index.contains_key(key))
        );
        assert_eq!(
            enriched.occupation_blocks().len(),
            baseline.occupation_blocks().len() + 2 * enrichment.charges.len()
        );
        for (baseline, retained) in baseline
            .occupation_blocks()
            .iter()
            .zip(enriched.occupation_blocks())
        {
            assert_eq!(retained.face.len(), baseline.face.len());
            assert_eq!(retained.basis, baseline.basis);
            assert_eq!(retained.kind, baseline.kind);
            assert_eq!(retained.charge, baseline.charge);
        }
        let extensions = &enriched.occupation_blocks()[baseline.occupation_blocks().len()..];
        for (index, &charge) in enrichment.charges.iter().enumerate() {
            let pair = &extensions[2 * index..2 * index + 2];
            assert_eq!(pair[0].charge, charge);
            assert_eq!(pair[0].kind, Some(OccupationBlockKind::Moment));
            assert_eq!(pair[1].charge, charge);
            assert_eq!(pair[1].kind, Some(OccupationBlockKind::Interval));
        }
    }

    #[test]
    fn anisotropic_enrichment_merges_an_exact_union_of_gram_directions() {
        let enrichment = ChargeEnrichment::new(vec![(0, -2), (0, -1), (0, 0)], 1).unwrap();
        for xi_degree in [12, 16] {
            let baseline =
                AnisotropicOccupationModel::create_with_enrichment(6, xi_degree, None).unwrap();
            let enriched =
                AnisotropicOccupationModel::create_with_enrichment(6, xi_degree, Some(&enrichment))
                    .unwrap();
            assert!(
                baseline
                    .moments
                    .keys
                    .iter()
                    .all(|key| enriched.moments.index.contains_key(key))
            );
            assert_eq!(enriched.blocks.len(), baseline.blocks.len());
            for (base, merged) in baseline.blocks.iter().zip(&enriched.blocks) {
                assert_eq!(merged.family, base.family);
                assert_eq!(merged.kind, base.kind);
                assert_eq!(merged.charge, base.charge);
                assert!(merged.basis.starts_with(&base.basis));
                assert!(merged.face.starts_with(&base.face));
                assert_eq!(merged.support, base.support);
            }

            let mut candidates = baseline.blocks.clone();
            let original_len = candidates.len();
            let mut ignored_counts = [0; 3];
            append_charge_enrichment(6, &enrichment, &mut candidates, &mut ignored_counts).unwrap();
            for candidate in &candidates[original_len..] {
                let merged = enriched
                    .blocks
                    .iter()
                    .find(|block| block.kind == candidate.kind && block.charge == candidate.charge)
                    .unwrap();
                let merged_positions = merged
                    .basis
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(index, key)| (key, index))
                    .collect::<BTreeMap<_, _>>();
                let mut span = ExactColumnSpan::default();
                for column in &merged.face {
                    assert!(span.insert(column));
                }
                for column in &candidate.face {
                    let remapped = column
                        .iter()
                        .map(|&(position, coefficient)| {
                            (merged_positions[&candidate.basis[position]], coefficient)
                        })
                        .collect::<Vec<_>>();
                    assert!(!span.insert(&remapped));
                }
            }
        }
    }

    #[test]
    fn matches_source_structure_counts() {
        let expected = [
            (2, 26, 10, 5, [13, 6, 6], 27, 72, 154),
            (3, 95, 33, 7, [29, 17, 21], 69, 955, 6_573),
            (4, 286, 88, 9, [51, 34, 56], 143, 9_590, 183_418),
            (5, 741, 202, 11, [79, 57, 126], 264, 69_229, 3_078_301),
            (6, 1_695, 413, 13, [113, 86, 252], 453, 388_275, 35_687_087),
        ];
        for (order, occupation, equalities, terminal, counts, blocks, squares, cubes) in expected {
            let structure = structure(order).unwrap();
            assert_eq!(
                structure.occupation_moment_count, occupation,
                "order {order}"
            );
            assert_eq!(
                structure.liouville_equality_count, equalities,
                "order {order}"
            );
            assert_eq!(structure.terminal_moment_count, terminal, "order {order}");
            assert_eq!(
                [
                    structure.occupation_moment_block_count,
                    structure.occupation_interval_block_count,
                    structure.occupation_interval_diagonal_count,
                ],
                counts,
                "order {order}"
            );
            assert_eq!(structure.psd_block_sides.len(), blocks, "order {order}");
            assert_eq!(structure.sum_psd_squares, squares, "order {order}");
            assert_eq!(structure.sum_psd_cubes, cubes, "order {order}");
        }
    }

    #[test]
    fn order_five_certificate_layout_matches_source() {
        let model = exact_certificate_model(5).unwrap();
        assert_eq!(model.coefficient_count(), 752);
        assert_eq!(model.equalities.len(), 202);
        assert_eq!(model.occupation_gram_count(), 262);
        assert_eq!(
            &model.gram_dimensions()[..8],
            &[68, 62, 64, 42, 43, 47, 53, 49]
        );
        assert_eq!(&model.gram_dimensions()[262..], &[6, 5]);
    }

    #[test]
    fn golden_endpoints_match_native_structure() {
        for (order, text) in [
            (
                2,
                include_str!("../../../golden/stationary-torus-hausdorff-lift-order-2.json"),
            ),
            (
                6,
                include_str!("../../../golden/stationary-torus-hausdorff-lift-order-6.json"),
            ),
        ] {
            let golden: serde_json::Value = serde_json::from_str(text).unwrap();
            let structure = structure(order).unwrap();
            assert_eq!(
                structure.occupation_moment_count as u64,
                golden["occupation_moments"].as_u64().unwrap()
            );
            assert_eq!(
                structure.liouville_equality_count as u64,
                golden["liouville_equalities"].as_u64().unwrap()
            );
            assert_eq!(
                structure.psd_block_sides.len() as u64,
                golden["psd_block_count"].as_u64().unwrap()
            );
            assert_eq!(
                hash_json(&structure.psd_block_sides),
                format!(
                    "sha256:{}",
                    golden["psd_block_sides_canonical_json_sha256"]
                        .as_str()
                        .unwrap()
                )
            );
            assert_eq!(
                structure.occupation_basis_hash,
                golden["occupation_basis_hash"].as_str().unwrap()
            );
            assert_eq!(
                structure.terminal_basis_hash,
                golden["terminal_basis_hash"].as_str().unwrap()
            );
            assert_eq!(
                structure.liouville_basis_hash,
                golden["liouville_basis_hash"].as_str().unwrap()
            );
        }
    }

    #[test]
    fn assembles_order_two_problem() {
        let problem = assemble(2).unwrap();
        assert_eq!(problem.conic.q.len(), 31);
        assert_eq!(problem.conic.cones.len(), 28);
        assert_eq!(problem.conic.cones[0], Cone::Zero(11));
        assert!(problem.conic.a.entries.len() > 100);
    }
}
