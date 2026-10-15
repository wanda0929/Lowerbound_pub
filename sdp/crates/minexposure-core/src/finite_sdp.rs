//! Native fixed-horizon occupation-moment SDP for finite-blockade CZ.
//!
//! This is a direct Rust assembly of `cz_finite_b_model.py` and
//! `cz_blockade_moment_sdp.py` from time_bound commit
//! `d349e42b3e6a5c7ebbbc00fc42d8fb152bf9362f`.

use crate::algebra::{Qsqrt2, Rational};
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::monomial::{Exponent, basis_hash, monomials};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};

const OCCUPATION_VARIABLES: usize = 12;
const STATE_VARIABLES: usize = 10;
const G1_RE: usize = 0;
const G1_IM: usize = 1;
const R1_RE: usize = 2;
const R1_IM: usize = 3;
const G2_RE: usize = 4;
const G2_IM: usize = 5;
const W_RE: usize = 6;
const W_IM: usize = 7;
const RR_RE: usize = 8;
const RR_IM: usize = 9;
const U_RE: usize = 10;
const U_IM: usize = 11;

type Polynomial = Vec<(Qsqrt2, Exponent)>;

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct FiniteSdpStructure {
    pub order: u8,
    pub kappa: Rational,
    pub horizon: Rational,
    pub occupation_moments: usize,
    pub terminal_moments: usize,
    pub equality_count: usize,
    pub psd_block_sides: Vec<usize>,
    pub affine_nnz: usize,
    pub occupation_basis_hash: String,
    pub terminal_basis_hash: String,
    pub formulation_hash: String,
    pub source_repository: &'static str,
    pub source_commit: &'static str,
    pub source_paths: [&'static str; 2],
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct FiniteSdpProblem {
    pub structure: FiniteSdpStructure,
    pub conic: ConicProblem,
}

#[derive(Default)]
struct SparseBuilder(BTreeMap<(usize, usize), f64>);

impl SparseBuilder {
    fn add(&mut self, row: usize, column: usize, value: f64) {
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

fn q(numerator: i128, denominator: i128) -> Qsqrt2 {
    Qsqrt2::new(Rational::new(numerator, denominator), Rational::ZERO)
}

fn qs(numerator: i128, denominator: i128) -> Qsqrt2 {
    Qsqrt2::new(Rational::ZERO, Rational::new(numerator, denominator))
}

fn exponent(variables: usize, powers: &[(usize, u16)]) -> Exponent {
    let mut value = vec![0; variables];
    for &(index, power) in powers {
        value[index] = power;
    }
    Exponent(value)
}

fn add(left: &Exponent, right: &Exponent) -> Exponent {
    Exponent(left.0.iter().zip(&right.0).map(|(a, b)| a + b).collect())
}

fn dynamics(kappa: Rational) -> Vec<Polynomial> {
    let t = |coefficient, powers| (coefficient, exponent(OCCUPATION_VARIABLES, powers));
    vec![
        vec![
            t(q(1, 2), &[(U_RE, 1), (R1_IM, 1)]),
            t(q(1, 2), &[(U_IM, 1), (R1_RE, 1)]),
        ],
        vec![
            t(q(1, 2), &[(U_IM, 1), (R1_IM, 1)]),
            t(q(-1, 2), &[(U_RE, 1), (R1_RE, 1)]),
        ],
        vec![
            t(q(1, 2), &[(U_RE, 1), (G1_IM, 1)]),
            t(q(-1, 2), &[(U_IM, 1), (G1_RE, 1)]),
        ],
        vec![
            t(q(-1, 2), &[(U_RE, 1), (G1_RE, 1)]),
            t(q(-1, 2), &[(U_IM, 1), (G1_IM, 1)]),
        ],
        vec![
            t(qs(1, 2), &[(U_RE, 1), (W_IM, 1)]),
            t(qs(1, 2), &[(U_IM, 1), (W_RE, 1)]),
        ],
        vec![
            t(qs(1, 2), &[(U_IM, 1), (W_IM, 1)]),
            t(qs(-1, 2), &[(U_RE, 1), (W_RE, 1)]),
        ],
        vec![
            t(qs(1, 2), &[(U_RE, 1), (G2_IM, 1)]),
            t(qs(-1, 2), &[(U_IM, 1), (G2_RE, 1)]),
            t(qs(1, 2), &[(U_RE, 1), (RR_IM, 1)]),
            t(qs(1, 2), &[(U_IM, 1), (RR_RE, 1)]),
        ],
        vec![
            t(qs(-1, 2), &[(U_RE, 1), (G2_RE, 1)]),
            t(qs(-1, 2), &[(U_IM, 1), (G2_IM, 1)]),
            t(qs(1, 2), &[(U_IM, 1), (RR_IM, 1)]),
            t(qs(-1, 2), &[(U_RE, 1), (RR_RE, 1)]),
        ],
        vec![
            t(qs(1, 2), &[(U_RE, 1), (W_IM, 1)]),
            t(qs(-1, 2), &[(U_IM, 1), (W_RE, 1)]),
            t(Qsqrt2::new(kappa, Rational::ZERO), &[(RR_IM, 1)]),
        ],
        vec![
            t(qs(-1, 2), &[(U_RE, 1), (W_RE, 1)]),
            t(qs(-1, 2), &[(U_IM, 1), (W_IM, 1)]),
            t(Qsqrt2::new(-kappa, Rational::ZERO), &[(RR_RE, 1)]),
        ],
    ]
}

fn norm_polynomials(variables: usize) -> Vec<Polynomial> {
    vec![
        [G1_RE, G1_IM, R1_RE, R1_IM]
            .into_iter()
            .map(|index| (q(1, 1), exponent(variables, &[(index, 2)])))
            .chain([(q(-1, 1), exponent(variables, &[]))])
            .collect(),
        [G2_RE, G2_IM, W_RE, W_IM, RR_RE, RR_IM]
            .into_iter()
            .map(|index| (q(1, 1), exponent(variables, &[(index, 2)])))
            .chain([(q(-1, 1), exponent(variables, &[]))])
            .collect(),
    ]
}

fn terminal_polynomials() -> Vec<Polynomial> {
    let mut result = norm_polynomials(STATE_VARIABLES);
    for index in [R1_RE, R1_IM, W_RE, W_IM, RR_RE, RR_IM] {
        result.push(vec![(q(1, 1), exponent(STATE_VARIABLES, &[(index, 1)]))]);
    }
    result.push(vec![
        (q(1, 1), exponent(STATE_VARIABLES, &[(G2_RE, 1)])),
        (q(1, 1), exponent(STATE_VARIABLES, &[(G1_RE, 2)])),
        (q(-1, 1), exponent(STATE_VARIABLES, &[(G1_IM, 2)])),
    ]);
    result.push(vec![
        (q(1, 1), exponent(STATE_VARIABLES, &[(G2_IM, 1)])),
        (
            q(2, 1),
            exponent(STATE_VARIABLES, &[(G1_RE, 1), (G1_IM, 1)]),
        ),
    ]);
    result
}

fn add_polynomial_row(
    sparse: &mut SparseBuilder,
    row: usize,
    offset: usize,
    index: &HashMap<Exponent, usize>,
    multiplier: &Exponent,
    polynomial: &Polynomial,
) {
    for &(coefficient, ref power) in polynomial {
        sparse.add(
            row,
            offset + index[&add(multiplier, power)],
            coefficient.to_f64(),
        );
    }
}

fn add_moment_psd(
    sparse: &mut SparseBuilder,
    next_row: &mut usize,
    offset: usize,
    index: &HashMap<Exponent, usize>,
    basis: &[Exponent],
    localizer: &Polynomial,
) {
    for column in 0..basis.len() {
        for row in 0..=column {
            let scale = if row == column { 1.0 } else { 2.0_f64.sqrt() };
            let product = add(&basis[row], &basis[column]);
            for &(coefficient, ref power) in localizer {
                sparse.add(
                    *next_row,
                    offset + index[&add(&product, power)],
                    -scale * coefficient.to_f64(),
                );
            }
            *next_row += 1;
        }
    }
}

pub fn assemble(order: u8, kappa: Rational, horizon: Rational) -> Result<FiniteSdpProblem, String> {
    if order < 2 {
        return Err("finite fixed-kappa relaxation order must be at least 2".into());
    }
    if kappa.denominator == 0 || horizon.denominator == 0 || horizon.numerator <= 0 {
        return Err("kappa must be rational and horizon must be positive".into());
    }
    let degree = 2 * u16::from(order);
    let occupation = monomials(OCCUPATION_VARIABLES, degree);
    let terminal = monomials(STATE_VARIABLES, degree);
    let occupation_index = occupation
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, exponent)| (exponent, index))
        .collect::<HashMap<_, _>>();
    let terminal_index = terminal
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, exponent)| (exponent, index))
        .collect::<HashMap<_, _>>();
    let terminal_offset = occupation.len();
    let mut q_vector = vec![0.0; occupation.len() + terminal.len()];
    for (coefficient, power) in [
        (q(1, 2), exponent(OCCUPATION_VARIABLES, &[(R1_RE, 2)])),
        (q(1, 2), exponent(OCCUPATION_VARIABLES, &[(R1_IM, 2)])),
        (q(1, 4), exponent(OCCUPATION_VARIABLES, &[(W_RE, 2)])),
        (q(1, 4), exponent(OCCUPATION_VARIABLES, &[(W_IM, 2)])),
        (q(1, 2), exponent(OCCUPATION_VARIABLES, &[(RR_RE, 2)])),
        (q(1, 2), exponent(OCCUPATION_VARIABLES, &[(RR_IM, 2)])),
    ] {
        q_vector[occupation_index[&power]] = coefficient.to_f64();
    }

    let mut sparse = SparseBuilder::default();
    let mut b = Vec::new();
    let zero_occ = exponent(OCCUPATION_VARIABLES, &[]);
    let zero_terminal = exponent(STATE_VARIABLES, &[]);
    for polynomial in norm_polynomials(OCCUPATION_VARIABLES) {
        for multiplier in monomials(OCCUPATION_VARIABLES, degree - 2) {
            let row = b.len();
            add_polynomial_row(
                &mut sparse,
                row,
                0,
                &occupation_index,
                &multiplier,
                &polynomial,
            );
            b.push(0.0);
        }
    }
    sparse.add(b.len(), occupation_index[&zero_occ], 1.0);
    b.push(horizon.numerator as f64 / horizon.denominator as f64);
    sparse.add(
        b.len(),
        terminal_offset + terminal_index[&zero_terminal],
        1.0,
    );
    b.push(1.0);
    for polynomial in terminal_polynomials() {
        let polynomial_degree = polynomial
            .iter()
            .map(|(_, power)| power.degree())
            .max()
            .unwrap();
        for multiplier in monomials(STATE_VARIABLES, degree - polynomial_degree) {
            let row = b.len();
            add_polynomial_row(
                &mut sparse,
                row,
                terminal_offset,
                &terminal_index,
                &multiplier,
                &polynomial,
            );
            b.push(0.0);
        }
    }
    let dynamics = dynamics(kappa);
    for test in monomials(STATE_VARIABLES, degree - 1).into_iter().skip(1) {
        let row = b.len();
        for (state, &multiplicity) in test.0.iter().enumerate() {
            if multiplicity == 0 {
                continue;
            }
            let mut base = test.0.clone();
            base[state] -= 1;
            base.extend([0, 0]);
            let base = Exponent(base);
            for &(coefficient, ref power) in &dynamics[state] {
                sparse.add(
                    row,
                    occupation_index[&add(&base, power)],
                    f64::from(multiplicity) * coefficient.to_f64(),
                );
            }
        }
        sparse.add(row, terminal_offset + terminal_index[&test], -1.0);
        let initial_value = test
            .0
            .iter()
            .enumerate()
            .all(|(index, &power)| power == 0 || matches!(index, G1_RE | G2_RE));
        b.push(if initial_value { -1.0 } else { 0.0 });
    }
    let equality_count = b.len();
    let occupation_gram = monomials(OCCUPATION_VARIABLES, order.into());
    let terminal_gram = monomials(STATE_VARIABLES, order.into());
    let disk_gram = monomials(OCCUPATION_VARIABLES, u16::from(order) - 1);
    let mut next_row = equality_count;
    add_moment_psd(
        &mut sparse,
        &mut next_row,
        0,
        &occupation_index,
        &occupation_gram,
        &vec![(q(1, 1), zero_occ.clone())],
    );
    add_moment_psd(
        &mut sparse,
        &mut next_row,
        terminal_offset,
        &terminal_index,
        &terminal_gram,
        &vec![(q(1, 1), zero_terminal)],
    );
    add_moment_psd(
        &mut sparse,
        &mut next_row,
        0,
        &occupation_index,
        &disk_gram,
        &vec![
            (q(1, 1), zero_occ),
            (q(-1, 1), exponent(OCCUPATION_VARIABLES, &[(U_RE, 2)])),
            (q(-1, 1), exponent(OCCUPATION_VARIABLES, &[(U_IM, 2)])),
        ],
    );
    b.resize(next_row, 0.0);
    let psd_block_sides = vec![occupation_gram.len(), terminal_gram.len(), disk_gram.len()];
    let entries = sparse.finish();
    let conic = ConicProblem {
        q: q_vector,
        a: SparseMatrix {
            rows: next_row,
            cols: occupation.len() + terminal.len(),
            entries,
        },
        b,
        cones: vec![
            Cone::Zero(equality_count),
            Cone::PsdTriangle(psd_block_sides[0]),
            Cone::PsdTriangle(psd_block_sides[1]),
            Cone::PsdTriangle(psd_block_sides[2]),
        ],
    };
    conic.validate()?;
    let occupation_basis_hash = basis_hash(&occupation);
    let terminal_basis_hash = basis_hash(&terminal);
    let formulation_hash = format!(
        "sha256:{:x}",
        Sha256::digest(
            serde_json::to_vec(&serde_json::json!({
                "schema": "minexposure/finite-cz-fixed-kappa-v1",
                "order": order,
                "kappa": kappa.to_string(),
                "horizon": horizon.to_string(),
                "occupation_basis_hash": &occupation_basis_hash,
                "terminal_basis_hash": &terminal_basis_hash,
                "source_commit": "d349e42b3e6a5c7ebbbc00fc42d8fb152bf9362f"
            }))
            .expect("finite formulation serializes"),
        )
    );
    Ok(FiniteSdpProblem {
        structure: FiniteSdpStructure {
            order,
            kappa,
            horizon,
            occupation_moments: occupation.len(),
            terminal_moments: terminal.len(),
            equality_count,
            psd_block_sides,
            affine_nnz: conic.a.entries.len(),
            occupation_basis_hash,
            terminal_basis_hash,
            formulation_hash,
            source_repository: "https://ampcode.com/@excalior/time_bound",
            source_commit: "d349e42b3e6a5c7ebbbc00fc42d8fb152bf9362f",
            source_paths: [
                "scripts/cz_finite_b_model.py",
                "scripts/cz_blockade_moment_sdp.py",
            ],
        },
        conic,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order_two_structure_matches_source_formulation() {
        let problem = assemble(
            2,
            Rational::new(10, 1),
            Rational::new(7725371148168462, 10_i128.pow(15)),
        )
        .unwrap();
        assert_eq!(problem.structure.occupation_moments, 1820);
        assert_eq!(problem.structure.terminal_moments, 1001);
        assert_eq!(problem.structure.equality_count, 2449);
        assert_eq!(problem.structure.psd_block_sides, [91, 66, 13]);
        // Independently compiled source CVXPY conic data has shape 8937x2821
        // with 12603 affine nonzeros and the same cone dimensions.
        assert_eq!(problem.conic.a.rows, 8937);
        assert_eq!(problem.conic.a.cols, 2821);
        assert_eq!(problem.structure.affine_nnz, 12603);
        assert_eq!(
            problem
                .conic
                .q
                .iter()
                .filter(|&&value| value != 0.0)
                .count(),
            6
        );
    }

    #[test]
    fn kappa_changes_only_the_scientific_formulation() {
        let horizon = Rational::new(7, 1);
        let ten = assemble(2, Rational::new(10, 1), horizon).unwrap();
        let twenty = assemble(2, Rational::new(20, 1), horizon).unwrap();
        assert_ne!(
            ten.structure.formulation_hash,
            twenty.structure.formulation_hash
        );
        assert_eq!(
            ten.structure.psd_block_sides,
            twenty.structure.psd_block_sides
        );
        assert_ne!(ten.conic.a, twenty.conic.a);
    }
}
