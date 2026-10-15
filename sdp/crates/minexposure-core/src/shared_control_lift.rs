//! Singular-safe projected shared-control occupation relaxation.
//!
//! Every physical stationary-torus trajectory pushes forward through
//! `(x,y,C,J,p,q,m,n)`. The projected functional may nevertheless contain
//! spurious trajectories, so solver values are exploratory until an exact
//! dual audit succeeds.

use crate::algebra::{Qsqrt2, Rational};
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::monomial::{Exponent, monomials};
use crate::stationary_torus::ComplexExact;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

const VARIABLES: usize = 8;
const STATE_VARIABLES: usize = 4;
const X: usize = 0;
const Y: usize = 1;
const C: usize = 2;
const J: usize = 3;
const P: usize = 4;
const Q: usize = 5;
const M: usize = 6;
const N: usize = 7;
const REAL_VARIABLES: [usize; 2] = [X, Y];
const STATE_REAL_VARIABLES: [usize; 2] = [X, Y];
const STATE_TO_BULK: [usize; STATE_VARIABLES] = [X, Y, C, J];

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Key {
    anti: Exponent,
    holo: Exponent,
}

impl Key {
    fn conjugate(&self) -> Self {
        Self {
            anti: self.holo.clone(),
            holo: self.anti.clone(),
        }
    }

    fn degree(&self) -> u16 {
        self.anti.degree() + self.holo.degree()
    }
}

type Polynomial = BTreeMap<Key, ComplexExact>;

fn exact(rational_numerator: i128, rational_denominator: i128) -> Qsqrt2 {
    Qsqrt2::new(
        Rational::new(rational_numerator, rational_denominator),
        Rational::ZERO,
    )
}

fn sqrt2(rational_numerator: i128, rational_denominator: i128) -> Qsqrt2 {
    Qsqrt2::new(
        Rational::ZERO,
        Rational::new(rational_numerator, rational_denominator),
    )
}

fn normalize_real(mut key: Key, real_variables: &[usize]) -> Key {
    for &variable in real_variables {
        key.holo.0[variable] += key.anti.0[variable];
        key.anti.0[variable] = 0;
    }
    key
}

fn add_exponents(left: &Exponent, right: &Exponent) -> Exponent {
    Exponent(left.0.iter().zip(&right.0).map(|(&a, &b)| a + b).collect())
}

fn shift(left: &Key, right: &Key) -> Key {
    Key {
        anti: add_exponents(&left.anti, &right.anti),
        holo: add_exponents(&left.holo, &right.holo),
    }
}

fn add_term(polynomial: &mut Polynomial, key: Key, coefficient: ComplexExact) {
    let value = polynomial.get(&key).copied().unwrap_or(ComplexExact::ZERO) + coefficient;
    if value == ComplexExact::ZERO {
        polynomial.remove(&key);
    } else {
        polynomial.insert(key, value);
    }
}

fn add(left: &Polynomial, right: &Polynomial) -> Polynomial {
    let mut result = left.clone();
    for (key, &coefficient) in right {
        add_term(&mut result, key.clone(), coefficient);
    }
    result
}

fn scale(polynomial: &Polynomial, coefficient: ComplexExact) -> Polynomial {
    polynomial
        .iter()
        .map(|(key, &value)| (key.clone(), value * coefficient))
        .collect()
}

fn multiply(left: &Polynomial, right: &Polynomial) -> Polynomial {
    let mut result = Polynomial::new();
    for (left_key, &left_coefficient) in left {
        for (right_key, &right_coefficient) in right {
            add_term(
                &mut result,
                shift(left_key, right_key),
                left_coefficient * right_coefficient,
            );
        }
    }
    result
}

fn conjugate(polynomial: &Polynomial) -> Polynomial {
    polynomial
        .iter()
        .map(|(key, &coefficient)| (key.conjugate(), coefficient.conjugate()))
        .collect()
}

fn variable(variables: usize, index: usize) -> Polynomial {
    let mut holo = vec![0; variables];
    holo[index] = 1;
    BTreeMap::from([(
        Key {
            anti: Exponent(vec![0; variables]),
            holo: Exponent(holo),
        },
        ComplexExact::ONE,
    )])
}

fn anti_variable(variables: usize, index: usize) -> Polynomial {
    conjugate(&variable(variables, index))
}

fn constant(variables: usize, value: ComplexExact) -> Polynomial {
    BTreeMap::from([(
        Key {
            anti: Exponent(vec![0; variables]),
            holo: Exponent(vec![0; variables]),
        },
        value,
    )])
}

fn one_minus(index: usize) -> Polynomial {
    add(
        &constant(VARIABLES, ComplexExact::ONE),
        &scale(&variable(VARIABLES, index), -ComplexExact::ONE),
    )
}

fn population_product(index: usize) -> Polynomial {
    multiply(&variable(VARIABLES, index), &one_minus(index))
}

fn modulus(index: usize) -> Polynomial {
    multiply(
        &anti_variable(VARIABLES, index),
        &variable(VARIABLES, index),
    )
}

fn support_equalities() -> Vec<(&'static str, Polynomial)> {
    let x = variable(VARIABLES, X);
    let y = variable(VARIABLES, Y);
    let c = variable(VARIABLES, C);
    let j = variable(VARIABLES, J);
    let p = variable(VARIABLES, P);
    let q = variable(VARIABLES, Q);
    let m = variable(VARIABLES, M);
    let n = variable(VARIABLES, N);
    let p_bar = anti_variable(VARIABLES, P);
    let q_bar = anti_variable(VARIABLES, Q);
    let m_bar = anti_variable(VARIABLES, M);
    let dx = population_product(X);
    let dy = population_product(Y);
    let ox = one_minus(X);
    let oy = one_minus(Y);
    vec![
        (
            "C_modulus",
            add(
                &modulus(C),
                &scale(&multiply(&oy, &multiply(&ox, &ox)), -ComplexExact::ONE),
            ),
        ),
        (
            "J_modulus",
            add(&modulus(J), &scale(&multiply(&dx, &dy), -ComplexExact::ONE)),
        ),
        (
            "p_modulus",
            add(&modulus(P), &scale(&dx, -ComplexExact::ONE)),
        ),
        (
            "q_modulus",
            add(&modulus(Q), &scale(&dy, -ComplexExact::ONE)),
        ),
        (
            "m_modulus",
            add(
                &modulus(M),
                &scale(&multiply(&y, &multiply(&ox, &ox)), -ComplexExact::ONE),
            ),
        ),
        (
            "n_modulus",
            add(&modulus(N), &scale(&multiply(&oy, &dx), -ComplexExact::ONE)),
        ),
        (
            "J_from_pq",
            add(&j, &scale(&multiply(&p_bar, &q), -ComplexExact::ONE)),
        ),
        (
            "m_regular_chart",
            add(
                &multiply(&oy, &m),
                &scale(&multiply(&c, &q_bar), -ComplexExact::ONE),
            ),
        ),
        (
            "n_regular_chart",
            add(
                &multiply(&ox, &n),
                &scale(&multiply(&c, &p), -ComplexExact::ONE),
            ),
        ),
        (
            "m_q_boundary_closure",
            add(
                &multiply(&m, &q),
                &scale(&multiply(&y, &c), -ComplexExact::ONE),
            ),
        ),
        (
            "n_p_boundary_closure",
            add(
                &multiply(&n, &p_bar),
                &scale(&multiply(&x, &c), -ComplexExact::ONE),
            ),
        ),
        (
            "mn_phase_closure",
            add(
                &multiply(&m_bar, &n),
                &scale(&multiply(&ox, &multiply(&p, &q)), -ComplexExact::ONE),
            ),
        ),
        (
            "singular_safe_shared_control",
            add(
                &multiply(&p, &j),
                &scale(&multiply(&dx, &q), -ComplexExact::ONE),
            ),
        ),
    ]
}

fn normalized_monomials(
    variables: usize,
    maximum_degree: u16,
    real_variables: &[usize],
) -> Vec<Key> {
    let through = monomials(variables, maximum_degree);
    let mut result = BTreeSet::new();
    for anti in &through {
        for holo in monomials(variables, maximum_degree - anti.degree()) {
            result.insert(normalize_real(
                Key {
                    anti: anti.clone(),
                    holo,
                },
                real_variables,
            ));
        }
    }
    result.into_iter().collect()
}

fn odd_parity(key: &Key) -> bool {
    ![P, Q, M, N]
        .iter()
        .map(|&index| key.anti.0[index] + key.holo.0[index])
        .sum::<u16>()
        .is_multiple_of(2)
}

fn reflection_phase(key: &Key) -> ComplexExact {
    if odd_parity(key) {
        ComplexExact::I
    } else {
        ComplexExact::ONE
    }
}

#[derive(Clone, Debug)]
struct MomentSpace {
    keys: Vec<Key>,
    index: BTreeMap<Key, usize>,
}

impl MomentSpace {
    fn create(maximum_degree: u16) -> Self {
        let canonical = normalized_monomials(VARIABLES, maximum_degree, &REAL_VARIABLES)
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

    fn complex_coefficient(&self, raw: &Key, coefficient: ComplexExact) -> (usize, ComplexExact) {
        let key = normalize_real(raw.clone(), &REAL_VARIABLES);
        let conjugate = key.conjugate();
        let canonical = key.clone().min(conjugate);
        let phase = if key == canonical {
            reflection_phase(&canonical)
        } else {
            reflection_phase(&canonical).conjugate()
        };
        (self.index[&canonical], coefficient * phase)
    }

    fn coefficient(&self, raw: &Key, coefficient: ComplexExact) -> (usize, Qsqrt2) {
        let (column, value) = self.complex_coefficient(raw, coefficient);
        assert_eq!(value.im, Qsqrt2::ZERO, "projected PSD entry is real");
        (column, value.re)
    }
}

#[derive(Default)]
struct SparseBuilder(BTreeMap<(usize, usize), f64>);

impl SparseBuilder {
    fn add(&mut self, row: usize, column: usize, value: Qsqrt2) {
        let value = value.to_f64();
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

fn polynomial_row(
    polynomial: &Polynomial,
    multiplier: &Key,
    moments: &MomentSpace,
) -> BTreeMap<usize, Qsqrt2> {
    let mut complex_row: BTreeMap<usize, ComplexExact> = BTreeMap::new();
    for (key, &coefficient) in polynomial {
        let (column, value) = moments.complex_coefficient(&shift(key, multiplier), coefficient);
        let next = complex_row
            .get(&column)
            .copied()
            .unwrap_or(ComplexExact::ZERO)
            + value;
        if next == ComplexExact::ZERO {
            complex_row.remove(&column);
        } else {
            complex_row.insert(column, next);
        }
    }
    let use_imaginary = complex_row.values().any(|value| value.im != Qsqrt2::ZERO);
    assert!(
        !use_imaginary || complex_row.values().all(|value| value.re == Qsqrt2::ZERO),
        "projected equality must have one reflection parity"
    );
    complex_row
        .into_iter()
        .filter_map(|(column, value)| {
            let value = if use_imaginary { value.im } else { value.re };
            (value != Qsqrt2::ZERO).then_some((column, value))
        })
        .collect()
}

fn projected_dynamics() -> [Polynomial; STATE_VARIABLES] {
    let p = variable(VARIABLES, P);
    let q = variable(VARIABLES, Q);
    let m = variable(VARIABLES, M);
    let n = variable(VARIABLES, N);
    let p_bar = anti_variable(VARIABLES, P);
    let q_bar = anti_variable(VARIABLES, Q);
    let x = variable(VARIABLES, X);
    let y = variable(VARIABLES, Y);
    let one = constant(VARIABLES, ComplexExact::ONE);
    [
        add(
            &scale(&p, -ComplexExact::I * ComplexExact::real(exact(1, 2))),
            &scale(&p_bar, ComplexExact::I * ComplexExact::real(exact(1, 2))),
        ),
        add(
            &scale(&q, -ComplexExact::I * ComplexExact::real(sqrt2(1, 2))),
            &scale(&q_bar, ComplexExact::I * ComplexExact::real(sqrt2(1, 2))),
        ),
        add(
            &scale(&m, -ComplexExact::I * ComplexExact::real(sqrt2(1, 2))),
            &scale(&n, ComplexExact::I),
        ),
        add(
            &scale(
                &multiply(
                    &add(
                        &scale(&x, ComplexExact::real(exact(2, 1))),
                        &scale(&one, -ComplexExact::ONE),
                    ),
                    &q,
                ),
                ComplexExact::I * ComplexExact::real(exact(1, 2)),
            ),
            &scale(
                &multiply(
                    &add(&one, &scale(&y, ComplexExact::real(exact(-2, 1)))),
                    &p_bar,
                ),
                ComplexExact::I * ComplexExact::real(sqrt2(1, 2)),
            ),
        ),
    ]
}

fn embed_state(key: &Key) -> Key {
    let mut anti = vec![0; VARIABLES];
    let mut holo = vec![0; VARIABLES];
    for (state, &bulk) in STATE_TO_BULK.iter().enumerate() {
        anti[bulk] = key.anti.0[state];
        holo[bulk] = key.holo.0[state];
    }
    Key {
        anti: Exponent(anti),
        holo: Exponent(holo),
    }
}

fn liouville_derivative(test: &Key) -> Polynomial {
    let dynamics = projected_dynamics();
    let mut derivative = Polynomial::new();
    for (variable, dynamic) in dynamics.iter().enumerate() {
        if test.holo.0[variable] != 0 {
            let mut reduced = test.clone();
            reduced.holo.0[variable] -= 1;
            let coefficient = ComplexExact::real(exact(i128::from(test.holo.0[variable]), 1));
            derivative = add(
                &derivative,
                &scale(
                    &multiply(
                        &BTreeMap::from([(embed_state(&reduced), ComplexExact::ONE)]),
                        dynamic,
                    ),
                    coefficient,
                ),
            );
        }
        if test.anti.0[variable] != 0 {
            let mut reduced = test.clone();
            reduced.anti.0[variable] -= 1;
            let coefficient = ComplexExact::real(exact(i128::from(test.anti.0[variable]), 1));
            derivative = add(
                &derivative,
                &scale(
                    &multiply(
                        &BTreeMap::from([(embed_state(&reduced), ComplexExact::ONE)]),
                        &conjugate(dynamic),
                    ),
                    coefficient,
                ),
            );
        }
    }
    derivative
}

fn boundary_value(test: &Key, target: bool) -> i64 {
    if test.anti.0[X] != 0
        || test.holo.0[X] != 0
        || test.anti.0[Y] != 0
        || test.holo.0[Y] != 0
        || test.anti.0[J] != 0
        || test.holo.0[J] != 0
    {
        0
    } else if target && !(test.anti.0[C] + test.holo.0[C]).is_multiple_of(2) {
        -1
    } else {
        1
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SharedControlLiftStructure {
    pub order: u8,
    pub maximum_moment_degree: u8,
    pub moment_count: usize,
    pub ideal_equality_count: usize,
    pub liouville_equality_count: usize,
    pub psd_block_sides: Vec<usize>,
    pub largest_psd_side: usize,
    pub formulation: &'static str,
    pub rigor: &'static str,
}

#[derive(Clone, Debug)]
pub struct SharedControlLiftProblem {
    pub structure: SharedControlLiftStructure,
    pub conic: ConicProblem,
}

pub fn assemble(order: u8) -> Result<SharedControlLiftProblem, String> {
    if order < 2 {
        return Err("shared-control lift order must be at least two".into());
    }
    let maximum_degree = 2 * u16::from(order);
    let moments = MomentSpace::create(maximum_degree);
    let mut q_objective = vec![0.0; moments.keys.len()];
    for (variable_index, coefficient) in [(X, 0.5), (Y, 0.25)] {
        let key = variable(VARIABLES, variable_index)
            .into_iter()
            .next()
            .unwrap()
            .0;
        q_objective[moments.coefficient(&key, ComplexExact::ONE).0] = coefficient;
    }
    let mut sparse = SparseBuilder::default();
    let mut b = Vec::new();
    let mut ideal_count = 0;
    for (_, polynomial) in support_equalities() {
        let degree = polynomial.keys().map(Key::degree).max().unwrap();
        for multiplier in normalized_monomials(VARIABLES, maximum_degree - degree, &REAL_VARIABLES)
            .into_iter()
            .filter(|key| *key <= key.conjugate())
        {
            let row = polynomial_row(&polynomial, &multiplier, &moments);
            for (column, value) in row {
                sparse.add(b.len(), column, value);
            }
            b.push(0.0);
            ideal_count += 1;
        }
    }
    let tests = normalized_monomials(STATE_VARIABLES, maximum_degree, &STATE_REAL_VARIABLES)
        .into_iter()
        .filter(|test| *test <= test.conjugate())
        .filter_map(|test| {
            let derivative = liouville_derivative(&test);
            (!derivative.is_empty()
                && derivative.keys().map(Key::degree).max().unwrap() <= maximum_degree)
                .then_some((test, derivative))
        })
        .collect::<Vec<_>>();
    for (test, derivative) in &tests {
        for (column, value) in polynomial_row(
            derivative,
            &Key {
                anti: Exponent(vec![0; VARIABLES]),
                holo: Exponent(vec![0; VARIABLES]),
            },
            &moments,
        ) {
            sparse.add(b.len(), column, value);
        }
        b.push((boundary_value(test, true) - boundary_value(test, false)) as f64);
    }
    let zero_rows = b.len();
    let mut cones = vec![Cone::Zero(zero_rows)];
    let mut psd_sides = Vec::new();
    for support in [
        constant(VARIABLES, ComplexExact::ONE),
        population_product(X),
        population_product(Y),
    ] {
        let support_degree = support.keys().map(Key::degree).max().unwrap();
        let basis_degree = u16::from(order) - support_degree.div_ceil(2);
        let basis = monomials(VARIABLES, basis_degree);
        let side = basis.len();
        for column in 0..side {
            for row in 0..=column {
                let left = Key {
                    anti: Exponent(basis[row].0.clone()),
                    holo: Exponent(vec![0; VARIABLES]),
                };
                let right = Key {
                    anti: Exponent(vec![0; VARIABLES]),
                    holo: Exponent(basis[column].0.clone()),
                };
                let base = shift(&left, &right);
                let basis_phase = reflection_phase(&Key {
                    anti: Exponent(vec![0; VARIABLES]),
                    holo: basis[row].clone(),
                })
                .conjugate()
                    * reflection_phase(&Key {
                        anti: Exponent(vec![0; VARIABLES]),
                        holo: basis[column].clone(),
                    });
                let svec = if row == column {
                    ComplexExact::ONE
                } else {
                    ComplexExact::real(sqrt2(1, 1))
                };
                for (support_key, &coefficient) in &support {
                    let (moment, value) = moments
                        .coefficient(&shift(&base, support_key), basis_phase * coefficient * svec);
                    sparse.add(b.len(), moment, -value);
                }
                b.push(0.0);
            }
        }
        cones.push(Cone::PsdTriangle(side));
        psd_sides.push(side);
    }
    let conic = ConicProblem {
        q: q_objective,
        a: SparseMatrix {
            rows: b.len(),
            cols: moments.keys.len(),
            entries: sparse.finish(),
        },
        b,
        cones,
    };
    conic.validate()?;
    Ok(SharedControlLiftProblem {
        structure: SharedControlLiftStructure {
            order,
            maximum_moment_degree: 2 * order,
            moment_count: moments.keys.len(),
            ideal_equality_count: ideal_count,
            liouville_equality_count: tests.len(),
            largest_psd_side: psd_sides.iter().copied().max().unwrap_or(0),
            psd_block_sides: psd_sides,
            formulation: "standalone singular-safe shared-control invariant occupation lift",
            rigor: "exploratory; projected functional may contain spurious trajectories",
        },
        conic,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_singular_safe_identity_is_present_and_exact() {
        let equalities = support_equalities();
        let polynomial = &equalities
            .iter()
            .find(|(label, _)| *label == "singular_safe_shared_control")
            .unwrap()
            .1;
        assert_eq!(polynomial.len(), 3);
        assert_eq!(polynomial.keys().map(Key::degree).max(), Some(3));
    }

    #[test]
    fn assembles_order_two_projected_problem() {
        let problem = assemble(2).unwrap();
        assert_eq!(problem.structure.psd_block_sides, vec![45, 9, 9]);
        assert!(problem.structure.moment_count > 1_000);
        assert!(problem.structure.ideal_equality_count > 500);
        assert!(problem.structure.liouville_equality_count > 50);
    }

    #[test]
    fn archived_upstream_composed_results_are_byte_preserved() {
        let order_two: serde_json::Value = serde_json::from_str(include_str!(
            "../../../golden/shared-control-lift-upstream-o2.json"
        ))
        .unwrap();
        let order_three: serde_json::Value = serde_json::from_str(include_str!(
            "../../../golden/shared-control-lift-upstream-o3.json"
        ))
        .unwrap();
        assert_eq!(order_two["projected_complex_moment_variable_count"], 1996);
        assert_eq!(order_two["projected_ideal_constraint_count"], 1033);
        assert_eq!(order_two["projected_liouville_constraint_count"], 119);
        assert_eq!(
            order_three["projected_complex_moment_variable_count"],
            27412
        );
        assert_eq!(order_three["projected_ideal_constraint_count"], 31348);
        assert_eq!(order_three["projected_liouville_constraint_count"], 579);
    }
}
