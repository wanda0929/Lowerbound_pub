use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Exponents are serialized in variable order and sorted by total degree, then lexicographically.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct Exponent(pub Vec<u16>);

impl Exponent {
    pub fn degree(&self) -> u16 {
        self.0.iter().sum()
    }
}

pub fn monomials(variables: usize, max_degree: u16) -> Vec<Exponent> {
    fn compositions(remaining: u16, slots: usize, prefix: &mut Vec<u16>, out: &mut Vec<Exponent>) {
        if slots == 1 {
            prefix.push(remaining);
            out.push(Exponent(prefix.clone()));
            prefix.pop();
            return;
        }
        // Ascending first exponent gives a stable lexicographic convention.
        for value in 0..=remaining {
            prefix.push(value);
            compositions(remaining - value, slots - 1, prefix, out);
            prefix.pop();
        }
    }

    assert!(variables > 0);
    let mut out = Vec::new();
    for degree in 0..=max_degree {
        compositions(degree, variables, &mut Vec::new(), &mut out);
    }
    out
}

pub fn basis_hash(basis: &[Exponent]) -> String {
    let bytes = serde_json::to_vec(basis).expect("exponents serialize");
    format!("sha256:{:x}", Sha256::digest(bytes))
}

/// Degree-preserving normal form modulo `x² + y² - 1`, eliminating powers `y >= 2`.
/// Returns `(coefficient, exponent)` terms in deterministic order.
pub fn circle_normal_form(exponent: &Exponent, x: usize, y: usize) -> Vec<(i64, Exponent)> {
    assert!(x < exponent.0.len() && y < exponent.0.len() && x != y);
    let pairs = exponent.0[y] / 2;
    let odd = exponent.0[y] % 2;
    let mut terms = Vec::new();
    // y^(2p+odd) = y^odd * (1-x²)^p.
    for k in 0..=pairs {
        let binomial = (0..k).fold(1_i64, |acc, j| {
            acc * i64::from(pairs - j) / i64::from(j + 1)
        });
        let sign = if k % 2 == 0 { 1 } else { -1 };
        let mut e = exponent.0.clone();
        e[y] = odd;
        e[x] += 2 * k;
        terms.push((sign * binomial, Exponent(e)));
    }
    terms.sort_by(|a, b| a.1.cmp(&b.1));
    terms
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_and_order_are_deterministic() {
        let basis = monomials(3, 4);
        assert_eq!(basis.len(), 35);
        assert!(basis.windows(2).all(|w| {
            w[0].degree() < w[1].degree() || (w[0].degree() == w[1].degree() && w[0] < w[1])
        }));
        assert_eq!(basis_hash(&basis), basis_hash(&monomials(3, 4)));
    }

    #[test]
    fn circle_reduction_preserves_degree_bound() {
        let e = Exponent(vec![1, 4]);
        let terms = circle_normal_form(&e, 0, 1);
        assert_eq!(
            terms,
            vec![
                (1, Exponent(vec![1, 0])),
                (-2, Exponent(vec![3, 0])),
                (1, Exponent(vec![5, 0]))
            ]
        );
        assert!(terms.iter().all(|(_, term)| term.degree() <= e.degree()));
    }
}
