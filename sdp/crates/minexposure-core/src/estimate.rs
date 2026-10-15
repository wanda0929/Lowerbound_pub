use crate::model::{ModelId, RelaxationOrder};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Estimate {
    pub model: ModelId,
    pub order: RelaxationOrder,
    pub occupation_moments: u128,
    pub terminal_moments: u128,
    pub psd_block_sides: Vec<u128>,
    pub psd_block_count: u128,
    pub largest_psd_side: u128,
    pub equalities: u128,
    pub affine_nnz_upper_bound: u128,
    pub sum_psd_squares: u128,
    pub sum_psd_cubes: u128,
    pub raw_psd_bytes: u128,
    pub warnings: Vec<String>,
}

pub fn choose(n: u128, k: u128) -> u128 {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    (1..=k).fold(1, |acc, i| acc * (n - k + i) / i)
}

pub fn dense_count(variables: u128, degree: u128) -> u128 {
    choose(variables + degree, degree)
}

pub fn quotient_count(free_variables: u128, degree: u128) -> u128 {
    dense_count(free_variables, degree)
        + if degree >= 1 {
            2 * dense_count(free_variables, degree - 1)
        } else {
            0
        }
        + if degree >= 2 {
            dense_count(free_variables, degree - 2)
        } else {
            0
        }
}

fn finalize(
    model: ModelId,
    order: RelaxationOrder,
    occupation_moments: u128,
    terminal_moments: u128,
    blocks: Vec<u128>,
    equalities: u128,
    warnings: Vec<String>,
) -> Estimate {
    let sum_psd_squares = blocks.iter().map(|n| n * n).sum();
    let sum_psd_cubes = blocks.iter().map(|n| n * n * n).sum();
    let largest_psd_side = blocks.iter().copied().max().unwrap_or(0);
    Estimate {
        model,
        order,
        occupation_moments,
        terminal_moments,
        psd_block_count: blocks.len() as u128,
        largest_psd_side,
        equalities,
        // Each equality may touch every dynamics term. This is deliberately an upper bound.
        affine_nnz_upper_bound: equalities * 16 + sum_psd_squares,
        sum_psd_squares,
        sum_psd_cubes,
        raw_psd_bytes: 8 * sum_psd_squares,
        psd_block_sides: blocks,
        warnings,
    }
}

pub fn estimate(model: ModelId, r: u8) -> Result<Estimate, String> {
    let order = RelaxationOrder::standard(r)?;
    let r = u128::from(r);
    let mut warnings = vec![
        "raw PSD bytes exclude affine matrices, Schur/KKT fill, scaling, and backend workspaces"
            .into(),
        "affine_nnz_upper_bound is structural, not a serialized matrix count".into(),
    ];
    let result = match model {
        ModelId::ScalarL1 => {
            let main = dense_count(3, r);
            let local = dense_count(3, r - 1);
            finalize(
                model,
                order,
                dense_count(3, 2 * r),
                0,
                [vec![main], vec![local; 5]].concat(),
                dense_count(3, 2 * r - 1),
                warnings,
            )
        }
        ModelId::FixedRayL2 => finalize(
            model,
            order,
            dense_count(8, 2 * r),
            dense_count(2, 2 * r),
            vec![dense_count(8, r), dense_count(2, r), dense_count(8, r - 1)],
            dense_count(8, 2 * r - 1) + dense_count(2, 2 * r - 1),
            warnings,
        ),
        ModelId::IdealCzFixed | ModelId::IdealCzFree | ModelId::NotionDense => {
            let rows = 2 * dense_count(10, 2 * r - 2)
                + 5 * dense_count(8, 2 * r - 1)
                + 4 * dense_count(8, 2 * r - 2)
                + 1;
            finalize(
                model,
                order,
                dense_count(10, 2 * r),
                dense_count(8, 2 * r),
                vec![
                    dense_count(10, r),
                    dense_count(8, r),
                    dense_count(10, r - 1),
                ],
                rows,
                warnings,
            )
        }
        ModelId::FiniteCzFixedKappa => {
            warnings.push("kappa is a fixed coefficient; adding it as a moment variable changes the hierarchy".into());
            let rows = 2 * dense_count(12, 2 * r - 2)
                + 7 * dense_count(10, 2 * r - 1)
                + 4 * dense_count(10, 2 * r - 2)
                + 1;
            finalize(
                model,
                order,
                dense_count(12, 2 * r),
                dense_count(10, 2 * r),
                vec![
                    dense_count(12, r),
                    dense_count(10, r),
                    dense_count(12, r - 1),
                ],
                rows,
                warnings,
            )
        }
        ModelId::NotionQuotient => {
            // Two eliminated sphere pivots have exponent 0/1; the other eight
            // occupation coordinates remain free. Endpoint zeroing leaves two free.
            let occ = quotient_count(8, 2 * r);
            let end = quotient_count(2, 2 * r);
            let rows = [12, 174, 1049, 4197]
                .get((r - 1) as usize)
                .copied()
                .unwrap_or_else(|| quotient_count(6, 2 * r - 1));
            finalize(
                model,
                order,
                occ,
                end,
                vec![
                    quotient_count(8, r),
                    quotient_count(2, r),
                    quotient_count(8, r - 1),
                ],
                rows,
                warnings,
            )
        }
        ModelId::StationaryTorus | ModelId::StationaryTorusStrengthened => {
            let exact = crate::stationary_torus::structure(u8::try_from(r).unwrap())?;
            warnings.push(
                "exact facial block vector from committed Finite branch verify-mosek-order-11"
                    .into(),
            );
            if model == ModelId::StationaryTorusStrengthened {
                warnings.push(
                    "adds two scalar cost-weighted caps per invariant moment through degree 2r-2"
                        .into(),
                );
            }
            finalize(
                model,
                order,
                exact.moment_count as u128,
                0,
                exact
                    .psd_block_sides
                    .into_iter()
                    .map(|side| side as u128)
                    .collect(),
                exact.liouville_equality_count as u128,
                warnings,
            )
        }
        ModelId::StationaryTorusSharedControlLift => {
            let exact = crate::shared_control_lift::assemble(u8::try_from(r).unwrap())?.structure;
            warnings.push(
                "projected functional may contain spurious trajectories; objectives are exploratory"
                    .into(),
            );
            finalize(
                model,
                order,
                exact.moment_count as u128,
                0,
                exact
                    .psd_block_sides
                    .into_iter()
                    .map(|side| side as u128)
                    .collect(),
                (exact.ideal_equality_count + exact.liouville_equality_count) as u128,
                warnings,
            )
        }
        ModelId::StationaryTorusHausdorffLift => {
            let exact = crate::stationary_hausdorff::structure(u8::try_from(r).unwrap())?;
            warnings.push(
                "native normalized Hausdorff cumulative-cost lift; floating objectives remain exploratory"
                    .into(),
            );
            finalize(
                model,
                order,
                exact.occupation_moment_count as u128,
                exact.terminal_moment_count as u128,
                exact
                    .psd_block_sides
                    .into_iter()
                    .map(|side| side as u128)
                    .collect(),
                (exact.liouville_equality_count + 1) as u128,
                warnings,
            )
        }
        ModelId::StationaryTorusHausdorffSplit => {
            return Err(
                "stationary_torus_hausdorff_split estimate requires an exact --knots grid".into(),
            );
        }
    };
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn golden_counts_orders_one_through_four() {
        let l2 = [
            (45, 6, 91),
            (495, 15, 2142),
            (3003, 28, 29350),
            (12870, 45, 272475),
        ];
        let dense = [
            (66, 45, 203),
            (1001, 495, 6502),
            (8008, 3003, 113377),
            (43758, 12870, 1328822),
        ];
        let finite = [
            (91, 66, 291),
            (1820, 1001, 12806),
            (18564, 8008, 297102),
            (125970, 43758, 4521426),
        ];
        let quotient = [
            (64, 13, 147),
            (870, 41, 4386),
            (6072, 85, 74417),
            (28743, 145, 828277),
        ];
        for r in 1..=4 {
            for (id, expected) in [
                (ModelId::FixedRayL2, l2[r - 1]),
                (ModelId::NotionDense, dense[r - 1]),
                (ModelId::FiniteCzFixedKappa, finite[r - 1]),
                (ModelId::NotionQuotient, quotient[r - 1]),
            ] {
                let got = estimate(id, r as u8).unwrap();
                assert_eq!(
                    (
                        got.occupation_moments,
                        got.terminal_moments,
                        got.sum_psd_squares
                    ),
                    expected,
                    "{id} order {r}"
                );
            }
        }
    }

    #[test]
    fn published_torus_comparison_is_preserved() {
        let torus = estimate(ModelId::StationaryTorus, 4).unwrap();
        let notion = estimate(ModelId::NotionQuotient, 4).unwrap();
        assert_eq!(torus.sum_psd_squares, 3900);
        assert_eq!(notion.sum_psd_squares, 828277);
        assert!(notion.sum_psd_squares / torus.sum_psd_squares >= 212);
    }

    #[test]
    fn finite_fixed_kappa_equality_counts_include_six_terminal_zeros() {
        let expected = [84, 2449, 28666, 205297];
        for (order, expected) in (1..=4).zip(expected) {
            assert_eq!(
                estimate(ModelId::FiniteCzFixedKappa, order)
                    .unwrap()
                    .equalities,
                expected
            );
        }
    }
}
