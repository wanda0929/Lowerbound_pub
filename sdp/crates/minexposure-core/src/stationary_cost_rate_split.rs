//! Exploratory two-axis split of the cumulative-cost stationary-torus lift.
//!
//! The existing local cumulative-cost coordinate `xi` is supplemented by a
//! partition of the physical running-cost rate
//! `c=|r1|^2/2+|r2|^2/4`.  Conceptually, rate interfaces carry separate
//! nonnegative upward and downward crossing measures.  Only their difference
//! occurs in Liouville balance, so assembly exactly eliminates the Jordan pair
//! to one free signed flux after quotienting by `c=rate`; the witness diagnostic
//! retains both crossing directions.  Supplying only the endpoint rate cell
//! delegates to the unchanged cumulative-cost split assembly.

use crate::algebra::{Qsqrt2, Rational};
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::estimate::Estimate;
use crate::model::{ModelId, RelaxationOrder};
use crate::stationary_hausdorff::{
    CostMonomial, EXPOSURE_UPPER, ExactCertificateModel, MomentSpace, RateInterfaceMomentSpace,
    boundary_moment_position, exact_certificate_model, initial_value, interface_gram_bases,
    interface_gram_entry_coefficients, liouville_tests, rate_localizer_gram_bases,
    rate_localizer_gram_entry_coefficients, reflection_phase_is_i, scaled_liouville_coefficients,
    target_value,
};
use crate::stationary_hausdorff_split::{self, SplitGrid};
use crate::stationary_torus::IdealBlockadePulse;
use num_complex::Complex64;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt;
use std::str::FromStr;

const BULK_VARIABLES: usize = 5;
const STATE_VARIABLES: usize = 4;
const MAXIMUM_RATE: Rational = Rational {
    numerator: 3,
    denominator: 4,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RateGrid {
    knots: Vec<Rational>,
}

impl RateGrid {
    pub fn new(knots: Vec<Rational>) -> Result<Self, String> {
        if knots.len() < 2 {
            return Err("rate grid requires at least the endpoint knots 0,3/4".into());
        }
        if knots[0] != Rational::ZERO || knots[knots.len() - 1] != MAXIMUM_RATE {
            return Err("rate grid endpoints must be exactly 0 and 3/4".into());
        }
        for (index, pair) in knots.windows(2).enumerate() {
            if rational_difference(pair[1], pair[0])?.numerator <= 0 {
                return Err(format!(
                    "rate grid knots must be strictly increasing (positions {index} and {})",
                    index + 1
                ));
            }
        }
        Ok(Self { knots })
    }

    pub fn knots(&self) -> &[Rational] {
        &self.knots
    }

    pub fn cell_count(&self) -> usize {
        self.knots.len() - 1
    }

    pub fn canonical_knots(&self) -> Vec<String> {
        self.knots.iter().map(ToString::to_string).collect()
    }

    pub fn canonical_hash(&self) -> String {
        hash_json(&serde_json::json!({
            "schema": "minexposure/cost-rate-grid-v1",
            "knots": self.canonical_knots(),
            "maximum_rate": MAXIMUM_RATE,
        }))
    }

    fn is_degenerate(&self) -> bool {
        self.knots == [Rational::ZERO, MAXIMUM_RATE]
    }
}

impl FromStr for RateGrid {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value.trim().is_empty() {
            return Err("rate grid cannot be empty".into());
        }
        let knots = value
            .split(',')
            .enumerate()
            .map(|(index, knot)| {
                knot.trim()
                    .parse::<Rational>()
                    .map_err(|error| format!("invalid rate grid knot {}: {error}", index + 1))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(knots)
    }
}

impl fmt::Display for RateGrid {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.canonical_knots().join(","))
    }
}

fn rational_difference(upper: Rational, lower: Rational) -> Result<Rational, String> {
    let upper_scaled = upper
        .numerator
        .checked_mul(lower.denominator)
        .ok_or("rational numerator overflow")?;
    let lower_scaled = lower
        .numerator
        .checked_mul(upper.denominator)
        .ok_or("rational numerator overflow")?;
    let numerator = upper_scaled
        .checked_sub(lower_scaled)
        .ok_or("rational numerator overflow")?;
    let denominator = upper
        .denominator
        .checked_mul(lower.denominator)
        .ok_or("rational denominator overflow")?;
    Ok(Rational::new(numerator, denominator))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RateSplitBlockFamily {
    Occupation,
    OccupationRateLocalizer,
    XiInterfaceMoment,
    XiInterfaceRateLocalizer,
    TerminalMoment,
    TerminalXiInterval,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct StationaryCostRateSplitStructure {
    pub schema: &'static str,
    pub rigor: &'static str,
    pub order: u8,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub rate_knots: Vec<String>,
    pub rate_grid_hash: String,
    pub xi_cell_count: usize,
    pub rate_cell_count: usize,
    pub occupation_moment_count_per_cell: usize,
    pub occupation_moment_count: usize,
    pub xi_interface_moment_count_per_measure: usize,
    pub xi_interface_measure_count: usize,
    pub rate_interface_moment_count_per_measure: usize,
    pub rate_interface_measure_count: usize,
    pub rate_interface_directional_measure_count: usize,
    pub terminal_moment_count_per_xi_cell: usize,
    pub terminal_moment_count: usize,
    pub liouville_equality_count_per_cell: usize,
    pub liouville_equality_count: usize,
    pub rate_ideal_equality_count_per_measure: usize,
    pub rate_ideal_equality_count: usize,
    pub normalization_equality_count: usize,
    pub occupation_block_count_per_cell: usize,
    pub occupation_rate_localizer_block_count_per_cell: usize,
    pub xi_interface_moment_block_count_per_measure: usize,
    pub xi_interface_rate_localizer_block_count_per_measure: usize,
    pub rate_interface_moment_block_count_per_measure: usize,
    pub rate_interface_interval_block_count_per_measure: usize,
    pub psd_block_families: Vec<RateSplitBlockFamily>,
    pub psd_block_sides: Vec<usize>,
    pub largest_psd_side: usize,
    pub sum_psd_squares: usize,
    pub sum_psd_cubes: usize,
    pub occupation_basis_hash: String,
    pub xi_interface_basis_hash: String,
    pub rate_interface_basis_hash: String,
    pub liouville_basis_hash: String,
    pub formulation_hash: String,
    pub exposure_upper: Rational,
    pub maximum_rate: Rational,
    pub degenerate_baseline: bool,
}

#[derive(Clone, Debug)]
pub struct StationaryCostRateSplitProblem {
    pub structure: StationaryCostRateSplitStructure,
    pub conic: ConicProblem,
}

#[derive(Clone, Debug)]
struct RateSplitRow {
    coefficients: Vec<(usize, Qsqrt2)>,
    rhs: i64,
}

#[derive(Clone, Debug)]
struct RateSplitModel {
    base: ExactCertificateModel,
    xi_interfaces: MomentSpace,
    xi_interface_bases: Vec<Vec<CostMonomial>>,
    rate_interfaces: Vec<RateInterfaceMomentSpace>,
    occupation_rate_bases: Vec<Vec<CostMonomial>>,
    xi_interface_rate_bases: Vec<Vec<CostMonomial>>,
    rows: Vec<RateSplitRow>,
    occupation_offsets: Vec<usize>,
    xi_interface_offsets: Vec<usize>,
    rate_interface_offsets: Vec<usize>,
    terminal_offsets: Vec<usize>,
    terminal_count: usize,
    coefficient_count: usize,
    xi_cells: usize,
    rate_cells: usize,
}

impl RateSplitModel {
    fn create(order: u8, xi_grid: &SplitGrid, rate_grid: &RateGrid) -> Result<Self, String> {
        if rate_grid.is_degenerate() {
            return Err("the degenerate rate grid uses the baseline split model".into());
        }
        let base = exact_certificate_model(order)?;
        let tests = liouville_tests(order);
        let inverse_widths = xi_grid.inverse_widths()?;
        let xi_interfaces = MomentSpace::interface(order);
        let xi_interface_bases = interface_gram_bases(order);
        let rate_interfaces = rate_grid.knots()[1..rate_grid.knots().len() - 1]
            .iter()
            .map(|&rate| RateInterfaceMomentSpace::create(order, rate))
            .collect::<Vec<_>>();
        let occupation_rate_bases = rate_localizer_gram_bases(order, BULK_VARIABLES);
        let xi_interface_rate_bases = rate_localizer_gram_bases(order, STATE_VARIABLES);
        let xi_cells = xi_grid.cell_count();
        let rate_cells = rate_grid.cell_count();
        let occupation_count = base.moments().keys.len();
        let xi_interface_count = xi_interfaces.keys.len();
        let rate_interface_count = rate_interfaces[0].keys.len();
        debug_assert!(
            rate_interfaces
                .iter()
                .all(|moments| moments.keys.len() == rate_interface_count)
        );
        let terminal_count = 2 * usize::from(order) + 1;

        let occupation_offsets = (0..xi_cells * rate_cells)
            .map(|cell| cell * occupation_count)
            .collect::<Vec<_>>();
        let xi_interface_base = occupation_offsets.len() * occupation_count;
        let xi_interface_offsets = (0..xi_cells.saturating_sub(1) * rate_cells)
            .map(|interface| xi_interface_base + interface * xi_interface_count)
            .collect::<Vec<_>>();
        let rate_interface_base =
            xi_interface_base + xi_interface_offsets.len() * xi_interface_count;
        // If sigma=nu_up-nu_down, every finite signed interface functional has
        // a Jordan decomposition into two nonnegative measures.  Since neither
        // direction occurs anywhere except through sigma, retaining one free
        // quotient-moment vector is exactly equivalent and avoids a singular
        // pair of PSD moment cones.
        let rate_interface_offsets = (0..xi_cells * (rate_cells - 1))
            .map(|interface| rate_interface_base + interface * rate_interface_count)
            .collect::<Vec<_>>();
        let terminal_base =
            rate_interface_base + rate_interface_offsets.len() * rate_interface_count;
        let terminal_offsets = (0..xi_cells)
            .map(|cell| terminal_base + cell * terminal_count)
            .collect::<Vec<_>>();
        let coefficient_count = terminal_base + xi_cells * terminal_count;

        let occupation_offset =
            |xi_cell: usize, rate_cell: usize| occupation_offsets[xi_cell * rate_cells + rate_cell];
        let xi_interface_offset = |interface: usize, rate_cell: usize| {
            xi_interface_offsets[interface * rate_cells + rate_cell]
        };
        let rate_interface_offset = |xi_cell: usize, interface: usize| {
            rate_interface_offsets[xi_cell * (rate_cells - 1) + interface]
        };

        let mut rows = Vec::with_capacity(xi_cells * rate_cells * tests.len());
        for (xi_cell, &inverse_width) in inverse_widths.iter().enumerate() {
            for rate_cell in 0..rate_cells {
                for test in &tests {
                    let mut coefficients =
                        scaled_liouville_coefficients(test, inverse_width, base.moments())
                            .into_iter()
                            .map(|(position, coefficient)| {
                                (
                                    occupation_offset(xi_cell, rate_cell) + position,
                                    coefficient,
                                )
                            })
                            .collect::<Vec<_>>();

                    let xi_boundary_position = boundary_moment_position(&xi_interfaces, test);
                    if xi_cell != 0 && test.cost_power == 0 {
                        coefficients.push((
                            xi_interface_offset(xi_cell - 1, rate_cell) + xi_boundary_position,
                            Qsqrt2::from(1),
                        ));
                    }
                    if xi_cell + 1 < xi_cells {
                        coefficients.push((
                            xi_interface_offset(xi_cell, rate_cell) + xi_boundary_position,
                            Qsqrt2::from(-1),
                        ));
                    }

                    if rate_cell != 0 {
                        let interface = rate_cell - 1;
                        for (position, coefficient) in rate_interfaces[interface].coefficients(test)
                        {
                            coefficients.push((
                                rate_interface_offset(xi_cell, interface) + position,
                                coefficient,
                            ));
                        }
                    }
                    if rate_cell + 1 < rate_cells {
                        let interface = rate_cell;
                        for (position, coefficient) in rate_interfaces[interface].coefficients(test)
                        {
                            coefficients.push((
                                rate_interface_offset(xi_cell, interface) + position,
                                -coefficient,
                            ));
                        }
                    }

                    let target = target_value(test);
                    if rate_cell == 0 && target != 0 {
                        coefficients.push((
                            terminal_offsets[xi_cell] + usize::from(test.cost_power),
                            Qsqrt2::from(-target),
                        ));
                    }
                    rows.push(RateSplitRow {
                        coefficients,
                        rhs: if xi_cell == 0 && rate_cell == 0 {
                            -initial_value(test)
                        } else {
                            0
                        },
                    });
                }
            }
        }

        Ok(Self {
            base,
            xi_interfaces,
            xi_interface_bases,
            rate_interfaces,
            occupation_rate_bases,
            xi_interface_rate_bases,
            rows,
            occupation_offsets,
            xi_interface_offsets,
            rate_interface_offsets,
            terminal_offsets,
            terminal_count,
            coefficient_count,
            xi_cells,
            rate_cells,
        })
    }

    #[cfg(test)]
    fn rate_interface_offset(&self, xi_cell: usize, interface: usize) -> usize {
        self.rate_interface_offsets[xi_cell * (self.rate_cells - 1) + interface]
    }
}

pub fn structure(
    order: u8,
    xi_grid: &SplitGrid,
    rate_grid: &RateGrid,
) -> Result<StationaryCostRateSplitStructure, String> {
    if rate_grid.is_degenerate() {
        let baseline = stationary_hausdorff_split::structure(order, xi_grid)?;
        let psd_block_families = baseline
            .psd_block_families
            .iter()
            .map(|family| match family {
                stationary_hausdorff_split::BlockFamily::Occupation => {
                    RateSplitBlockFamily::Occupation
                }
                stationary_hausdorff_split::BlockFamily::InterfaceMoment => {
                    RateSplitBlockFamily::XiInterfaceMoment
                }
                stationary_hausdorff_split::BlockFamily::TerminalMoment => {
                    RateSplitBlockFamily::TerminalMoment
                }
                stationary_hausdorff_split::BlockFamily::TerminalInterval => {
                    RateSplitBlockFamily::TerminalXiInterval
                }
            })
            .collect();
        return Ok(StationaryCostRateSplitStructure {
            schema: "minexposure/stationary-torus-hausdorff-split-v1",
            rigor: "exploratory",
            order,
            knots: baseline.knots,
            split_grid_hash: baseline.split_grid_hash,
            rate_knots: rate_grid.canonical_knots(),
            rate_grid_hash: rate_grid.canonical_hash(),
            xi_cell_count: baseline.cell_count,
            rate_cell_count: 1,
            occupation_moment_count_per_cell: baseline.occupation_moment_count_per_cell,
            occupation_moment_count: baseline.occupation_moment_count,
            xi_interface_moment_count_per_measure: baseline.interface_moment_count_per_interface,
            xi_interface_measure_count: baseline.cell_count.saturating_sub(1),
            rate_interface_moment_count_per_measure: 0,
            rate_interface_measure_count: 0,
            rate_interface_directional_measure_count: 0,
            terminal_moment_count_per_xi_cell: baseline.terminal_moment_count_per_cell,
            terminal_moment_count: baseline.terminal_moment_count,
            liouville_equality_count_per_cell: baseline.liouville_equality_count_per_cell,
            liouville_equality_count: baseline.liouville_equality_count,
            rate_ideal_equality_count_per_measure: 0,
            rate_ideal_equality_count: 0,
            normalization_equality_count: 1,
            occupation_block_count_per_cell: baseline.occupation_moment_block_count_per_cell
                + baseline.occupation_interval_block_count_per_cell
                + baseline.occupation_interval_diagonal_count_per_cell,
            occupation_rate_localizer_block_count_per_cell: 0,
            xi_interface_moment_block_count_per_measure: baseline
                .interface_moment_block_count_per_interface,
            xi_interface_rate_localizer_block_count_per_measure: 0,
            rate_interface_moment_block_count_per_measure: 0,
            rate_interface_interval_block_count_per_measure: 0,
            psd_block_families,
            psd_block_sides: baseline.psd_block_sides,
            largest_psd_side: baseline.largest_psd_side,
            sum_psd_squares: baseline.sum_psd_squares,
            sum_psd_cubes: baseline.sum_psd_cubes,
            occupation_basis_hash: baseline.occupation_basis_hash,
            xi_interface_basis_hash: baseline.interface_basis_hash,
            rate_interface_basis_hash: hash_json(&Vec::<CostMonomial>::new()),
            liouville_basis_hash: baseline.liouville_basis_hash,
            formulation_hash: baseline.formulation_hash,
            exposure_upper: EXPOSURE_UPPER,
            maximum_rate: MAXIMUM_RATE,
            degenerate_baseline: true,
        });
    }

    let model = RateSplitModel::create(order, xi_grid, rate_grid)?;
    let occupation_sides = model.base.occupation_gram_dimensions();
    let occupation_rate_sides = model
        .occupation_rate_bases
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let xi_interface_sides = model
        .xi_interface_bases
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let xi_interface_rate_sides = model
        .xi_interface_rate_bases
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let mut psd_block_families = Vec::new();
    let mut psd_block_sides = Vec::new();
    for _ in 0..model.xi_cells * model.rate_cells {
        append_family(
            &mut psd_block_sides,
            &mut psd_block_families,
            &occupation_sides,
            RateSplitBlockFamily::Occupation,
        );
        append_family(
            &mut psd_block_sides,
            &mut psd_block_families,
            &occupation_rate_sides,
            RateSplitBlockFamily::OccupationRateLocalizer,
        );
    }
    for _ in 0..model.xi_cells.saturating_sub(1) * model.rate_cells {
        append_family(
            &mut psd_block_sides,
            &mut psd_block_families,
            &xi_interface_sides,
            RateSplitBlockFamily::XiInterfaceMoment,
        );
        append_family(
            &mut psd_block_sides,
            &mut psd_block_families,
            &xi_interface_rate_sides,
            RateSplitBlockFamily::XiInterfaceRateLocalizer,
        );
    }
    for _ in 0..model.xi_cells {
        psd_block_sides.extend([usize::from(order) + 1, usize::from(order)]);
        psd_block_families.extend([
            RateSplitBlockFamily::TerminalMoment,
            RateSplitBlockFamily::TerminalXiInterval,
        ]);
    }

    let knots = xi_grid.canonical_knots();
    let split_grid_hash = xi_grid.canonical_hash();
    let rate_knots = rate_grid.canonical_knots();
    let rate_grid_hash = rate_grid.canonical_hash();
    let occupation_basis_hash = hash_json(&model.base.moments().keys);
    let xi_interface_basis_hash = hash_json(&model.xi_interfaces.keys);
    let rate_interface_basis_hash = hash_json(&model.rate_interfaces[0].keys);
    let tests = liouville_tests(order);
    let liouville_basis_hash = hash_json(&tests);
    let formulation_hash = hash_json(&serde_json::json!({
        "schema": "minexposure/stationary-torus-cost-rate-split-exploratory-v1",
        "order": order,
        "knots": &knots,
        "split_grid_hash": &split_grid_hash,
        "rate_knots": &rate_knots,
        "rate_grid_hash": &rate_grid_hash,
        "occupation_basis_hash": &occupation_basis_hash,
        "xi_interface_basis_hash": &xi_interface_basis_hash,
        "rate_interface_basis_hash": &rate_interface_basis_hash,
        "liouville_basis_hash": &liouville_basis_hash,
        "psd_block_families": &psd_block_families,
        "psd_block_sides": &psd_block_sides,
        "rate_cell_support": "(c-lower)(upper-c)/(upper-lower)^2>=0",
        "rate_interface_ideal": "quotient normal form |r2|^2=4*rate-2|r1|^2",
        "rate_interface_semantics": "signed flux is the exact algebraic elimination of separate nonnegative upward and downward crossing measures",
        "terminal_rate": "c=0; first rate cell only",
        "field": "Q(sqrt(2))",
    }));
    let rate_interface_measure_count = model.rate_interface_offsets.len();
    Ok(StationaryCostRateSplitStructure {
        schema: "minexposure/stationary-torus-cost-rate-split-exploratory-v1",
        rigor: "exploratory",
        order,
        knots,
        split_grid_hash,
        rate_knots,
        rate_grid_hash,
        xi_cell_count: model.xi_cells,
        rate_cell_count: model.rate_cells,
        occupation_moment_count_per_cell: model.base.moments().keys.len(),
        occupation_moment_count: model.occupation_offsets.len() * model.base.moments().keys.len(),
        xi_interface_moment_count_per_measure: model.xi_interfaces.keys.len(),
        xi_interface_measure_count: model.xi_interface_offsets.len(),
        rate_interface_moment_count_per_measure: model.rate_interfaces[0].keys.len(),
        rate_interface_measure_count,
        rate_interface_directional_measure_count: 2 * rate_interface_measure_count,
        terminal_moment_count_per_xi_cell: model.terminal_count,
        terminal_moment_count: model.xi_cells * model.terminal_count,
        liouville_equality_count_per_cell: tests.len(),
        liouville_equality_count: model.rows.len(),
        rate_ideal_equality_count_per_measure: 0,
        rate_ideal_equality_count: 0,
        normalization_equality_count: 1,
        occupation_block_count_per_cell: occupation_sides.len(),
        occupation_rate_localizer_block_count_per_cell: occupation_rate_sides.len(),
        xi_interface_moment_block_count_per_measure: xi_interface_sides.len(),
        xi_interface_rate_localizer_block_count_per_measure: xi_interface_rate_sides.len(),
        rate_interface_moment_block_count_per_measure: 0,
        rate_interface_interval_block_count_per_measure: 0,
        largest_psd_side: psd_block_sides.iter().copied().max().unwrap_or(0),
        sum_psd_squares: psd_block_sides.iter().map(|side| side * side).sum(),
        sum_psd_cubes: psd_block_sides.iter().map(|side| side * side * side).sum(),
        psd_block_families,
        psd_block_sides,
        occupation_basis_hash,
        xi_interface_basis_hash,
        rate_interface_basis_hash,
        liouville_basis_hash,
        formulation_hash,
        exposure_upper: EXPOSURE_UPPER,
        maximum_rate: MAXIMUM_RATE,
        degenerate_baseline: false,
    })
}

fn append_family(
    sides: &mut Vec<usize>,
    families: &mut Vec<RateSplitBlockFamily>,
    new_sides: &[usize],
    family: RateSplitBlockFamily,
) {
    sides.extend(new_sides);
    families.extend(std::iter::repeat_n(family, new_sides.len()));
}

pub fn estimate(order: u8, xi_grid: &SplitGrid, rate_grid: &RateGrid) -> Result<Estimate, String> {
    if rate_grid.is_degenerate() {
        return stationary_hausdorff_split::estimate(order, xi_grid);
    }
    let structure = structure(order, xi_grid, rate_grid)?;
    let blocks = structure
        .psd_block_sides
        .iter()
        .map(|&side| side as u128)
        .collect::<Vec<_>>();
    let sum_psd_squares = blocks.iter().map(|side| side * side).sum();
    let sum_psd_cubes = blocks.iter().map(|side| side * side * side).sum();
    let equalities = (structure.liouville_equality_count
        + structure.rate_ideal_equality_count
        + structure.normalization_equality_count) as u128;
    Ok(Estimate {
        model: ModelId::StationaryTorusHausdorffSplit,
        order: RelaxationOrder::standard(order)?,
        occupation_moments: (structure.occupation_moment_count
            + structure.xi_interface_measure_count
                * structure.xi_interface_moment_count_per_measure
            + structure.rate_interface_measure_count
                * structure.rate_interface_moment_count_per_measure) as u128,
        terminal_moments: structure.terminal_moment_count as u128,
        psd_block_count: blocks.len() as u128,
        largest_psd_side: blocks.iter().copied().max().unwrap_or(0),
        affine_nnz_upper_bound: equalities * 20 + sum_psd_squares,
        equalities,
        sum_psd_squares,
        sum_psd_cubes,
        raw_psd_bytes: 8 * sum_psd_squares,
        psd_block_sides: blocks,
        warnings: vec![
            "exploratory two-axis cumulative-cost and running-cost-rate split; floating objectives are not bounds".into(),
            format!("xi grid {xi_grid}; rate grid {rate_grid}"),
            "rate interfaces use separate nonnegative upward/downward measures on the exact ideal c-rate=0".into(),
            "raw PSD bytes exclude affine matrices, Schur/KKT fill, scaling, and backend workspaces".into(),
        ],
    })
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

pub fn assemble(
    order: u8,
    xi_grid: &SplitGrid,
    rate_grid: &RateGrid,
) -> Result<StationaryCostRateSplitProblem, String> {
    let structure = structure(order, xi_grid, rate_grid)?;
    if rate_grid.is_degenerate() {
        let baseline = stationary_hausdorff_split::assemble(order, xi_grid)?;
        return Ok(StationaryCostRateSplitProblem {
            structure,
            conic: baseline.conic,
        });
    }
    let model = RateSplitModel::create(order, xi_grid, rate_grid)?;
    let mut q = vec![0.0; model.coefficient_count];
    for &offset in &model.occupation_offsets {
        for &(position, coefficient) in &model.base.cost {
            q[offset + position] = coefficient.to_f64();
        }
    }

    let mut sparse = SparseBuilder::default();
    let mut b = Vec::with_capacity(model.rows.len() + 1);
    for (row_index, equality) in model.rows.iter().enumerate() {
        for &(column, coefficient) in &equality.coefficients {
            sparse.add(row_index, column, coefficient);
        }
        b.push(equality.rhs as f64);
    }
    let normalization_row = b.len();
    for &terminal_offset in &model.terminal_offsets {
        sparse.add(normalization_row, terminal_offset, Qsqrt2::from(1));
    }
    b.push(1.0);

    let mut cones = vec![Cone::Zero(b.len())];
    let mut next_row = b.len();
    let occupation_dimensions = model.base.occupation_gram_dimensions();
    for (cell, &cell_offset) in model.occupation_offsets.iter().enumerate() {
        for (block_index, &side) in occupation_dimensions.iter().enumerate() {
            append_psd(
                side,
                &mut next_row,
                &mut b,
                &mut cones,
                |cone_row, row, column, scale| {
                    model.base.for_each_gram_entry_coefficient(
                        block_index,
                        row,
                        column,
                        |position, coefficient| {
                            sparse.add(cone_row, cell_offset + position, -(coefficient * scale));
                        },
                    );
                },
            );
        }
        let rate_cell = cell % model.rate_cells;
        let lower = rate_grid.knots()[rate_cell];
        let upper = rate_grid.knots()[rate_cell + 1];
        for basis in &model.occupation_rate_bases {
            append_psd(
                basis.len(),
                &mut next_row,
                &mut b,
                &mut cones,
                |cone_row, row, column, scale| {
                    for (position, coefficient) in rate_localizer_gram_entry_coefficients(
                        model.base.moments(),
                        &basis[row],
                        &basis[column],
                        lower,
                        upper,
                        BULK_VARIABLES,
                    ) {
                        sparse.add(cone_row, cell_offset + position, -(coefficient * scale));
                    }
                },
            );
        }
    }

    for (measure, &offset) in model.xi_interface_offsets.iter().enumerate() {
        for basis in &model.xi_interface_bases {
            append_psd(
                basis.len(),
                &mut next_row,
                &mut b,
                &mut cones,
                |cone_row, row, column, scale| {
                    for (position, coefficient) in interface_gram_entry_coefficients(
                        &model.xi_interfaces,
                        &basis[row],
                        &basis[column],
                    ) {
                        sparse.add(cone_row, offset + position, -(coefficient * scale));
                    }
                },
            );
        }
        let rate_cell = measure % model.rate_cells;
        let lower = rate_grid.knots()[rate_cell];
        let upper = rate_grid.knots()[rate_cell + 1];
        for basis in &model.xi_interface_rate_bases {
            append_psd(
                basis.len(),
                &mut next_row,
                &mut b,
                &mut cones,
                |cone_row, row, column, scale| {
                    for (position, coefficient) in rate_localizer_gram_entry_coefficients(
                        &model.xi_interfaces,
                        &basis[row],
                        &basis[column],
                        lower,
                        upper,
                        STATE_VARIABLES,
                    ) {
                        sparse.add(cone_row, offset + position, -(coefficient * scale));
                    }
                },
            );
        }
    }

    for &terminal_offset in &model.terminal_offsets {
        let moment_side = usize::from(order) + 1;
        append_psd(
            moment_side,
            &mut next_row,
            &mut b,
            &mut cones,
            |cone_row, row, column, scale| {
                sparse.add(cone_row, terminal_offset + row + column, -scale);
            },
        );
        let interval_side = usize::from(order);
        append_psd(
            interval_side,
            &mut next_row,
            &mut b,
            &mut cones,
            |cone_row, row, column, scale| {
                sparse.add(cone_row, terminal_offset + row + column + 1, -scale);
                sparse.add(cone_row, terminal_offset + row + column + 2, scale);
            },
        );
    }

    let conic = ConicProblem {
        q,
        a: SparseMatrix {
            rows: next_row,
            cols: model.coefficient_count,
            entries: sparse.finish(),
        },
        b,
        cones,
    };
    conic.validate()?;
    Ok(StationaryCostRateSplitProblem { structure, conic })
}

fn append_psd(
    side: usize,
    next_row: &mut usize,
    b: &mut Vec<f64>,
    cones: &mut Vec<Cone>,
    mut visit: impl FnMut(usize, usize, usize, Qsqrt2),
) {
    for column in 0..side {
        for row in 0..=column {
            let scale = if row == column {
                Qsqrt2::from(1)
            } else {
                Qsqrt2::new(Rational::ZERO, Rational::ONE)
            };
            visit(*next_row, row, column, scale);
            b.push(0.0);
            *next_row += 1;
        }
    }
    cones.push(Cone::PsdTriangle(side));
}

#[derive(Clone, Debug, Serialize)]
pub struct RateCrossingDiagnostic {
    pub xi_cell: usize,
    pub rate_interface: usize,
    pub rate: String,
    pub upward: bool,
    pub segment: usize,
    pub fraction: f64,
    pub time: f64,
    pub local_xi: f64,
    pub moments: Vec<f64>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CostRateSplitWitnessDiagnostic {
    pub schema: &'static str,
    pub order: u8,
    pub knots: Vec<String>,
    pub rate_knots: Vec<String>,
    pub segment_count: usize,
    pub duration: f64,
    pub trajectory_objective: f64,
    pub terminal_normalized_cost: f64,
    pub terminal_xi_cell: usize,
    pub occupation_moment_basis: Vec<CostMonomial>,
    pub xi_interface_moment_basis: Vec<CostMonomial>,
    pub rate_interface_moment_basis: Vec<CostMonomial>,
    pub xi_interface_rate_cells: Vec<usize>,
    pub rate_crossings: Vec<RateCrossingDiagnostic>,
    pub upward_crossing_count: usize,
    pub downward_crossing_count: usize,
    pub maximum_discarded_reflection_imaginary_part: f64,
    pub maximum_liouville_residual: f64,
    pub maximum_rate_ideal_residual: f64,
    pub normalization_residual: f64,
}

#[derive(Clone, Copy)]
struct Breakpoint {
    fraction: f64,
    event: BreakpointEvent,
}

#[derive(Clone, Copy)]
enum BreakpointEvent {
    Xi(usize),
    Rate { interface: usize, upward: bool },
}

pub fn diagnose_ideal_blockade_pulse(
    order: u8,
    xi_grid: &SplitGrid,
    rate_grid: &RateGrid,
    pulse: &IdealBlockadePulse,
) -> Result<CostRateSplitWitnessDiagnostic, String> {
    if rate_grid.is_degenerate() {
        let baseline =
            stationary_hausdorff_split::diagnose_ideal_blockade_pulse(order, xi_grid, pulse)?;
        return Ok(CostRateSplitWitnessDiagnostic {
            schema: "minexposure/stationary-torus-cost-rate-split-witness-v1",
            order,
            knots: baseline.knots,
            rate_knots: rate_grid.canonical_knots(),
            segment_count: baseline.segment_count,
            duration: baseline.duration,
            trajectory_objective: baseline.trajectory_objective,
            terminal_normalized_cost: baseline.terminal_normalized_cost,
            terminal_xi_cell: baseline.terminal_cell,
            occupation_moment_basis: baseline.occupation_moment_basis,
            xi_interface_moment_basis: baseline.interface_moment_basis,
            rate_interface_moment_basis: Vec::new(),
            xi_interface_rate_cells: Vec::new(),
            rate_crossings: Vec::new(),
            upward_crossing_count: 0,
            downward_crossing_count: 0,
            maximum_discarded_reflection_imaginary_part: baseline
                .maximum_discarded_reflection_imaginary_part,
            maximum_liouville_residual: baseline.maximum_liouville_residual,
            maximum_rate_ideal_residual: 0.0,
            normalization_residual: baseline.normalization_residual,
        });
    }
    if pulse.phases.is_empty() || !pulse.duration.is_finite() || pulse.duration <= 0.0 {
        return Err("invalid ideal-blockade pulse".into());
    }
    let model = RateSplitModel::create(order, xi_grid, rate_grid)?;
    let occupation_count = model.base.moments().keys.len();
    let xi_interface_count = model.xi_interfaces.keys.len();
    let rate_interface_count = model.rate_interfaces[0].keys.len();
    let mut occupation = vec![vec![0.0; occupation_count]; model.xi_cells * model.rate_cells];
    let mut xi_interfaces = vec![vec![0.0; xi_interface_count]; model.xi_interface_offsets.len()];
    let mut rate_interfaces =
        vec![vec![0.0; rate_interface_count]; model.rate_interface_offsets.len()];
    let mut xi_interface_rate_cells = vec![usize::MAX; model.xi_cells.saturating_sub(1)];
    let mut crossings = Vec::new();
    let mut maximum_discarded = 0.0_f64;
    let mut maximum_rate_ideal_residual = 0.0_f64;
    let quadrature = gauss_legendre(32);
    let segment_duration = pulse.duration / pulse.phases.len() as f64;
    let exposure_upper = rational_f64(EXPOSURE_UPPER);
    let xi_knots = xi_grid
        .knots()
        .iter()
        .map(|&value| rational_f64(value))
        .collect::<Vec<_>>();
    let rate_knots = rate_grid
        .knots()
        .iter()
        .map(|&value| rational_f64(value))
        .collect::<Vec<_>>();
    let xi_targets = xi_knots[1..xi_knots.len() - 1]
        .iter()
        .map(|value| exposure_upper * value)
        .collect::<Vec<_>>();
    let mut next_xi_interface = 0;
    let mut state = initial_state();
    let mut cumulative_exposure = 0.0;

    for (segment, &phase) in pulse.phases.iter().enumerate() {
        let segment_start_state = state;
        let segment_exposure =
            segment_cost_integral(&segment_start_state, phase, segment_duration, 1.0);
        let segment_end_exposure = cumulative_exposure + segment_exposure;
        let mut breakpoints = Vec::new();
        while next_xi_interface < xi_targets.len()
            && xi_targets[next_xi_interface] <= segment_end_exposure + 2e-14
        {
            let target = xi_targets[next_xi_interface];
            let fraction = crossing_fraction(
                &segment_start_state,
                phase,
                segment_duration,
                target - cumulative_exposure,
            );
            breakpoints.push(Breakpoint {
                fraction,
                event: BreakpointEvent::Xi(next_xi_interface),
            });
            next_xi_interface += 1;
        }
        for (interface, &rate) in rate_knots[1..rate_knots.len() - 1].iter().enumerate() {
            for (fraction, upward) in
                rate_crossing_fractions(&segment_start_state, phase, segment_duration, rate)
            {
                breakpoints.push(Breakpoint {
                    fraction,
                    event: BreakpointEvent::Rate { interface, upward },
                });
            }
        }
        breakpoints.sort_by(|left, right| left.fraction.total_cmp(&right.fraction));

        let mut lower = 0.0;
        for breakpoint in &breakpoints {
            integrate_rate_piece(
                &mut occupation,
                model.base.moments(),
                xi_grid,
                rate_grid,
                cumulative_exposure,
                &segment_start_state,
                phase,
                segment_duration,
                lower,
                breakpoint.fraction,
                &quadrature,
                &mut maximum_discarded,
            );
            let point = trajectory_point(
                &segment_start_state,
                phase,
                segment_duration,
                breakpoint.fraction,
            );
            let state_point = [point[1], point[2], point[3], point[4]];
            let exposure = cumulative_exposure
                + segment_cost_integral(
                    &segment_start_state,
                    phase,
                    segment_duration,
                    breakpoint.fraction,
                );
            let normalized_cost = exposure / exposure_upper;
            match breakpoint.event {
                BreakpointEvent::Xi(interface) => {
                    let rate_cell = containing_cell(running_cost(&point), &rate_knots)?;
                    let values = moment_values(
                        &model.xi_interfaces.keys,
                        &state_point,
                        0.0,
                        STATE_VARIABLES,
                        &mut maximum_discarded,
                    );
                    xi_interfaces[interface * model.rate_cells + rate_cell]
                        .copy_from_slice(&values);
                    xi_interface_rate_cells[interface] = rate_cell + 1;
                }
                BreakpointEvent::Rate { interface, upward } => {
                    let xi_cell = containing_cell(normalized_cost, &xi_knots)?;
                    let local_xi = (normalized_cost - xi_knots[xi_cell])
                        / (xi_knots[xi_cell + 1] - xi_knots[xi_cell]);
                    let values = moment_values(
                        &model.rate_interfaces[interface].keys,
                        &state_point,
                        local_xi,
                        STATE_VARIABLES,
                        &mut maximum_discarded,
                    );
                    maximum_rate_ideal_residual = maximum_rate_ideal_residual
                        .max((running_cost(&point) - rate_knots[interface + 1]).abs());
                    let offset = xi_cell * (model.rate_cells - 1) + interface;
                    let direction = if upward { 1.0 } else { -1.0 };
                    for (moment, value) in rate_interfaces[offset].iter_mut().zip(&values) {
                        *moment += direction * value;
                    }
                    crossings.push(RateCrossingDiagnostic {
                        xi_cell: xi_cell + 1,
                        rate_interface: interface + 1,
                        rate: rate_grid.knots()[interface + 1].to_string(),
                        upward,
                        segment,
                        fraction: breakpoint.fraction,
                        time: (segment as f64 + breakpoint.fraction) * segment_duration,
                        local_xi,
                        moments: values,
                    });
                }
            }
            lower = breakpoint.fraction;
        }
        integrate_rate_piece(
            &mut occupation,
            model.base.moments(),
            xi_grid,
            rate_grid,
            cumulative_exposure,
            &segment_start_state,
            phase,
            segment_duration,
            lower,
            1.0,
            &quadrature,
            &mut maximum_discarded,
        );
        let endpoint = trajectory_point(&segment_start_state, phase, segment_duration, 1.0);
        state.copy_from_slice(&endpoint[1..]);
        cumulative_exposure = segment_end_exposure;
    }

    if next_xi_interface != xi_targets.len() {
        return Err(format!(
            "witness crossed {next_xi_interface} xi interfaces, expected {}",
            xi_targets.len()
        ));
    }
    let terminal_normalized_cost = cumulative_exposure / exposure_upper;
    if terminal_normalized_cost >= 1.0 {
        return Err(format!(
            "witness terminal normalized cost {terminal_normalized_cost:.16} is not below 1"
        ));
    }
    let terminal_xi_cell = containing_cell(terminal_normalized_cost, &xi_knots)?;
    let terminal_xi = (terminal_normalized_cost - xi_knots[terminal_xi_cell])
        / (xi_knots[terminal_xi_cell + 1] - xi_knots[terminal_xi_cell]);
    let mut terminal = vec![vec![0.0; model.terminal_count]; model.xi_cells];
    let mut power = 1.0;
    for moment in &mut terminal[terminal_xi_cell] {
        *moment = power;
        power *= terminal_xi;
    }

    let mut variables = vec![0.0; model.coefficient_count];
    for (offset, moments) in model.occupation_offsets.iter().zip(&occupation) {
        variables[*offset..*offset + occupation_count].copy_from_slice(moments);
    }
    for (offset, moments) in model.xi_interface_offsets.iter().zip(&xi_interfaces) {
        variables[*offset..*offset + xi_interface_count].copy_from_slice(moments);
    }
    for (offset, moments) in model.rate_interface_offsets.iter().zip(&rate_interfaces) {
        variables[*offset..*offset + rate_interface_count].copy_from_slice(moments);
    }
    for (offset, moments) in model.terminal_offsets.iter().zip(&terminal) {
        variables[*offset..*offset + model.terminal_count].copy_from_slice(moments);
    }

    let maximum_liouville_residual = model
        .rows
        .iter()
        .map(|row| {
            let lhs = row
                .coefficients
                .iter()
                .map(|&(position, coefficient)| coefficient.to_f64() * variables[position])
                .sum::<f64>();
            (lhs - row.rhs as f64).abs()
        })
        .fold(0.0, f64::max);
    let trajectory_objective = model
        .occupation_offsets
        .iter()
        .map(|&offset| {
            model
                .base
                .cost
                .iter()
                .map(|&(position, coefficient)| coefficient.to_f64() * variables[offset + position])
                .sum::<f64>()
        })
        .sum();
    let normalization_residual =
        (terminal.iter().map(|moments| moments[0]).sum::<f64>() - 1.0).abs();
    let upward_crossing_count = crossings.iter().filter(|crossing| crossing.upward).count();
    let downward_crossing_count = crossings.len() - upward_crossing_count;
    Ok(CostRateSplitWitnessDiagnostic {
        schema: "minexposure/stationary-torus-cost-rate-split-witness-v1",
        order,
        knots: xi_grid.canonical_knots(),
        rate_knots: rate_grid.canonical_knots(),
        segment_count: pulse.phases.len(),
        duration: pulse.duration,
        trajectory_objective,
        terminal_normalized_cost,
        terminal_xi_cell: terminal_xi_cell + 1,
        occupation_moment_basis: model.base.moments().keys.clone(),
        xi_interface_moment_basis: model.xi_interfaces.keys.clone(),
        rate_interface_moment_basis: model.rate_interfaces[0].keys.clone(),
        xi_interface_rate_cells,
        rate_crossings: crossings,
        upward_crossing_count,
        downward_crossing_count,
        maximum_discarded_reflection_imaginary_part: maximum_discarded,
        maximum_liouville_residual,
        maximum_rate_ideal_residual,
        normalization_residual,
    })
}

#[allow(clippy::too_many_arguments)]
fn integrate_rate_piece(
    occupation: &mut [Vec<f64>],
    moments: &MomentSpace,
    xi_grid: &SplitGrid,
    rate_grid: &RateGrid,
    segment_start_exposure: f64,
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    lower_fraction: f64,
    upper_fraction: f64,
    quadrature: &[(f64, f64)],
    maximum_discarded: &mut f64,
) {
    if upper_fraction <= lower_fraction + 2e-16 {
        return;
    }
    let exposure_upper = rational_f64(EXPOSURE_UPPER);
    let xi_knots = xi_grid
        .knots()
        .iter()
        .map(|&value| rational_f64(value))
        .collect::<Vec<_>>();
    let rate_knots = rate_grid
        .knots()
        .iter()
        .map(|&value| rational_f64(value))
        .collect::<Vec<_>>();
    let midpoint = (lower_fraction + upper_fraction) / 2.0;
    let midpoint_point = trajectory_point(state, phase, segment_duration, midpoint);
    let midpoint_exposure =
        segment_start_exposure + segment_cost_integral(state, phase, segment_duration, midpoint);
    let xi_cell = containing_cell(midpoint_exposure / exposure_upper, &xi_knots)
        .expect("breakpoints partition the xi grid");
    let rate_cell = containing_cell(running_cost(&midpoint_point), &rate_knots)
        .expect("breakpoints partition the rate grid");
    let lower_xi = xi_knots[xi_cell];
    let xi_width = xi_knots[xi_cell + 1] - lower_xi;
    let target = &mut occupation[xi_cell * rate_grid.cell_count() + rate_cell];
    for &(node, weight) in quadrature {
        let fraction = lower_fraction + (upper_fraction - lower_fraction) * node;
        let point = trajectory_point(state, phase, segment_duration, fraction);
        let exposure = segment_start_exposure
            + segment_cost_integral(state, phase, segment_duration, fraction);
        let xi = (exposure / exposure_upper - lower_xi) / xi_width;
        let values = moment_values(&moments.keys, &point, xi, BULK_VARIABLES, maximum_discarded);
        let scale = segment_duration * (upper_fraction - lower_fraction) * weight;
        for (moment, value) in target.iter_mut().zip(values) {
            *moment += scale * value;
        }
    }
}

fn containing_cell(value: f64, knots: &[f64]) -> Result<usize, String> {
    knots
        .windows(2)
        .position(|pair| value >= pair[0] - 2e-13 && value <= pair[1] + 2e-13)
        .ok_or_else(|| {
            format!(
                "value {value:.16e} is outside [{:.16e},{:.16e}]",
                knots[0],
                knots[knots.len() - 1]
            )
        })
}

fn rate_crossing_fractions(
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    target: f64,
) -> Vec<(f64, bool)> {
    let samples = (segment_duration.abs() * 64.0).ceil() as usize + 64;
    let value = |fraction: f64| {
        running_cost(&trajectory_point(state, phase, segment_duration, fraction)) - target
    };
    let mut result = Vec::new();
    let mut left_fraction = 0.0;
    let mut left_value = value(0.0);
    for sample in 1..=samples {
        let right_fraction = sample as f64 / samples as f64;
        let right_value = value(right_fraction);
        if left_value * right_value < 0.0 {
            let upward = left_value < right_value;
            let mut lower = left_fraction;
            let mut upper = right_fraction;
            for _ in 0..70 {
                let middle = (lower + upper) / 2.0;
                if (value(middle) < 0.0) == (left_value < 0.0) {
                    lower = middle;
                } else {
                    upper = middle;
                }
            }
            let root = (lower + upper) / 2.0;
            if root > 2e-14 && result.last().is_none_or(|(last, _)| root - last > 1e-12) {
                result.push((root, upward));
            }
        }
        left_fraction = right_fraction;
        left_value = right_value;
    }
    result
}

fn crossing_fraction(
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    target_exposure: f64,
) -> f64 {
    let mut lower = 0.0;
    let mut upper = 1.0;
    for _ in 0..80 {
        let middle = (lower + upper) / 2.0;
        if segment_cost_integral(state, phase, segment_duration, middle) < target_exposure {
            lower = middle;
        } else {
            upper = middle;
        }
    }
    (lower + upper) / 2.0
}

fn moment_values<const N: usize>(
    basis: &[CostMonomial],
    z: &[Complex64; N],
    xi: f64,
    variables: usize,
    maximum_discarded: &mut f64,
) -> Vec<f64> {
    basis
        .iter()
        .map(|key| {
            let mut value = Complex64::new(xi.powi(i32::from(key.cost_power)), 0.0);
            for (variable, (&anti, &holo)) in key.anti.0.iter().zip(&key.holo.0).enumerate() {
                value *= z[variable].conj().powu(u32::from(anti));
                value *= z[variable].powu(u32::from(holo));
            }
            if reflection_phase_is_i(key, variables) {
                value *= Complex64::new(0.0, -1.0);
            }
            *maximum_discarded = maximum_discarded.max(value.im.abs());
            value.re
        })
        .collect()
}

fn initial_state() -> [Complex64; STATE_VARIABLES] {
    [
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(1.0, 0.0),
        Complex64::new(0.0, 0.0),
    ]
}

fn trajectory_point(
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    fraction: f64,
) -> [Complex64; BULK_VARIABLES] {
    let time = fraction * segment_duration;
    let u = Complex64::from_polar(1.0, phase);
    let minus_i = Complex64::new(0.0, -1.0);
    let evolve = |ground: Complex64, rydberg: Complex64, rate: f64| {
        let (sine, cosine) = (rate * time).sin_cos();
        (
            ground * cosine + minus_i * u * rydberg * sine,
            rydberg * cosine + minus_i * u.conj() * ground * sine,
        )
    };
    let (g1, r1) = evolve(state[0], state[1], 0.5);
    let (g2, r2) = evolve(state[2], state[3], 1.0 / 2.0_f64.sqrt());
    [u, g1, r1, g2, r2]
}

fn running_cost(point: &[Complex64; BULK_VARIABLES]) -> f64 {
    0.5 * point[2].norm_sqr() + 0.25 * point[4].norm_sqr()
}

fn segment_cost_integral(
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    fraction: f64,
) -> f64 {
    let time = fraction * segment_duration;
    let u = Complex64::from_polar(1.0, phase);
    0.5 * population_integral(state[0], state[1], u, 0.5, time)
        + 0.25 * population_integral(state[2], state[3], u, 1.0 / 2.0_f64.sqrt(), time)
}

fn population_integral(
    ground: Complex64,
    rydberg: Complex64,
    u: Complex64,
    rate: f64,
    time: f64,
) -> f64 {
    let coupled_ground = Complex64::new(0.0, -1.0) * u.conj() * ground;
    let angle = rate * time;
    let cosine_square = time / 2.0 + (2.0 * angle).sin() / (4.0 * rate);
    let sine_square = time / 2.0 - (2.0 * angle).sin() / (4.0 * rate);
    let cosine_sine = angle.sin().powi(2) / (2.0 * rate);
    rydberg.norm_sqr() * cosine_square
        + coupled_ground.norm_sqr() * sine_square
        + 2.0 * (rydberg.conj() * coupled_ground).re * cosine_sine
}

fn gauss_legendre(count: usize) -> Vec<(f64, f64)> {
    let mut result = vec![(0.0, 0.0); count];
    for index in 0..count.div_ceil(2) {
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

fn rational_f64(value: Rational) -> f64 {
    value.numerator as f64 / value.denominator as f64
}

fn hash_json(value: &impl Serialize) -> String {
    format!(
        "sha256:{:x}",
        Sha256::digest(serde_json::to_vec(value).expect("hash input serializes"))
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pulse() -> IdealBlockadePulse {
        serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap()
    }

    #[test]
    fn validates_exact_rate_grid_and_true_state_range() {
        let grid = "0,2/32,0.125,3/4".parse::<RateGrid>().unwrap();
        assert_eq!(grid.to_string(), "0,1/16,1/8,3/4");
        assert_eq!(grid.cell_count(), 3);
        for invalid in ["", "0", "0,1", "0,1/2", "0,1/2,1/2,3/4"] {
            assert!(invalid.parse::<RateGrid>().is_err(), "{invalid}");
        }
        assert_eq!(MAXIMUM_RATE, Rational::new(1, 2) + Rational::new(1, 4));
    }

    #[test]
    fn degenerate_rate_grid_is_byte_identical_to_baseline_conic() {
        let xi_grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        let rate_grid = "0,3/4".parse::<RateGrid>().unwrap();
        let baseline = stationary_hausdorff_split::assemble(4, &xi_grid).unwrap();
        let split = assemble(4, &xi_grid, &rate_grid).unwrap();
        assert_eq!(split.conic, baseline.conic);
        assert_eq!(
            split.structure.formulation_hash,
            baseline.structure.formulation_hash
        );
        assert!(split.structure.degenerate_baseline);
    }

    #[test]
    fn two_axis_structure_has_both_rate_directions_and_localizers() {
        let xi_grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let rate_grid = "0,1/8,3/4".parse::<RateGrid>().unwrap();
        let structure = structure(3, &xi_grid, &rate_grid).unwrap();
        assert_eq!(structure.xi_cell_count, 2);
        assert_eq!(structure.rate_cell_count, 2);
        assert_eq!(structure.xi_interface_measure_count, 2);
        assert_eq!(structure.rate_interface_measure_count, 2);
        assert_eq!(structure.rate_interface_directional_measure_count, 4);
        assert!(structure.occupation_rate_localizer_block_count_per_cell > 0);
        assert!(structure.xi_interface_rate_localizer_block_count_per_measure > 0);
        assert_eq!(structure.rate_interface_moment_block_count_per_measure, 0);
        assert_eq!(structure.rate_interface_interval_block_count_per_measure, 0);
        assert_eq!(structure.rate_ideal_equality_count, 0);
    }

    #[test]
    fn rate_interface_signs_match_upward_and_downward_cell_balance() {
        let xi_grid = "0,1".parse::<SplitGrid>().unwrap();
        let rate_grid = "0,1/8,3/4".parse::<RateGrid>().unwrap();
        let model = RateSplitModel::create(2, &xi_grid, &rate_grid).unwrap();
        let test = &liouville_tests(2)[0];
        let lower = &model.rows[0];
        let upper = &model.rows[liouville_tests(2).len()];
        for (position, coefficient) in model.rate_interfaces[0].coefficients(test) {
            let signed = model.rate_interface_offset(0, 0) + position;
            assert!(lower.coefficients.contains(&(signed, -coefficient)));
            assert!(upper.coefficients.contains(&(signed, coefficient)));
        }
    }

    #[test]
    fn witness_satisfies_two_axis_liouville_and_interface_ideal() {
        let xi_grid = "0,1/36,1/3,2/3,35/36,1".parse::<SplitGrid>().unwrap();
        let rate_grid = "0,1/16,3/4".parse::<RateGrid>().unwrap();
        let report = diagnose_ideal_blockade_pulse(4, &xi_grid, &rate_grid, &pulse()).unwrap();
        assert!((report.trajectory_objective - 2.935_885_902_112_58).abs() < 1e-12);
        assert!(report.upward_crossing_count > 0);
        assert!(report.downward_crossing_count > 0);
        assert!(
            report.maximum_liouville_residual < 1e-12,
            "{}",
            report.maximum_liouville_residual
        );
        assert!(
            report.maximum_rate_ideal_residual < 1e-12,
            "{}",
            report.maximum_rate_ideal_residual
        );
        assert_eq!(report.normalization_residual, 0.0);
    }
}
