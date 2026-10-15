//! Piecewise normalized cumulative-cost lift of the JAN22 stationary torus.
//!
//! Each exact rational cost cell has its own local coordinate `xi` and
//! occupation/terminal measures. Nonnegative state-only interface moment
//! measures carry the one-way crossing flux between adjacent cells.

use crate::algebra::{Qsqrt2, Rational};
use crate::conic::{Cone, ConicProblem, SparseMatrix};
use crate::estimate::Estimate;
use crate::model::{ModelId, RelaxationOrder};
use crate::stationary_hausdorff::{
    AnisotropicOccupationModel, ChargeEnrichment, CostMonomial, EXPOSURE_UPPER,
    ExactCertificateModel, MomentSpace, active_time_capped_certificate_model,
    anisotropic_liouville_tests, boundary_moment_position, control_enriched_certificate_model,
    enriched_certificate_model, exact_certificate_model, initial_value, interface_gram_bases,
    interface_gram_entry_coefficients, liouville_tests, reflection_phase_is_i,
    rydberg_localized_certificate_model, scaled_liouville_coefficients, target_value,
};
use crate::stationary_torus::{IdealBlockadePulse, PackedPsdBlock, StationarySolutionDump};
use nalgebra::DMatrix;
use nalgebra::linalg::SymmetricEigen;
use num_complex::Complex64;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt;
use std::str::FromStr;

const BULK_VARIABLES: usize = 5;
const STATE_VARIABLES: usize = 4;
pub const ACTIVE_TIME_CAPPED_BOUND_SCOPE: &str = "active-time-capped, NOT all-duration";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SplitGrid {
    knots: Vec<Rational>,
}

impl SplitGrid {
    pub fn new(knots: Vec<Rational>) -> Result<Self, String> {
        if knots.len() < 2 {
            return Err("split grid requires at least the endpoint knots 0,1".into());
        }
        if knots[0] != Rational::ZERO || knots[knots.len() - 1] != Rational::ONE {
            return Err("split grid endpoints must be exactly 0 and 1".into());
        }
        for (index, pair) in knots.windows(2).enumerate() {
            let width = checked_difference(pair[1], pair[0]).map_err(|error| {
                format!("could not validate split grid cell {}: {error}", index + 1)
            })?;
            if width.numerator <= 0 {
                return Err(format!(
                    "split grid knots must be strictly increasing (positions {index} and {})",
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
            "schema": "minexposure/split-grid-v1",
            "knots": self.canonical_knots(),
        }))
    }

    pub(crate) fn inverse_widths(&self) -> Result<Vec<Rational>, String> {
        self.knots
            .windows(2)
            .enumerate()
            .map(|(index, pair)| {
                let width = checked_difference(pair[1], pair[0]).map_err(|error| {
                    format!("could not compute split grid cell {}: {error}", index + 1)
                })?;
                Ok(Rational::new(width.denominator, width.numerator))
            })
            .collect()
    }
}

impl FromStr for SplitGrid {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value.trim().is_empty() {
            return Err("split grid cannot be empty".into());
        }
        let knots = value
            .split(',')
            .enumerate()
            .map(|(index, knot)| {
                let knot = knot.trim();
                if knot.is_empty() {
                    return Err(format!("split grid knot {} is empty", index + 1));
                }
                knot.parse::<Rational>()
                    .map_err(|error| format!("invalid split grid knot {}: {error}", index + 1))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(knots)
    }
}

impl fmt::Display for SplitGrid {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.canonical_knots().join(","))
    }
}

fn checked_difference(upper: Rational, lower: Rational) -> Result<Rational, String> {
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
pub enum BlockFamily {
    Occupation,
    InterfaceMoment,
    TerminalMoment,
    TerminalInterval,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct StationaryHausdorffSplitStructure {
    pub order: u8,
    pub maximum_moment_degree: u8,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub enrichment: Option<ChargeEnrichment>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub u_degree: Option<u8>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub rydberg_localizer_charges: Vec<(i32, i32)>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub active_time_cap: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bound_scope: Option<&'static str>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub active_time_cap_row_scaling: Option<&'static str>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub occupation_variable_scale: Option<String>,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub cell_count: usize,
    pub occupation_moment_count_per_cell: usize,
    pub occupation_moment_count: usize,
    pub interface_moment_count_per_interface: usize,
    pub interface_moment_count: usize,
    pub terminal_moment_count_per_cell: usize,
    pub terminal_moment_count: usize,
    pub liouville_equality_count_per_cell: usize,
    pub liouville_equality_count: usize,
    pub normalization_equality_count: usize,
    pub occupation_moment_block_count_per_cell: usize,
    pub occupation_interval_block_count_per_cell: usize,
    pub occupation_interval_diagonal_count_per_cell: usize,
    pub interface_moment_block_count_per_interface: usize,
    pub terminal_block_sides_per_cell: [usize; 2],
    pub psd_block_families: Vec<BlockFamily>,
    pub psd_block_sides: Vec<usize>,
    pub largest_psd_side: usize,
    pub sum_psd_squares: usize,
    pub sum_psd_cubes: usize,
    pub occupation_basis_hash: String,
    pub interface_basis_hash: String,
    pub terminal_basis_hash: String,
    pub liouville_basis_hash: String,
    pub formulation_hash: String,
    pub exposure_upper: Rational,
    pub source_thread: &'static str,
}

#[derive(Clone, Debug)]
pub struct StationaryHausdorffSplitProblem {
    pub structure: StationaryHausdorffSplitStructure,
    pub conic: ConicProblem,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct StationaryHausdorffAnisotropicSplitStructure {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema: Option<&'static str>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rigor: Option<&'static str>,
    pub order: u8,
    pub xi_degree: u8,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub enrichment: Option<ChargeEnrichment>,
    pub maximum_state_moment_degree: u16,
    pub maximum_xi_moment_degree: u16,
    pub anisotropic_basis: &'static str,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub cell_count: usize,
    pub occupation_moment_count_per_cell: usize,
    pub occupation_moment_count: usize,
    pub interface_moment_count_per_interface: usize,
    pub interface_moment_count: usize,
    pub terminal_moment_count_per_cell: usize,
    pub terminal_moment_count: usize,
    pub liouville_equality_count_per_cell: usize,
    pub liouville_equality_count: usize,
    pub normalization_equality_count: usize,
    pub occupation_moment_block_count_per_cell: usize,
    pub occupation_interval_block_count_per_cell: usize,
    pub occupation_interval_diagonal_count_per_cell: usize,
    pub interface_moment_block_count_per_interface: usize,
    pub terminal_block_sides_per_cell: [usize; 2],
    pub psd_block_families: Vec<BlockFamily>,
    pub psd_block_sides: Vec<usize>,
    pub largest_psd_side: usize,
    pub sum_psd_squares: usize,
    pub sum_psd_cubes: usize,
    pub occupation_basis_hash: String,
    pub interface_basis_hash: String,
    pub terminal_basis_hash: String,
    pub liouville_basis_hash: String,
    pub formulation_hash: String,
    pub exposure_upper: Rational,
    pub source_thread: &'static str,
}

#[derive(Clone, Debug)]
pub struct StationaryHausdorffAnisotropicSplitProblem {
    pub structure: StationaryHausdorffAnisotropicSplitStructure,
    pub conic: ConicProblem,
}

#[derive(Clone, Debug)]
pub(crate) struct ExactSplitRow {
    pub(crate) cell: usize,
    pub(crate) coefficients: Vec<(usize, Qsqrt2)>,
    pub(crate) rhs: i64,
}

#[derive(Clone, Debug)]
pub(crate) struct ExactSplitModel {
    base: ExactCertificateModel,
    interfaces: MomentSpace,
    interface_bases: Vec<Vec<CostMonomial>>,
    pub(crate) rows: Vec<ExactSplitRow>,
    cell_offsets: Vec<usize>,
    interface_offsets: Vec<usize>,
    terminal_offsets: Vec<usize>,
    terminal_count: usize,
    coefficient_count: usize,
}

impl ExactSplitModel {
    pub(crate) fn create(order: u8, grid: &SplitGrid) -> Result<Self, String> {
        Self::create_with_enrichment(order, grid, None)
    }

    fn create_with_enrichment(
        order: u8,
        grid: &SplitGrid,
        enrichment: Option<&ChargeEnrichment>,
    ) -> Result<Self, String> {
        Self::create_with_options(order, grid, enrichment, false)
    }

    fn create_active_time_capped(order: u8, grid: &SplitGrid) -> Result<Self, String> {
        Self::create_with_options(order, grid, None, true)
    }

    fn create_with_options(
        order: u8,
        grid: &SplitGrid,
        enrichment: Option<&ChargeEnrichment>,
        active_time_capped: bool,
    ) -> Result<Self, String> {
        let base = match (enrichment, active_time_capped) {
            (None, true) => active_time_capped_certificate_model(order)?,
            (Some(enrichment), false) => enriched_certificate_model(order, enrichment)?,
            (None, false) => exact_certificate_model(order)?,
            (Some(_), true) => unreachable!("active-time cap and enrichment are not composed"),
        };
        Self::create_with_base(order, grid, base)
    }

    fn create_with_u_degree(order: u8, u_degree: u8, grid: &SplitGrid) -> Result<Self, String> {
        Self::create_with_base(
            order,
            grid,
            control_enriched_certificate_model(order, u_degree)?,
        )
    }

    fn create_with_rydberg_localizers(
        order: u8,
        grid: &SplitGrid,
        charges: &[(i32, i32)],
    ) -> Result<Self, String> {
        Self::create_with_base(
            order,
            grid,
            rydberg_localized_certificate_model(order, charges)?,
        )
    }

    fn create_with_base(
        order: u8,
        grid: &SplitGrid,
        base: ExactCertificateModel,
    ) -> Result<Self, String> {
        let tests = liouville_tests(order);
        let interfaces = MomentSpace::interface(order);
        let interface_bases = interface_gram_bases(order);
        let inverse_widths = grid.inverse_widths()?;
        let cells = grid.cell_count();
        let occupation_count = base.moments().keys.len();
        let interface_count = interfaces.keys.len();
        let terminal_count = 2 * usize::from(order) + 1;

        let cell_offsets = (0..cells)
            .map(|cell| cell * occupation_count)
            .collect::<Vec<_>>();
        let interface_base = cells * occupation_count;
        let interface_offsets = (0..cells.saturating_sub(1))
            .map(|interface| interface_base + interface * interface_count)
            .collect::<Vec<_>>();
        let terminal_base = interface_base + interface_offsets.len() * interface_count;
        let terminal_offsets = (0..cells)
            .map(|cell| terminal_base + cell * terminal_count)
            .collect::<Vec<_>>();
        let coefficient_count = terminal_base + cells * terminal_count;

        let mut rows = Vec::with_capacity(cells * tests.len());
        for (cell, &inverse_width) in inverse_widths.iter().enumerate() {
            for test in &tests {
                let mut coefficients =
                    scaled_liouville_coefficients(test, inverse_width, base.moments())
                        .into_iter()
                        .map(|(position, coefficient)| (cell_offsets[cell] + position, coefficient))
                        .collect::<Vec<_>>();

                let boundary_position = boundary_moment_position(&interfaces, test);
                if cell != 0 && test.cost_power == 0 {
                    coefficients.push((
                        interface_offsets[cell - 1] + boundary_position,
                        Qsqrt2::from(1),
                    ));
                }
                if cell + 1 < cells {
                    coefficients.push((
                        interface_offsets[cell] + boundary_position,
                        Qsqrt2::from(-1),
                    ));
                }
                let target = target_value(test);
                if target != 0 {
                    coefficients.push((
                        terminal_offsets[cell] + usize::from(test.cost_power),
                        Qsqrt2::from(-target),
                    ));
                }
                rows.push(ExactSplitRow {
                    cell,
                    coefficients,
                    rhs: if cell == 0 { -initial_value(test) } else { 0 },
                });
            }
        }

        Ok(Self {
            base,
            interfaces,
            interface_bases,
            rows,
            cell_offsets,
            interface_offsets,
            terminal_offsets,
            terminal_count,
            coefficient_count,
        })
    }

    pub(crate) fn coefficient_count(&self) -> usize {
        self.coefficient_count
    }

    pub(crate) fn cell_count(&self) -> usize {
        self.cell_offsets.len()
    }

    pub(crate) fn equality_count_per_cell(&self) -> usize {
        self.rows.len() / self.cell_count()
    }

    pub(crate) fn occupation_gram_count_per_cell(&self) -> usize {
        self.base.occupation_gram_count()
    }

    pub(crate) fn interface_gram_count_per_interface(&self) -> usize {
        self.interface_bases.len()
    }

    pub(crate) fn gram_dimensions(&self) -> Vec<usize> {
        let occupation = self.base.occupation_gram_dimensions();
        let interfaces = self
            .interface_bases
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>();
        let terminal = [self.terminal_count().div_ceil(2), self.terminal_count() / 2];
        let mut dimensions = Vec::new();
        for _ in &self.cell_offsets {
            dimensions.extend(&occupation);
        }
        for _ in &self.interface_offsets {
            dimensions.extend(&interfaces);
        }
        for _ in &self.terminal_offsets {
            dimensions.extend(terminal);
        }
        dimensions
    }

    pub(crate) fn for_each_cost_coefficient(&self, mut visit: impl FnMut(usize, Qsqrt2)) {
        for &offset in &self.cell_offsets {
            for &(position, coefficient) in &self.base.cost {
                visit(offset + position, coefficient);
            }
        }
    }

    pub(crate) fn for_each_normalization_position(&self, mut visit: impl FnMut(usize)) {
        for &offset in &self.terminal_offsets {
            visit(offset);
        }
    }

    fn for_each_active_time_position(&self, mut visit: impl FnMut(usize)) {
        let mass_position = self
            .base
            .moments()
            .keys
            .iter()
            .position(|key| key.cost_power == 0 && key.anti.degree() == 0 && key.holo.degree() == 0)
            .expect("occupation moment basis contains the constant monomial");
        for &offset in &self.cell_offsets {
            visit(offset + mass_position);
        }
    }

    pub(crate) fn for_each_gram_entry_coefficient(
        &self,
        block: usize,
        row: usize,
        column: usize,
        mut visit: impl FnMut(usize, Qsqrt2),
    ) {
        let occupation_per_cell = self.occupation_gram_count_per_cell();
        let occupation_count = self.cell_count() * occupation_per_cell;
        if block < occupation_count {
            let cell = block / occupation_per_cell;
            let local_block = block % occupation_per_cell;
            self.base.for_each_gram_entry_coefficient(
                local_block,
                row,
                column,
                |position, coefficient| {
                    visit(self.cell_offsets[cell] + position, coefficient);
                },
            );
            return;
        }

        let block = block - occupation_count;
        let interface_per_knot = self.interface_gram_count_per_interface();
        let interface_count = self.interface_offsets.len() * interface_per_knot;
        if block < interface_count {
            let interface = block / interface_per_knot;
            let local_block = block % interface_per_knot;
            for (position, coefficient) in interface_gram_entry_coefficients(
                &self.interfaces,
                &self.interface_bases[local_block][row],
                &self.interface_bases[local_block][column],
            ) {
                visit(self.interface_offsets[interface] + position, coefficient);
            }
            return;
        }

        let block = block - interface_count;
        let cell = block / 2;
        let family = block % 2;
        let offset = self.terminal_offsets[cell] + row + column;
        if family == 0 {
            visit(offset, Qsqrt2::from(1));
        } else {
            visit(offset + 1, Qsqrt2::from(1));
            visit(offset + 2, Qsqrt2::from(-1));
        }
    }

    fn terminal_count(&self) -> usize {
        self.terminal_count
    }
}

#[derive(Clone, Debug)]
struct AnisotropicSplitModel {
    base: AnisotropicOccupationModel,
    interfaces: MomentSpace,
    interface_bases: Vec<Vec<CostMonomial>>,
    rows: Vec<ExactSplitRow>,
    cell_offsets: Vec<usize>,
    interface_offsets: Vec<usize>,
    terminal_offsets: Vec<usize>,
    terminal_count: usize,
    coefficient_count: usize,
}

impl AnisotropicSplitModel {
    fn create(order: u8, xi_degree: u8, grid: &SplitGrid) -> Result<Self, String> {
        Self::create_with_enrichment(order, xi_degree, grid, None)
    }

    fn create_with_enrichment(
        order: u8,
        xi_degree: u8,
        grid: &SplitGrid,
        enrichment: Option<&ChargeEnrichment>,
    ) -> Result<Self, String> {
        let base =
            AnisotropicOccupationModel::create_with_enrichment(order, xi_degree, enrichment)?;
        let tests = anisotropic_liouville_tests(order, xi_degree)?;
        let interfaces = MomentSpace::interface(order);
        let interface_bases = interface_gram_bases(order);
        let inverse_widths = grid.inverse_widths()?;
        let cells = grid.cell_count();
        let occupation_count = base.moments().keys.len();
        let interface_count = interfaces.keys.len();
        let terminal_count = 2 * usize::from(xi_degree) + 1;

        let cell_offsets = (0..cells)
            .map(|cell| cell * occupation_count)
            .collect::<Vec<_>>();
        let interface_base = cells * occupation_count;
        let interface_offsets = (0..cells.saturating_sub(1))
            .map(|interface| interface_base + interface * interface_count)
            .collect::<Vec<_>>();
        let terminal_base = interface_base + interface_offsets.len() * interface_count;
        let terminal_offsets = (0..cells)
            .map(|cell| terminal_base + cell * terminal_count)
            .collect::<Vec<_>>();
        let coefficient_count = terminal_base + cells * terminal_count;

        let mut rows = Vec::with_capacity(cells * tests.len());
        for (cell, &inverse_width) in inverse_widths.iter().enumerate() {
            for test in &tests {
                let mut coefficients =
                    scaled_liouville_coefficients(test, inverse_width, base.moments())
                        .into_iter()
                        .map(|(position, coefficient)| (cell_offsets[cell] + position, coefficient))
                        .collect::<Vec<_>>();

                let boundary_position = boundary_moment_position(&interfaces, test);
                if cell != 0 && test.cost_power == 0 {
                    coefficients.push((
                        interface_offsets[cell - 1] + boundary_position,
                        Qsqrt2::from(1),
                    ));
                }
                if cell + 1 < cells {
                    coefficients.push((
                        interface_offsets[cell] + boundary_position,
                        Qsqrt2::from(-1),
                    ));
                }
                let target = target_value(test);
                if target != 0 {
                    coefficients.push((
                        terminal_offsets[cell] + usize::from(test.cost_power),
                        Qsqrt2::from(-target),
                    ));
                }
                rows.push(ExactSplitRow {
                    cell,
                    coefficients,
                    rhs: if cell == 0 { -initial_value(test) } else { 0 },
                });
            }
        }

        Ok(Self {
            base,
            interfaces,
            interface_bases,
            rows,
            cell_offsets,
            interface_offsets,
            terminal_offsets,
            terminal_count,
            coefficient_count,
        })
    }
}

pub fn structure(order: u8, grid: &SplitGrid) -> Result<StationaryHausdorffSplitStructure, String> {
    structure_with_options(order, grid, None, None, &[], None)
}

pub fn active_time_capped_structure(
    order: u8,
    grid: &SplitGrid,
    active_time_cap: Rational,
) -> Result<StationaryHausdorffSplitStructure, String> {
    validate_active_time_cap(active_time_cap)?;
    structure_with_options(order, grid, None, None, &[], Some(active_time_cap))
}

pub fn enriched_structure(
    order: u8,
    grid: &SplitGrid,
    enrichment: &ChargeEnrichment,
) -> Result<StationaryHausdorffSplitStructure, String> {
    structure_with_options(order, grid, Some(enrichment), None, &[], None)
}

pub fn u_anisotropic_structure(
    order: u8,
    u_degree: u8,
    grid: &SplitGrid,
) -> Result<StationaryHausdorffSplitStructure, String> {
    structure_with_options(order, grid, None, Some(u_degree), &[], None)
}

pub fn rydberg_localized_structure(
    order: u8,
    grid: &SplitGrid,
    charges: &[(i32, i32)],
) -> Result<StationaryHausdorffSplitStructure, String> {
    structure_with_options(order, grid, None, None, charges, None)
}

fn structure_with_options(
    order: u8,
    grid: &SplitGrid,
    enrichment: Option<&ChargeEnrichment>,
    u_degree: Option<u8>,
    rydberg_localizer_charges: &[(i32, i32)],
    active_time_cap: Option<Rational>,
) -> Result<StationaryHausdorffSplitStructure, String> {
    let occupation_variable_scale = active_time_cap.map(active_time_solver_scale);
    let exact = match (
        enrichment,
        u_degree,
        rydberg_localizer_charges.is_empty(),
        active_time_cap,
    ) {
        (Some(enrichment), None, true, None) => {
            ExactSplitModel::create_with_enrichment(order, grid, Some(enrichment))?
        }
        (None, Some(u_degree), true, None) => {
            ExactSplitModel::create_with_u_degree(order, u_degree, grid)?
        }
        (None, None, false, None) => {
            ExactSplitModel::create_with_rydberg_localizers(order, grid, rydberg_localizer_charges)?
        }
        (None, None, true, Some(_)) => ExactSplitModel::create_active_time_capped(order, grid)?,
        (None, None, true, None) => ExactSplitModel::create(order, grid)?,
        _ => {
            return Err(
                "exploratory split strengthenings must be tested one family at a time".into(),
            );
        }
    };
    let base = crate::stationary_hausdorff::structure(order)?;
    let cells = grid.cell_count();
    let interfaces = cells.saturating_sub(1);
    let occupation_counts = exact.base.occupation_block_counts();
    let occupation_sides = exact.base.occupation_gram_dimensions();
    let interface_sides = exact
        .interface_bases
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let terminal_sides = [usize::from(order) + 1, usize::from(order)];
    let mut psd_block_sides = Vec::new();
    let mut psd_block_families = Vec::new();
    for _ in 0..cells {
        psd_block_sides.extend(&occupation_sides);
        psd_block_families.extend(vec![BlockFamily::Occupation; occupation_sides.len()]);
    }
    for _ in 0..interfaces {
        psd_block_sides.extend(&interface_sides);
        psd_block_families.extend(vec![BlockFamily::InterfaceMoment; interface_sides.len()]);
    }
    for _ in 0..cells {
        psd_block_sides.extend(terminal_sides);
        psd_block_families.push(BlockFamily::TerminalMoment);
        psd_block_families.push(BlockFamily::TerminalInterval);
    }
    let knots = grid.canonical_knots();
    let split_grid_hash = grid.canonical_hash();
    let occupation_basis_hash = hash_json(&exact.base.moments().keys);
    let interface_basis_hash = hash_json(&exact.interfaces.keys);
    let formulation_hash = match (
        enrichment,
        u_degree,
        rydberg_localizer_charges.is_empty(),
        active_time_cap,
    ) {
        (None, None, true, None) => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-v1",
            "order": order,
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &base.terminal_basis_hash,
            "liouville_basis_hash": &base.liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "cell_support": "xi(1-xi)>=0",
            "interface_semantics": "nonnegative one-way state crossing flux",
            "source_thread": "T-01a05601-9ca5-72fc-81b8-a7bab8bdca1d",
        })),
        (Some(enrichment), None, true, None) => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-charge-enriched-v1",
            "order": order,
            "enrichment": enrichment,
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &base.terminal_basis_hash,
            "liouville_basis_hash": &base.liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "cell_support": "xi(1-xi)>=0",
            "interface_semantics": "nonnegative one-way state crossing flux",
            "enrichment_semantics": "baseline blocks retained; additional selected-sector higher-degree facial and xi(1-xi) extension directions only; baseline Liouville, interface, terminal, and exact-certificate schemas unchanged",
        })),
        (None, Some(u_degree), true, None) => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-u-anisotropic-exploratory-v1",
            "order": order,
            "u_degree": u_degree,
            "basis": "(local_xi_degree + state_degree)/order + control_degree/flag <= 1",
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &base.terminal_basis_hash,
            "liouville_basis_hash": &base.liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "semantics": "baseline Liouville, interface, and terminal constraints with a higher weighted control-harmonic degree in every occupation Gram sector",
        })),
        (None, None, false, None) => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-rydberg-product-localizers-exploratory-v1",
            "order": order,
            "rydberg_localizer_charges": rydberg_localizer_charges,
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &base.terminal_basis_hash,
            "liouville_basis_hash": &base.liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "semantics": "baseline cone plus selected-sector localizing Grams for |r1|^2 and |r2|^2",
        })),
        (None, None, true, Some(active_time_cap)) => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-active-time-capped-v1",
            "order": order,
            "active_time_cap": active_time_cap,
            "bound_scope": ACTIVE_TIME_CAPPED_BOUND_SCOPE,
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &base.terminal_basis_hash,
            "liouville_basis_hash": &base.liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "cell_support": "xi(1-xi)>=0",
            "interface_semantics": "nonnegative one-way state crossing flux",
            "active_time_cap_semantics": "sum_j mu_j[1] <= active_time_cap; full occupation moment cones replace the free-time zero-cost facial reduction",
            "active_time_cap_row_scaling": "sum_j mu_j[1]/active_time_cap <= 1",
            "occupation_variable_scale": occupation_variable_scale,
            "occupation_variable_scaling": "solver variables z_j[p]=mu_j[p]/occupation_variable_scale; diagnostic primal_variables are rescaled to physical mu_j[p]",
        })),
        _ => unreachable!("invalid strengthening combination rejected above"),
    };
    let extension_degree = enrichment.map_or(0, |value| value.extra_degree);
    let maximum_basis_degree = u_degree.unwrap_or(order).max(
        order
            .checked_add(extension_degree)
            .ok_or("maximum moment degree overflows u8")?,
    );
    let maximum_basis_degree = maximum_basis_degree
        .checked_add(u8::from(!rydberg_localizer_charges.is_empty()))
        .ok_or("maximum moment degree overflows u8")?;
    let maximum_moment_degree = maximum_basis_degree
        .checked_mul(2)
        .ok_or("maximum moment degree overflows u8")?;
    let occupation_moment_count = exact.base.moments().keys.len();
    let terminal_moment_count = exact.terminal_count();
    let liouville_equality_count = liouville_tests(order).len();
    Ok(StationaryHausdorffSplitStructure {
        order,
        maximum_moment_degree,
        enrichment: enrichment.cloned(),
        u_degree,
        rydberg_localizer_charges: rydberg_localizer_charges.to_vec(),
        active_time_cap: active_time_cap.map(|value| value.to_string()),
        bound_scope: active_time_cap.map(|_| ACTIVE_TIME_CAPPED_BOUND_SCOPE),
        active_time_cap_row_scaling: active_time_cap.map(|_| "sum_j mu_j[1]/active_time_cap <= 1"),
        occupation_variable_scale: occupation_variable_scale.map(|value| value.to_string()),
        knots,
        split_grid_hash,
        cell_count: cells,
        occupation_moment_count_per_cell: occupation_moment_count,
        occupation_moment_count: cells * occupation_moment_count,
        interface_moment_count_per_interface: exact.interfaces.keys.len(),
        interface_moment_count: interfaces * exact.interfaces.keys.len(),
        terminal_moment_count_per_cell: terminal_moment_count,
        terminal_moment_count: cells * terminal_moment_count,
        liouville_equality_count_per_cell: liouville_equality_count,
        liouville_equality_count: cells * liouville_equality_count,
        normalization_equality_count: 1,
        occupation_moment_block_count_per_cell: occupation_counts[0],
        occupation_interval_block_count_per_cell: occupation_counts[1],
        occupation_interval_diagonal_count_per_cell: occupation_counts[2],
        interface_moment_block_count_per_interface: interface_sides.len(),
        terminal_block_sides_per_cell: terminal_sides,
        largest_psd_side: psd_block_sides.iter().copied().max().unwrap_or(0),
        sum_psd_squares: psd_block_sides.iter().map(|side| side * side).sum(),
        sum_psd_cubes: psd_block_sides.iter().map(|side| side * side * side).sum(),
        psd_block_families,
        psd_block_sides,
        occupation_basis_hash,
        interface_basis_hash,
        terminal_basis_hash: base.terminal_basis_hash,
        liouville_basis_hash: base.liouville_basis_hash,
        formulation_hash,
        exposure_upper: EXPOSURE_UPPER,
        source_thread: "T-01a05601-9ca5-72fc-81b8-a7bab8bdca1d",
    })
}

pub fn anisotropic_structure(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
) -> Result<StationaryHausdorffAnisotropicSplitStructure, String> {
    anisotropic_structure_with_enrichment(order, xi_degree, grid, None)
}

pub fn composed_structure(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    enrichment: &ChargeEnrichment,
) -> Result<StationaryHausdorffAnisotropicSplitStructure, String> {
    anisotropic_structure_with_enrichment(order, xi_degree, grid, Some(enrichment))
}

fn anisotropic_structure_with_enrichment(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    enrichment: Option<&ChargeEnrichment>,
) -> Result<StationaryHausdorffAnisotropicSplitStructure, String> {
    let model = AnisotropicSplitModel::create_with_enrichment(order, xi_degree, grid, enrichment)?;
    let tests = anisotropic_liouville_tests(order, xi_degree)?;
    let cells = grid.cell_count();
    let interfaces = cells.saturating_sub(1);
    let occupation_sides = model.base.gram_dimensions();
    let occupation_counts = model.base.block_counts();
    let interface_sides = model
        .interface_bases
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>();
    let terminal_sides = [usize::from(xi_degree) + 1, usize::from(xi_degree)];
    let mut psd_block_sides = Vec::new();
    let mut psd_block_families = Vec::new();
    for _ in 0..cells {
        psd_block_sides.extend(&occupation_sides);
        psd_block_families.extend(vec![BlockFamily::Occupation; occupation_sides.len()]);
    }
    for _ in 0..interfaces {
        psd_block_sides.extend(&interface_sides);
        psd_block_families.extend(vec![BlockFamily::InterfaceMoment; interface_sides.len()]);
    }
    for _ in 0..cells {
        psd_block_sides.extend(terminal_sides);
        psd_block_families.push(BlockFamily::TerminalMoment);
        psd_block_families.push(BlockFamily::TerminalInterval);
    }
    let knots = grid.canonical_knots();
    let split_grid_hash = grid.canonical_hash();
    let occupation_basis_hash = hash_json(&model.base.moments().keys);
    let interface_basis_hash = hash_json(&model.interfaces.keys);
    let terminal_keys = (0..=2 * u16::from(xi_degree)).collect::<Vec<_>>();
    let terminal_basis_hash = hash_json(&terminal_keys);
    let liouville_basis_hash = hash_json(&tests);
    let formulation_hash = match enrichment {
        None => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-anisotropic-v1",
            "order": order,
            "xi_degree": xi_degree,
            "anisotropic_basis": "state_degree/order + xi_degree/flag <= 1",
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &terminal_basis_hash,
            "liouville_basis_hash": &liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "cell_support": "xi(1-xi)>=0",
            "interface_semantics": "nonnegative one-way state crossing flux",
            "source_thread": "T-01a0573e-e22c-77ed-b97c-61279a7ae523",
        })),
        Some(enrichment) => hash_json(&serde_json::json!({
            "schema": "minexposure/stationary-torus-hausdorff-split-composed-enrichment-xi-exploratory-v1",
            "rigor": "exploratory",
            "order": order,
            "xi_degree": xi_degree,
            "enrichment": enrichment,
            "anisotropic_basis": "state_degree/order + xi_degree/flag <= 1",
            "knots": &knots,
            "split_grid_hash": &split_grid_hash,
            "occupation_basis_hash": &occupation_basis_hash,
            "interface_basis_hash": &interface_basis_hash,
            "terminal_basis_hash": &terminal_basis_hash,
            "liouville_basis_hash": &liouville_basis_hash,
            "psd_block_families": &psd_block_families,
            "psd_block_sides": &psd_block_sides,
            "exposure_upper": EXPOSURE_UPPER,
            "field": "Q(sqrt(2))",
            "cell_support": "xi(1-xi)>=0",
            "interface_semantics": "nonnegative one-way state crossing flux",
            "composition_semantics": "union of the complete anisotropic split Gram blocks and selected-sector charge-enrichment extension blocks; anisotropic Liouville tests retained; exact-certificate schemas and auditors unchanged",
            "source_thread": "T-01a05a6d-11c2-74be-9c3c-08bf97e8708b",
        })),
    };
    let maximum_state_moment_degree = 2 * u16::from(
        order
            .checked_add(enrichment.map_or(0, |value| value.extra_degree))
            .ok_or("composed maximum state moment degree overflows u8")?,
    );
    Ok(StationaryHausdorffAnisotropicSplitStructure {
        schema: enrichment.map(|_| {
            "minexposure/stationary-torus-hausdorff-split-composed-enrichment-xi-exploratory-v1"
        }),
        rigor: enrichment.map(|_| "exploratory"),
        order,
        xi_degree,
        enrichment: enrichment.cloned(),
        maximum_state_moment_degree,
        maximum_xi_moment_degree: 2 * u16::from(xi_degree),
        anisotropic_basis: "state_degree/order + xi_degree/flag <= 1",
        knots,
        split_grid_hash,
        cell_count: cells,
        occupation_moment_count_per_cell: model.base.moments().keys.len(),
        occupation_moment_count: cells * model.base.moments().keys.len(),
        interface_moment_count_per_interface: model.interfaces.keys.len(),
        interface_moment_count: interfaces * model.interfaces.keys.len(),
        terminal_moment_count_per_cell: model.terminal_count,
        terminal_moment_count: cells * model.terminal_count,
        liouville_equality_count_per_cell: tests.len(),
        liouville_equality_count: cells * tests.len(),
        normalization_equality_count: 1,
        occupation_moment_block_count_per_cell: occupation_counts[0],
        occupation_interval_block_count_per_cell: occupation_counts[1],
        occupation_interval_diagonal_count_per_cell: occupation_counts[2],
        interface_moment_block_count_per_interface: interface_sides.len(),
        terminal_block_sides_per_cell: terminal_sides,
        largest_psd_side: psd_block_sides.iter().copied().max().unwrap_or(0),
        sum_psd_squares: psd_block_sides.iter().map(|side| side * side).sum(),
        sum_psd_cubes: psd_block_sides.iter().map(|side| side * side * side).sum(),
        psd_block_families,
        psd_block_sides,
        occupation_basis_hash,
        interface_basis_hash,
        terminal_basis_hash,
        liouville_basis_hash,
        formulation_hash,
        exposure_upper: EXPOSURE_UPPER,
        source_thread: "T-01a0573e-e22c-77ed-b97c-61279a7ae523",
    })
}

pub fn estimate(order: u8, grid: &SplitGrid) -> Result<Estimate, String> {
    estimate_with_options(order, grid, None, None, &[])
}

pub fn enriched_estimate(
    order: u8,
    grid: &SplitGrid,
    enrichment: &ChargeEnrichment,
) -> Result<Estimate, String> {
    estimate_with_options(order, grid, Some(enrichment), None, &[])
}

pub fn u_anisotropic_estimate(
    order: u8,
    u_degree: u8,
    grid: &SplitGrid,
) -> Result<Estimate, String> {
    estimate_with_options(order, grid, None, Some(u_degree), &[])
}

pub fn rydberg_localized_estimate(
    order: u8,
    grid: &SplitGrid,
    charges: &[(i32, i32)],
) -> Result<Estimate, String> {
    estimate_with_options(order, grid, None, None, charges)
}

fn estimate_with_options(
    order: u8,
    grid: &SplitGrid,
    enrichment: Option<&ChargeEnrichment>,
    u_degree: Option<u8>,
    rydberg_localizer_charges: &[(i32, i32)],
) -> Result<Estimate, String> {
    let structure = structure_with_options(
        order,
        grid,
        enrichment,
        u_degree,
        rydberg_localizer_charges,
        None,
    )?;
    let order = RelaxationOrder::standard(order)?;
    let blocks = structure
        .psd_block_sides
        .iter()
        .map(|&side| side as u128)
        .collect::<Vec<_>>();
    let sum_psd_squares = blocks.iter().map(|side| side * side).sum();
    let sum_psd_cubes = blocks.iter().map(|side| side * side * side).sum();
    let equalities =
        (structure.liouville_equality_count + structure.normalization_equality_count) as u128;
    let mut warnings = vec![
        "native piecewise cumulative-cost lift; floating objectives remain exploratory".into(),
        format!(
            "occupation_moments includes {} state-only interface moments; grid {} ({})",
            structure.interface_moment_count, grid, structure.split_grid_hash
        ),
        "raw PSD bytes exclude affine matrices, Schur/KKT fill, scaling, and backend workspaces"
            .into(),
        "affine_nnz_upper_bound is structural, not a serialized matrix count".into(),
    ];
    if let Some(enrichment) = enrichment {
        warnings.push(format!(
            "exploratory charge enrichment {:?} by {} degree(s); baseline Liouville, interface, terminal, and certificate schemas are unchanged",
            enrichment.charges, enrichment.extra_degree
        ));
    }
    if let Some(u_degree) = u_degree {
        warnings.push(format!(
            "exploratory control anisotropy raises the weighted u degree to {u_degree}; baseline Liouville, interface, terminal, and certificate schemas are unchanged"
        ));
    }
    if !rydberg_localizer_charges.is_empty() {
        warnings.push(format!(
            "exploratory |r1|^2 and |r2|^2 product localizers in charge sectors {rydberg_localizer_charges:?}; exact-certificate schemas are unchanged"
        ));
    }
    Ok(Estimate {
        model: ModelId::StationaryTorusHausdorffSplit,
        order,
        occupation_moments: (structure.occupation_moment_count + structure.interface_moment_count)
            as u128,
        terminal_moments: structure.terminal_moment_count as u128,
        psd_block_count: blocks.len() as u128,
        largest_psd_side: blocks.iter().copied().max().unwrap_or(0),
        affine_nnz_upper_bound: equalities * 16 + sum_psd_squares,
        equalities,
        sum_psd_squares,
        sum_psd_cubes,
        raw_psd_bytes: 8 * sum_psd_squares,
        psd_block_sides: blocks,
        warnings,
    })
}

pub fn anisotropic_estimate(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
) -> Result<Estimate, String> {
    anisotropic_estimate_with_enrichment(order, xi_degree, grid, None)
}

pub fn composed_estimate(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    enrichment: &ChargeEnrichment,
) -> Result<Estimate, String> {
    anisotropic_estimate_with_enrichment(order, xi_degree, grid, Some(enrichment))
}

fn anisotropic_estimate_with_enrichment(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    enrichment: Option<&ChargeEnrichment>,
) -> Result<Estimate, String> {
    let structure = anisotropic_structure_with_enrichment(order, xi_degree, grid, enrichment)?;
    let order_metadata = RelaxationOrder::standard(order)?;
    let blocks = structure
        .psd_block_sides
        .iter()
        .map(|&side| side as u128)
        .collect::<Vec<_>>();
    let sum_psd_squares = blocks.iter().map(|side| side * side).sum();
    let sum_psd_cubes = blocks.iter().map(|side| side * side * side).sum();
    let equalities =
        (structure.liouville_equality_count + structure.normalization_equality_count) as u128;
    let mut warnings = vec![
        format!(
            "anisotropic split basis uses state order {order} and xi degree {xi_degree}; floating objectives remain exploratory"
        ),
        format!(
            "occupation_moments includes {} state-only interface moments; grid {} ({})",
            structure.interface_moment_count, grid, structure.split_grid_hash
        ),
        "raw PSD bytes exclude affine matrices, Schur/KKT fill, scaling, and backend workspaces"
            .into(),
        "affine_nnz_upper_bound is structural, not a serialized matrix count".into(),
    ];
    if let Some(enrichment) = enrichment {
        warnings.push(format!(
            "exploratory composition merges charge sectors {:?} by {} degree(s) into matching anisotropic Gram blocks; exact-certificate schemas and auditors do not accept this formulation",
            enrichment.charges, enrichment.extra_degree
        ));
    }
    Ok(Estimate {
        model: ModelId::StationaryTorusHausdorffSplit,
        order: order_metadata,
        occupation_moments: (structure.occupation_moment_count + structure.interface_moment_count)
            as u128,
        terminal_moments: structure.terminal_moment_count as u128,
        psd_block_count: blocks.len() as u128,
        largest_psd_side: blocks.iter().copied().max().unwrap_or(0),
        affine_nnz_upper_bound: equalities * 16 + sum_psd_squares,
        equalities,
        sum_psd_squares,
        sum_psd_cubes,
        raw_psd_bytes: 8 * sum_psd_squares,
        psd_block_sides: blocks,
        warnings,
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

pub fn assemble(order: u8, grid: &SplitGrid) -> Result<StationaryHausdorffSplitProblem, String> {
    assemble_with_options(order, grid, None, None, &[], None)
}

pub fn assemble_with_active_time_cap(
    order: u8,
    grid: &SplitGrid,
    active_time_cap: Rational,
) -> Result<StationaryHausdorffSplitProblem, String> {
    validate_active_time_cap(active_time_cap)?;
    assemble_with_options(order, grid, None, None, &[], Some(active_time_cap))
}

pub fn assemble_enriched(
    order: u8,
    grid: &SplitGrid,
    enrichment: &ChargeEnrichment,
) -> Result<StationaryHausdorffSplitProblem, String> {
    assemble_with_options(order, grid, Some(enrichment), None, &[], None)
}

pub fn assemble_u_anisotropic(
    order: u8,
    u_degree: u8,
    grid: &SplitGrid,
) -> Result<StationaryHausdorffSplitProblem, String> {
    assemble_with_options(order, grid, None, Some(u_degree), &[], None)
}

pub fn assemble_rydberg_localized(
    order: u8,
    grid: &SplitGrid,
    charges: &[(i32, i32)],
) -> Result<StationaryHausdorffSplitProblem, String> {
    assemble_with_options(order, grid, None, None, charges, None)
}

fn assemble_with_options(
    order: u8,
    grid: &SplitGrid,
    enrichment: Option<&ChargeEnrichment>,
    u_degree: Option<u8>,
    rydberg_localizer_charges: &[(i32, i32)],
    active_time_cap: Option<Rational>,
) -> Result<StationaryHausdorffSplitProblem, String> {
    let structure = structure_with_options(
        order,
        grid,
        enrichment,
        u_degree,
        rydberg_localizer_charges,
        active_time_cap,
    )?;
    let exact = match (
        enrichment,
        u_degree,
        rydberg_localizer_charges.is_empty(),
        active_time_cap,
    ) {
        (Some(enrichment), None, true, None) => {
            ExactSplitModel::create_with_enrichment(order, grid, Some(enrichment))?
        }
        (None, Some(u_degree), true, None) => {
            ExactSplitModel::create_with_u_degree(order, u_degree, grid)?
        }
        (None, None, false, None) => {
            ExactSplitModel::create_with_rydberg_localizers(order, grid, rydberg_localizer_charges)?
        }
        (None, None, true, Some(_)) => ExactSplitModel::create_active_time_capped(order, grid)?,
        (None, None, true, None) => ExactSplitModel::create(order, grid)?,
        _ => {
            return Err(
                "exploratory split strengthenings must be tested one family at a time".into(),
            );
        }
    };
    let occupation_scale = active_time_cap
        .map(active_time_solver_scale)
        .unwrap_or(Rational::ONE);
    let inverse_occupation_scale =
        Rational::new(occupation_scale.denominator, occupation_scale.numerator);
    let inverse_cap = active_time_cap
        .map(|cap| Rational::new(cap.denominator, cap.numerator))
        .unwrap_or(Rational::ONE);
    let cap_row_scale = occupation_scale * inverse_cap;
    let occupation_end = exact.cell_count() * exact.base.moments().keys.len();
    let mut q = vec![0.0; exact.coefficient_count];
    for &offset in &exact.cell_offsets {
        for &(position, coefficient) in &exact.base.cost {
            q[offset + position] =
                (coefficient * Qsqrt2::new(occupation_scale, Rational::ZERO)).to_f64();
        }
    }

    let mut sparse = SparseBuilder::default();
    let mut b = Vec::with_capacity(exact.rows.len() + 1);
    for (row_index, equality) in exact.rows.iter().enumerate() {
        for &(column, coefficient) in &equality.coefficients {
            let coefficient = if column < occupation_end {
                coefficient
            } else {
                coefficient * Qsqrt2::new(inverse_occupation_scale, Rational::ZERO)
            };
            sparse.add(row_index, column, coefficient);
        }
        b.push(equality.rhs as f64 * rational_f64(inverse_occupation_scale));
    }
    let normalization_row = b.len();
    for &terminal_offset in &exact.terminal_offsets {
        sparse.add(normalization_row, terminal_offset, Qsqrt2::from(1));
    }
    b.push(1.0);

    let mut cones = vec![Cone::Zero(b.len())];
    let mut next_row = b.len();
    let occupation_dimensions = exact.base.occupation_gram_dimensions();
    for &cell_offset in &exact.cell_offsets {
        for (block_index, &side) in occupation_dimensions.iter().enumerate() {
            for column in 0..side {
                for row in 0..=column {
                    let scale = if row == column {
                        Qsqrt2::from(1)
                    } else {
                        Qsqrt2::new(Rational::ZERO, Rational::ONE)
                    };
                    exact.base.for_each_gram_entry_coefficient(
                        block_index,
                        row,
                        column,
                        |position, coefficient| {
                            sparse.add(next_row, cell_offset + position, -(coefficient * scale));
                        },
                    );
                    b.push(0.0);
                    next_row += 1;
                }
            }
            cones.push(Cone::PsdTriangle(side));
        }
    }
    for &interface_offset in &exact.interface_offsets {
        for basis in &exact.interface_bases {
            let side = basis.len();
            for column in 0..side {
                for row in 0..=column {
                    let scale = if row == column {
                        Qsqrt2::from(1)
                    } else {
                        Qsqrt2::new(Rational::ZERO, Rational::ONE)
                    };
                    for (position, coefficient) in interface_gram_entry_coefficients(
                        &exact.interfaces,
                        &basis[row],
                        &basis[column],
                    ) {
                        sparse.add(
                            next_row,
                            interface_offset + position,
                            -(coefficient * scale),
                        );
                    }
                    b.push(0.0);
                    next_row += 1;
                }
            }
            cones.push(Cone::PsdTriangle(side));
        }
    }
    for &terminal_offset in &exact.terminal_offsets {
        let moment_side = usize::from(order) + 1;
        for column in 0..moment_side {
            for row in 0..=column {
                let scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                sparse.add(next_row, terminal_offset + row + column, -scale);
                b.push(0.0);
                next_row += 1;
            }
        }
        cones.push(Cone::PsdTriangle(moment_side));

        let interval_side = usize::from(order);
        for column in 0..interval_side {
            for row in 0..=column {
                let scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                sparse.add(next_row, terminal_offset + row + column + 1, -scale);
                sparse.add(next_row, terminal_offset + row + column + 2, scale);
                b.push(0.0);
                next_row += 1;
            }
        }
        cones.push(Cone::PsdTriangle(interval_side));
    }

    if active_time_cap.is_some() {
        exact.for_each_active_time_position(|column| {
            sparse.add(next_row, column, Qsqrt2::new(cap_row_scale, Rational::ZERO));
        });
        b.push(1.0);
        next_row += 1;
        cones.push(Cone::Nonnegative(1));
    }

    let conic = ConicProblem {
        q,
        a: SparseMatrix {
            rows: next_row,
            cols: exact.coefficient_count,
            entries: sparse.finish(),
        },
        b,
        cones,
    };
    conic.validate()?;
    Ok(StationaryHausdorffSplitProblem { structure, conic })
}

fn validate_active_time_cap(active_time_cap: Rational) -> Result<(), String> {
    if active_time_cap.numerator <= 0 {
        return Err("active-time cap must be positive".into());
    }
    let value = rational_f64(active_time_cap);
    if !value.is_finite() {
        return Err("active-time cap is outside the finite floating-point range".into());
    }
    Ok(())
}

fn active_time_solver_scale(active_time_cap: Rational) -> Rational {
    if rational_f64(active_time_cap) <= 1_000.0 {
        Rational::ONE
    } else {
        active_time_cap * Rational::new(1, 1_000)
    }
}

pub fn assemble_anisotropic(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
) -> Result<StationaryHausdorffAnisotropicSplitProblem, String> {
    assemble_anisotropic_with_enrichment(order, xi_degree, grid, None)
}

pub fn assemble_composed(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    enrichment: &ChargeEnrichment,
) -> Result<StationaryHausdorffAnisotropicSplitProblem, String> {
    assemble_anisotropic_with_enrichment(order, xi_degree, grid, Some(enrichment))
}

fn assemble_anisotropic_with_enrichment(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    enrichment: Option<&ChargeEnrichment>,
) -> Result<StationaryHausdorffAnisotropicSplitProblem, String> {
    let structure = anisotropic_structure_with_enrichment(order, xi_degree, grid, enrichment)?;
    let model = AnisotropicSplitModel::create_with_enrichment(order, xi_degree, grid, enrichment)?;
    let mut q = vec![0.0; model.coefficient_count];
    for &offset in &model.cell_offsets {
        for &(position, coefficient) in model.base.cost() {
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
    let occupation_dimensions = model.base.gram_dimensions();
    for &cell_offset in &model.cell_offsets {
        for (block_index, &side) in occupation_dimensions.iter().enumerate() {
            for column in 0..side {
                for row in 0..=column {
                    let scale = if row == column {
                        Qsqrt2::from(1)
                    } else {
                        Qsqrt2::new(Rational::ZERO, Rational::ONE)
                    };
                    model.base.for_each_gram_entry_coefficient(
                        block_index,
                        row,
                        column,
                        |position, coefficient| {
                            sparse.add(next_row, cell_offset + position, -(coefficient * scale));
                        },
                    );
                    b.push(0.0);
                    next_row += 1;
                }
            }
            cones.push(Cone::PsdTriangle(side));
        }
    }
    for &interface_offset in &model.interface_offsets {
        for basis in &model.interface_bases {
            let side = basis.len();
            for column in 0..side {
                for row in 0..=column {
                    let scale = if row == column {
                        Qsqrt2::from(1)
                    } else {
                        Qsqrt2::new(Rational::ZERO, Rational::ONE)
                    };
                    for (position, coefficient) in interface_gram_entry_coefficients(
                        &model.interfaces,
                        &basis[row],
                        &basis[column],
                    ) {
                        sparse.add(
                            next_row,
                            interface_offset + position,
                            -(coefficient * scale),
                        );
                    }
                    b.push(0.0);
                    next_row += 1;
                }
            }
            cones.push(Cone::PsdTriangle(side));
        }
    }
    for &terminal_offset in &model.terminal_offsets {
        let moment_side = usize::from(xi_degree) + 1;
        for column in 0..moment_side {
            for row in 0..=column {
                let scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                sparse.add(next_row, terminal_offset + row + column, -scale);
                b.push(0.0);
                next_row += 1;
            }
        }
        cones.push(Cone::PsdTriangle(moment_side));

        let interval_side = usize::from(xi_degree);
        for column in 0..interval_side {
            for row in 0..=column {
                let scale = if row == column {
                    Qsqrt2::from(1)
                } else {
                    Qsqrt2::new(Rational::ZERO, Rational::ONE)
                };
                sparse.add(next_row, terminal_offset + row + column + 1, -scale);
                sparse.add(next_row, terminal_offset + row + column + 2, scale);
                b.push(0.0);
                next_row += 1;
            }
        }
        cones.push(Cone::PsdTriangle(interval_side));
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
    Ok(StationaryHausdorffAnisotropicSplitProblem { structure, conic })
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitWitnessCell {
    pub cell: usize,
    pub lower_knot: String,
    pub upper_knot: String,
    pub occupation_moments: Vec<f64>,
    pub terminal_moments: Vec<f64>,
    pub terminal_mass: f64,
    pub maximum_liouville_residual: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitWitnessInterface {
    pub interface: usize,
    pub knot: String,
    pub time: f64,
    pub state: [[f64; 2]; STATE_VARIABLES],
    pub state_moments: Vec<f64>,
}

trait WitnessSplitModel {
    fn occupation_moments(&self) -> &MomentSpace;
    fn interface_moments(&self) -> &MomentSpace;
    fn cost(&self) -> &[(usize, Qsqrt2)];
    fn rows(&self) -> &[ExactSplitRow];
    fn cell_offsets(&self) -> &[usize];
    fn interface_offsets(&self) -> &[usize];
    fn terminal_offsets(&self) -> &[usize];
    fn terminal_count(&self) -> usize;
    fn coefficient_count(&self) -> usize;
}

impl WitnessSplitModel for ExactSplitModel {
    fn occupation_moments(&self) -> &MomentSpace {
        self.base.moments()
    }

    fn interface_moments(&self) -> &MomentSpace {
        &self.interfaces
    }

    fn cost(&self) -> &[(usize, Qsqrt2)] {
        &self.base.cost
    }

    fn rows(&self) -> &[ExactSplitRow] {
        &self.rows
    }

    fn cell_offsets(&self) -> &[usize] {
        &self.cell_offsets
    }

    fn interface_offsets(&self) -> &[usize] {
        &self.interface_offsets
    }

    fn terminal_offsets(&self) -> &[usize] {
        &self.terminal_offsets
    }

    fn terminal_count(&self) -> usize {
        self.terminal_count
    }

    fn coefficient_count(&self) -> usize {
        self.coefficient_count
    }
}

impl WitnessSplitModel for AnisotropicSplitModel {
    fn occupation_moments(&self) -> &MomentSpace {
        self.base.moments()
    }

    fn interface_moments(&self) -> &MomentSpace {
        &self.interfaces
    }

    fn cost(&self) -> &[(usize, Qsqrt2)] {
        self.base.cost()
    }

    fn rows(&self) -> &[ExactSplitRow] {
        &self.rows
    }

    fn cell_offsets(&self) -> &[usize] {
        &self.cell_offsets
    }

    fn interface_offsets(&self) -> &[usize] {
        &self.interface_offsets
    }

    fn terminal_offsets(&self) -> &[usize] {
        &self.terminal_offsets
    }

    fn terminal_count(&self) -> usize {
        self.terminal_count
    }

    fn coefficient_count(&self) -> usize {
        self.coefficient_count
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitWitnessDiagnostic {
    pub schema: &'static str,
    pub order: u8,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub xi_degree: Option<u8>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub enrichment: Option<ChargeEnrichment>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub u_degree: Option<u8>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rydberg_localizer_charges: Vec<(i32, i32)>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub active_time_cap: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bound_scope: Option<&'static str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub active_time_cap_slack: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub active_time_cap_feasible: Option<bool>,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub segment_count: usize,
    pub duration: f64,
    pub trajectory_objective: f64,
    pub terminal_normalized_cost: f64,
    pub terminal_cell: usize,
    pub occupation_moment_basis: Vec<CostMonomial>,
    pub interface_moment_basis: Vec<CostMonomial>,
    pub terminal_moment_powers: Vec<usize>,
    pub cells: Vec<SplitWitnessCell>,
    pub interfaces: Vec<SplitWitnessInterface>,
    pub maximum_discarded_reflection_imaginary_part: f64,
    pub maximum_liouville_residual: f64,
    pub normalization_residual: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitSlackLocation {
    pub segment: usize,
    pub fraction: f64,
    pub time: f64,
    pub cell: usize,
    pub normalized_cost: f64,
    pub local_coordinate: f64,
    pub multiplier_slack: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitChargeContribution {
    pub charge: (i32, i32),
    pub moment: f64,
    pub interval: f64,
    pub interval_diagonal: f64,
    pub total: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitChargeProfile {
    pub location: SplitSlackLocation,
    pub gram_total: f64,
    pub gram_identity_error: f64,
    pub largest_sectors: Vec<SplitChargeContribution>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitGramTargetEntry {
    pub row: usize,
    pub column: usize,
    pub coefficient: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitFaceTerm {
    pub coefficient: i64,
    pub monomial: CostMonomial,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitNullVectorComponent {
    pub gram_row: usize,
    pub amplitude: f64,
    pub face: Vec<SplitFaceTerm>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitTrackedGramFace {
    pub cell: usize,
    pub block_index_per_cell: usize,
    pub kind: &'static str,
    pub charge: (i32, i32),
    pub side: usize,
    pub minimum_eigenvalue: f64,
    pub spectral_radius: f64,
    pub null_threshold: f64,
    pub numerical_nullity: usize,
    pub target_entries: Vec<SplitGramTargetEntry>,
    pub target_row_null_projection: f64,
    pub dominant_null_eigenvalue: Option<f64>,
    pub dominant_null_components: Vec<SplitNullVectorComponent>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitLiouvilleOccurrence {
    pub cell: usize,
    pub row_per_cell: usize,
    pub test: CostMonomial,
    pub coefficient: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitTrackedPrimalFace {
    pub name: &'static str,
    pub moment: CostMonomial,
    pub moment_position_per_cell: usize,
    pub solver_global_value: f64,
    pub gram_faces: Vec<SplitTrackedGramFace>,
    pub liouville_rows: Vec<SplitLiouvilleOccurrence>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SplitChargeDiagnostic {
    pub schema: &'static str,
    pub order: u8,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub enrichment: Option<ChargeEnrichment>,
    pub knots: Vec<String>,
    pub split_grid_hash: String,
    pub trajectory_objective: f64,
    pub solver_objective: f64,
    pub objective_gap: f64,
    pub maximum_liouville_residual: f64,
    pub normalization_residual: f64,
    pub profiles: Vec<SplitChargeProfile>,
    pub maximum_gram_identity_error: f64,
    pub tracked_primal_faces: Vec<SplitTrackedPrimalFace>,
}

pub fn diagnose_ideal_blockade_pulse(
    order: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
) -> Result<SplitWitnessDiagnostic, String> {
    let model = ExactSplitModel::create(order, grid)?;
    diagnose_ideal_blockade_pulse_with_model(order, None, None, None, &[], grid, pulse, &model)
}

pub fn diagnose_ideal_blockade_pulse_with_active_time_cap(
    order: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
    active_time_cap: Rational,
) -> Result<SplitWitnessDiagnostic, String> {
    validate_active_time_cap(active_time_cap)?;
    let model = ExactSplitModel::create_active_time_capped(order, grid)?;
    let mut report = diagnose_ideal_blockade_pulse_with_model(
        order,
        None,
        None,
        None,
        &[],
        grid,
        pulse,
        &model,
    )?;
    let cap = rational_f64(active_time_cap);
    let slack = cap - report.duration;
    report.schema = "minexposure/stationary-torus-hausdorff-split-active-time-capped-witness-v1";
    report.active_time_cap = Some(active_time_cap.to_string());
    report.bound_scope = Some(ACTIVE_TIME_CAPPED_BOUND_SCOPE);
    report.active_time_cap_slack = Some(slack);
    report.active_time_cap_feasible = Some(slack >= -1e-12);
    Ok(report)
}

pub fn diagnose_ideal_blockade_pulse_anisotropic(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
) -> Result<SplitWitnessDiagnostic, String> {
    let model = AnisotropicSplitModel::create(order, xi_degree, grid)?;
    diagnose_ideal_blockade_pulse_with_model(
        order,
        Some(xi_degree),
        None,
        None,
        &[],
        grid,
        pulse,
        &model,
    )
}

pub fn diagnose_enriched_ideal_blockade_pulse(
    order: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
    enrichment: &ChargeEnrichment,
) -> Result<SplitWitnessDiagnostic, String> {
    let model = ExactSplitModel::create_with_enrichment(order, grid, Some(enrichment))?;
    diagnose_ideal_blockade_pulse_with_model(
        order,
        None,
        Some(enrichment),
        None,
        &[],
        grid,
        pulse,
        &model,
    )
}

pub fn diagnose_u_anisotropic_ideal_blockade_pulse(
    order: u8,
    u_degree: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
) -> Result<SplitWitnessDiagnostic, String> {
    let model = ExactSplitModel::create_with_u_degree(order, u_degree, grid)?;
    diagnose_ideal_blockade_pulse_with_model(
        order,
        None,
        None,
        Some(u_degree),
        &[],
        grid,
        pulse,
        &model,
    )
}

pub fn diagnose_rydberg_localized_ideal_blockade_pulse(
    order: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
    charges: &[(i32, i32)],
) -> Result<SplitWitnessDiagnostic, String> {
    let model = ExactSplitModel::create_with_rydberg_localizers(order, grid, charges)?;
    diagnose_ideal_blockade_pulse_with_model(order, None, None, None, charges, grid, pulse, &model)
}

pub fn diagnose_composed_ideal_blockade_pulse(
    order: u8,
    xi_degree: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
    enrichment: &ChargeEnrichment,
) -> Result<SplitWitnessDiagnostic, String> {
    let model =
        AnisotropicSplitModel::create_with_enrichment(order, xi_degree, grid, Some(enrichment))?;
    diagnose_ideal_blockade_pulse_with_model(
        order,
        Some(xi_degree),
        Some(enrichment),
        None,
        &[],
        grid,
        pulse,
        &model,
    )
}

#[allow(clippy::too_many_arguments)]
fn diagnose_ideal_blockade_pulse_with_model(
    order: u8,
    xi_degree: Option<u8>,
    enrichment: Option<&ChargeEnrichment>,
    u_degree: Option<u8>,
    rydberg_localizer_charges: &[(i32, i32)],
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
    model: &impl WitnessSplitModel,
) -> Result<SplitWitnessDiagnostic, String> {
    if pulse.phases.is_empty() || !pulse.duration.is_finite() || pulse.duration <= 0.0 {
        return Err("invalid ideal-blockade pulse".into());
    }
    let cells = grid.cell_count();
    let occupation_count = model.occupation_moments().keys.len();
    let interface_count = model.interface_moments().keys.len();
    let terminal_count = model.terminal_count();
    let mut occupation = vec![vec![0.0; occupation_count]; cells];
    let mut interface_values = Vec::with_capacity(cells.saturating_sub(1));
    let mut maximum_discarded = 0.0_f64;
    let segment_duration = pulse.duration / pulse.phases.len() as f64;
    let quadrature = gauss_legendre(32);
    let exposure_upper = rational_f64(EXPOSURE_UPPER);
    let target_exposures = grid.knots()[1..grid.knots().len() - 1]
        .iter()
        .map(|&knot| exposure_upper * rational_f64(knot))
        .collect::<Vec<_>>();
    let knot_values = grid
        .knots()
        .iter()
        .map(|&knot| rational_f64(knot))
        .collect::<Vec<_>>();
    let mut state = initial_state();
    let mut cumulative_exposure = 0.0;
    let mut current_cell = 0;

    for (segment, &phase) in pulse.phases.iter().enumerate() {
        let segment_start_state = state;
        let segment_exposure =
            segment_cost_integral(&segment_start_state, phase, segment_duration, 1.0);
        let segment_end_exposure = cumulative_exposure + segment_exposure;
        let mut lower_fraction = 0.0;
        while current_cell < target_exposures.len()
            && target_exposures[current_cell] <= segment_end_exposure + 2e-14
        {
            let target = target_exposures[current_cell];
            let crossing = if target <= cumulative_exposure + 2e-14 {
                lower_fraction
            } else {
                crossing_fraction(
                    &segment_start_state,
                    phase,
                    segment_duration,
                    target - cumulative_exposure,
                    lower_fraction,
                )
            };
            integrate_piece(
                &mut occupation[current_cell],
                &model.occupation_moments().keys,
                current_cell,
                grid,
                cumulative_exposure,
                &segment_start_state,
                phase,
                segment_duration,
                lower_fraction,
                crossing,
                &quadrature,
                &mut maximum_discarded,
            );
            let point = trajectory_point(&segment_start_state, phase, segment_duration, crossing);
            let state_at_interface = [point[1], point[2], point[3], point[4]];
            let moments = moment_values(
                &model.interface_moments().keys,
                &state_at_interface,
                0.0,
                STATE_VARIABLES,
                &mut maximum_discarded,
            );
            debug_assert_eq!(moments.len(), interface_count);
            interface_values.push(SplitWitnessInterface {
                interface: current_cell + 1,
                knot: grid.knots()[current_cell + 1].to_string(),
                time: (segment as f64 + crossing) * segment_duration,
                state: state_at_interface.map(|value| [value.re, value.im]),
                state_moments: moments,
            });
            current_cell += 1;
            lower_fraction = crossing;
        }
        if lower_fraction < 1.0 {
            integrate_piece(
                &mut occupation[current_cell],
                &model.occupation_moments().keys,
                current_cell,
                grid,
                cumulative_exposure,
                &segment_start_state,
                phase,
                segment_duration,
                lower_fraction,
                1.0,
                &quadrature,
                &mut maximum_discarded,
            );
        }
        let endpoint = trajectory_point(&segment_start_state, phase, segment_duration, 1.0);
        state.copy_from_slice(&endpoint[1..]);
        cumulative_exposure = segment_end_exposure;
    }

    let terminal_normalized_cost = cumulative_exposure / exposure_upper;
    if terminal_normalized_cost >= 1.0 {
        return Err(format!(
            "witness terminal normalized cost {terminal_normalized_cost:.16} is not below 1"
        ));
    }
    if interface_values.len() != cells.saturating_sub(1) {
        return Err(format!(
            "witness crossed {} interfaces, expected {}",
            interface_values.len(),
            cells.saturating_sub(1)
        ));
    }
    let terminal_cell = grid
        .knots()
        .windows(2)
        .position(|pair| {
            terminal_normalized_cost >= rational_f64(pair[0])
                && terminal_normalized_cost <= rational_f64(pair[1])
        })
        .ok_or("witness terminal cost is outside the split grid")?;
    let terminal_xi = (terminal_normalized_cost - knot_values[terminal_cell])
        / (knot_values[terminal_cell + 1] - knot_values[terminal_cell]);
    let mut terminal = vec![vec![0.0; terminal_count]; cells];
    let mut power = 1.0;
    for moment in &mut terminal[terminal_cell] {
        *moment = power;
        power *= terminal_xi;
    }

    let mut variables = vec![0.0; model.coefficient_count()];
    for (offset, moments) in model.cell_offsets().iter().zip(&occupation) {
        variables[*offset..*offset + occupation_count].copy_from_slice(moments);
    }
    for (offset, interface) in model.interface_offsets().iter().zip(&interface_values) {
        variables[*offset..*offset + interface_count].copy_from_slice(&interface.state_moments);
    }
    for (offset, moments) in model.terminal_offsets().iter().zip(&terminal) {
        variables[*offset..*offset + terminal_count].copy_from_slice(moments);
    }

    let mut maximum_by_cell = vec![0.0_f64; cells];
    for row in model.rows() {
        let lhs = row
            .coefficients
            .iter()
            .map(|&(position, coefficient)| coefficient.to_f64() * variables[position])
            .sum::<f64>();
        maximum_by_cell[row.cell] = maximum_by_cell[row.cell].max((lhs - row.rhs as f64).abs());
    }
    let maximum_liouville_residual = maximum_by_cell.iter().copied().fold(0.0, f64::max);
    let normalization_residual =
        (terminal.iter().map(|moments| moments[0]).sum::<f64>() - 1.0).abs();
    let trajectory_objective = model
        .cell_offsets()
        .iter()
        .map(|&offset| {
            model
                .cost()
                .iter()
                .map(|&(position, coefficient)| coefficient.to_f64() * variables[offset + position])
                .sum::<f64>()
        })
        .sum();
    let cells = occupation
        .into_iter()
        .zip(terminal)
        .enumerate()
        .map(
            |(cell, (occupation_moments, terminal_moments))| SplitWitnessCell {
                cell: cell + 1,
                lower_knot: grid.knots()[cell].to_string(),
                upper_knot: grid.knots()[cell + 1].to_string(),
                occupation_moments,
                terminal_mass: terminal_moments[0],
                terminal_moments,
                maximum_liouville_residual: maximum_by_cell[cell],
            },
        )
        .collect();

    Ok(SplitWitnessDiagnostic {
        schema: match (xi_degree, enrichment) {
            (Some(_), Some(_)) => {
                "minexposure/stationary-torus-hausdorff-split-composed-enrichment-xi-exploratory-witness-v1"
            }
            (Some(_), None) => {
                "minexposure/stationary-torus-hausdorff-split-anisotropic-witness-v1"
            }
            (None, Some(_)) => "minexposure/stationary-torus-hausdorff-split-witness-v1",
            (None, None) if u_degree.is_some() => {
                "minexposure/stationary-torus-hausdorff-split-u-anisotropic-exploratory-witness-v1"
            }
            (None, None) if !rydberg_localizer_charges.is_empty() => {
                "minexposure/stationary-torus-hausdorff-split-rydberg-product-localizers-exploratory-witness-v1"
            }
            (None, None) => "minexposure/stationary-torus-hausdorff-split-witness-v1",
        },
        order,
        xi_degree,
        enrichment: enrichment.cloned(),
        u_degree,
        rydberg_localizer_charges: rydberg_localizer_charges.to_vec(),
        active_time_cap: None,
        bound_scope: None,
        active_time_cap_slack: None,
        active_time_cap_feasible: None,
        knots: grid.canonical_knots(),
        split_grid_hash: grid.canonical_hash(),
        segment_count: pulse.phases.len(),
        duration: pulse.duration,
        trajectory_objective,
        terminal_normalized_cost,
        terminal_cell: terminal_cell + 1,
        occupation_moment_basis: model.occupation_moments().keys.clone(),
        interface_moment_basis: model.interface_moments().keys.clone(),
        terminal_moment_powers: (0..terminal_count).collect(),
        cells,
        interfaces: interface_values,
        maximum_discarded_reflection_imaginary_part: maximum_discarded,
        maximum_liouville_residual,
        normalization_residual,
    })
}

pub fn diagnose_solution_charge_slack(
    order: u8,
    grid: &SplitGrid,
    pulse: &IdealBlockadePulse,
    solution: &StationarySolutionDump,
    enrichment: Option<&ChargeEnrichment>,
) -> Result<SplitChargeDiagnostic, String> {
    if pulse.phases.is_empty() || !pulse.duration.is_finite() || pulse.duration <= 0.0 {
        return Err("invalid ideal-blockade pulse".into());
    }
    let exact = ExactSplitModel::create_with_enrichment(order, grid, enrichment)?;
    if solution.primal_variables.len() != exact.coefficient_count() {
        return Err(format!(
            "solution has {} primal variables, expected {}",
            solution.primal_variables.len(),
            exact.coefficient_count()
        ));
    }
    if solution.dual.zero_cone_multipliers.len() != exact.rows.len() + 1 {
        return Err(format!(
            "solution has {} zero-cone multipliers, expected {} Liouville rows plus normalization",
            solution.dual.zero_cone_multipliers.len(),
            exact.rows.len()
        ));
    }
    let dimensions = exact.gram_dimensions();
    if solution.dual.psd_blocks.len() != dimensions.len() {
        return Err(format!(
            "solution has {} PSD blocks, expected {}",
            solution.dual.psd_blocks.len(),
            dimensions.len()
        ));
    }
    for (index, (matrix, &side)) in solution.dual.psd_blocks.iter().zip(&dimensions).enumerate() {
        if matrix.side != side || matrix.lower_triangle_column_major.len() != side * (side + 1) / 2
        {
            return Err(format!(
                "solution PSD block {index} has the wrong dimensions"
            ));
        }
    }

    let tests = liouville_tests(order);
    let inverse_widths = grid.inverse_widths()?;
    let knot_values = grid
        .knots()
        .iter()
        .map(|&knot| rational_f64(knot))
        .collect::<Vec<_>>();
    let exposure_upper = rational_f64(EXPOSURE_UPPER);
    let segment_duration = pulse.duration / pulse.phases.len() as f64;
    let mut state = initial_state();
    let mut cumulative_exposure = 0.0;
    let mut maxima =
        vec![None::<(SplitSlackLocation, [Complex64; BULK_VARIABLES])>; grid.cell_count()];
    for (segment, &phase) in pulse.phases.iter().enumerate() {
        let point = trajectory_point(&state, phase, segment_duration, 0.5);
        let midpoint_exposure =
            cumulative_exposure + segment_cost_integral(&state, phase, segment_duration, 0.5);
        let normalized_cost = midpoint_exposure / exposure_upper;
        let cell = knot_values
            .windows(2)
            .position(|pair| normalized_cost >= pair[0] && normalized_cost <= pair[1])
            .ok_or_else(|| format!("segment {segment} midpoint cost is outside the split grid"))?;
        let local_coordinate =
            (normalized_cost - knot_values[cell]) / (knot_values[cell + 1] - knot_values[cell]);
        let mut discarded_imaginary_part = 0.0;
        let values = moment_values(
            &exact.base.moments().keys,
            &point,
            local_coordinate,
            BULK_VARIABLES,
            &mut discarded_imaginary_part,
        );
        let mut multiplier_slack = 0.5 * point[2].norm_sqr() + 0.25 * point[4].norm_sqr();
        for (test_index, test) in tests.iter().enumerate() {
            let derivative =
                scaled_liouville_coefficients(test, inverse_widths[cell], exact.base.moments())
                    .into_iter()
                    .map(|(position, coefficient)| coefficient.to_f64() * values[position])
                    .sum::<f64>();
            multiplier_slack +=
                solution.dual.zero_cone_multipliers[cell * tests.len() + test_index] * derivative;
        }
        let location = SplitSlackLocation {
            segment,
            fraction: 0.5,
            time: (segment as f64 + 0.5) * segment_duration,
            cell: cell + 1,
            normalized_cost,
            local_coordinate,
            multiplier_slack,
        };
        if maxima[cell]
            .as_ref()
            .is_none_or(|(current, _)| multiplier_slack > current.multiplier_slack)
        {
            maxima[cell] = Some((location, point));
        }
        cumulative_exposure += segment_cost_integral(&state, phase, segment_duration, 1.0);
        let endpoint = trajectory_point(&state, phase, segment_duration, 1.0);
        state.copy_from_slice(&endpoint[1..]);
    }

    let occupation_blocks = exact.base.occupation_blocks();
    let occupation_count = occupation_blocks.len();
    let mut profiles = Vec::with_capacity(grid.cell_count());
    let mut maximum_gram_identity_error = 0.0_f64;
    for (cell, maximum) in maxima.into_iter().enumerate() {
        let (location, point) =
            maximum.ok_or_else(|| format!("witness has no sample in cell {}", cell + 1))?;
        let matrices =
            &solution.dual.psd_blocks[cell * occupation_count..(cell + 1) * occupation_count];
        let mut by_charge = BTreeMap::<(i32, i32), [f64; 3]>::new();
        for (block, matrix) in occupation_blocks.iter().zip(matrices) {
            let value = evaluate_occupation_gram(block, matrix, &point, location.local_coordinate);
            let family = match block.kind.expect("occupation block has a kind") {
                crate::stationary_hausdorff::OccupationBlockKind::Moment => 0,
                crate::stationary_hausdorff::OccupationBlockKind::Interval => 1,
                crate::stationary_hausdorff::OccupationBlockKind::IntervalDiagonal => 2,
            };
            by_charge.entry(block.charge).or_default()[family] += value;
        }
        let gram_total = by_charge.values().flatten().sum::<f64>();
        let gram_identity_error = (gram_total - location.multiplier_slack).abs();
        maximum_gram_identity_error = maximum_gram_identity_error.max(gram_identity_error);
        let mut largest_sectors = by_charge
            .into_iter()
            .map(|(charge, values)| SplitChargeContribution {
                charge,
                moment: values[0],
                interval: values[1],
                interval_diagonal: values[2],
                total: values.iter().sum(),
            })
            .collect::<Vec<_>>();
        largest_sectors.sort_by(|left, right| right.total.abs().total_cmp(&left.total.abs()));
        largest_sectors.truncate(16);
        profiles.push(SplitChargeProfile {
            location,
            gram_total,
            gram_identity_error,
            largest_sectors,
        });
    }

    let witness = match enrichment {
        Some(enrichment) => diagnose_enriched_ideal_blockade_pulse(order, grid, pulse, enrichment)?,
        None => diagnose_ideal_blockade_pulse(order, grid, pulse)?,
    };
    let tracked_primal_faces = diagnose_tracked_primal_faces(order, &exact, solution)?;
    Ok(SplitChargeDiagnostic {
        schema: "minexposure/stationary-torus-hausdorff-split-charge-diagnostic-v1",
        order,
        enrichment: enrichment.cloned(),
        knots: grid.canonical_knots(),
        split_grid_hash: grid.canonical_hash(),
        trajectory_objective: witness.trajectory_objective,
        solver_objective: solution.objective,
        objective_gap: witness.trajectory_objective - solution.objective,
        maximum_liouville_residual: witness.maximum_liouville_residual,
        normalization_residual: witness.normalization_residual,
        profiles,
        maximum_gram_identity_error,
        tracked_primal_faces,
    })
}

fn diagnose_tracked_primal_faces(
    order: u8,
    exact: &ExactSplitModel,
    solution: &StationarySolutionDump,
) -> Result<Vec<SplitTrackedPrimalFace>, String> {
    let tracked = [
        ("g2bar_u_g1_r1", &[0, 0, 0, 1, 0][..], &[1, 1, 1, 0, 0][..]),
        ("g1bar2_u_r2", &[0, 2, 0, 0, 0][..], &[1, 0, 0, 0, 1][..]),
    ];
    let tests = liouville_tests(order);
    let occupation_blocks = exact.base.occupation_blocks();
    let occupation_count = exact.base.moments().keys.len();
    let mut diagnostics = Vec::with_capacity(tracked.len());

    for (name, anti, holo) in tracked {
        let (moment_position, moment) = exact
            .base
            .moments()
            .keys
            .iter()
            .enumerate()
            .find(|(_, key)| key.cost_power == 0 && key.anti.0 == anti && key.holo.0 == holo)
            .map(|(position, key)| (position, key.clone()))
            .ok_or_else(|| format!("tracked moment {name} is absent"))?;
        let solver_global_value = exact
            .cell_offsets
            .iter()
            .map(|&offset| solution.primal_variables[offset + moment_position])
            .sum();
        let mut gram_faces = Vec::new();

        for (block_index, block) in occupation_blocks.iter().enumerate() {
            let side = block.face.len();
            let mut target_entries = Vec::new();
            for column in 0..side {
                for row in 0..=column {
                    let mut coefficient = 0.0;
                    exact.base.for_each_gram_entry_coefficient(
                        block_index,
                        row,
                        column,
                        |position, value| {
                            if position == moment_position {
                                coefficient += value.to_f64();
                            }
                        },
                    );
                    if coefficient != 0.0 {
                        target_entries.push(SplitGramTargetEntry {
                            row,
                            column,
                            coefficient,
                        });
                    }
                }
            }
            if target_entries.is_empty() {
                continue;
            }
            let mut target_rows = target_entries
                .iter()
                .flat_map(|entry| [entry.row, entry.column])
                .collect::<Vec<_>>();
            target_rows.sort_unstable();
            target_rows.dedup();

            for (cell, &cell_offset) in exact.cell_offsets.iter().enumerate() {
                let moments =
                    &solution.primal_variables[cell_offset..cell_offset + occupation_count];
                let mut matrix = DMatrix::zeros(side, side);
                for column in 0..side {
                    for row in 0..=column {
                        let mut value = 0.0;
                        exact.base.for_each_gram_entry_coefficient(
                            block_index,
                            row,
                            column,
                            |position, coefficient| {
                                value += coefficient.to_f64() * moments[position];
                            },
                        );
                        matrix[(row, column)] = value;
                        matrix[(column, row)] = value;
                    }
                }
                let eigen = SymmetricEigen::new(matrix);
                let spectral_radius = eigen
                    .eigenvalues
                    .iter()
                    .map(|value| value.abs())
                    .fold(0.0_f64, f64::max);
                let null_threshold = (1e-7 * spectral_radius.max(1.0)).max(1e-9);
                let null_indices = eigen
                    .eigenvalues
                    .iter()
                    .enumerate()
                    .filter_map(|(index, &value)| (value.abs() <= null_threshold).then_some(index))
                    .collect::<Vec<_>>();
                let target_row_null_projection = if target_rows.is_empty() {
                    0.0
                } else {
                    target_rows
                        .iter()
                        .map(|&row| {
                            null_indices
                                .iter()
                                .map(|&index| eigen.eigenvectors[(row, index)].powi(2))
                                .sum::<f64>()
                        })
                        .sum::<f64>()
                        / target_rows.len() as f64
                };
                let dominant_null = null_indices.iter().copied().max_by(|&left, &right| {
                    let support = |index| {
                        target_rows
                            .iter()
                            .map(|&row| eigen.eigenvectors[(row, index)].powi(2))
                            .sum::<f64>()
                    };
                    support(left).total_cmp(&support(right))
                });
                let mut dominant_null_components = dominant_null
                    .map(|index| {
                        (0..side)
                            .map(|row| (row, eigen.eigenvectors[(row, index)]))
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                dominant_null_components
                    .sort_by(|left, right| right.1.abs().total_cmp(&left.1.abs()));
                dominant_null_components.truncate(8);
                let dominant_null_components = dominant_null_components
                    .into_iter()
                    .map(|(row, amplitude)| SplitNullVectorComponent {
                        gram_row: row,
                        amplitude,
                        face: block.face[row]
                            .iter()
                            .map(|&(position, coefficient)| SplitFaceTerm {
                                coefficient,
                                monomial: block.basis[position].clone(),
                            })
                            .collect(),
                    })
                    .collect();
                let kind = match block.kind.expect("occupation block has a kind") {
                    crate::stationary_hausdorff::OccupationBlockKind::Moment => "moment",
                    crate::stationary_hausdorff::OccupationBlockKind::Interval => "xi(1-xi)",
                    crate::stationary_hausdorff::OccupationBlockKind::IntervalDiagonal => {
                        "xi(1-xi)-diagonal"
                    }
                };
                gram_faces.push(SplitTrackedGramFace {
                    cell: cell + 1,
                    block_index_per_cell: block_index,
                    kind,
                    charge: block.charge,
                    side,
                    minimum_eigenvalue: eigen.eigenvalues.min(),
                    spectral_radius,
                    null_threshold,
                    numerical_nullity: null_indices.len(),
                    target_entries: target_entries.clone(),
                    target_row_null_projection,
                    dominant_null_eigenvalue: dominant_null.map(|index| eigen.eigenvalues[index]),
                    dominant_null_components,
                });
            }
        }

        let mut liouville_rows = Vec::new();
        for (row_index, row) in exact.rows.iter().enumerate() {
            let offset = exact.cell_offsets[row.cell] + moment_position;
            let coefficient = row
                .coefficients
                .iter()
                .filter(|(position, _)| *position == offset)
                .map(|(_, coefficient)| coefficient.to_f64())
                .sum::<f64>();
            if coefficient != 0.0 {
                let row_per_cell = row_index % tests.len();
                liouville_rows.push(SplitLiouvilleOccurrence {
                    cell: row.cell + 1,
                    row_per_cell,
                    test: tests[row_per_cell].clone(),
                    coefficient,
                });
            }
        }
        diagnostics.push(SplitTrackedPrimalFace {
            name,
            moment,
            moment_position_per_cell: moment_position,
            solver_global_value,
            gram_faces,
            liouville_rows,
        });
    }
    Ok(diagnostics)
}

fn evaluate_occupation_gram(
    block: &crate::stationary_hausdorff::ExactGramBlock,
    matrix: &PackedPsdBlock,
    point: &[Complex64; BULK_VARIABLES],
    local_coordinate: f64,
) -> f64 {
    let basis_values = block
        .basis
        .iter()
        .map(|key| {
            let mut value = Complex64::new(local_coordinate.powi(i32::from(key.cost_power)), 0.0);
            for (variable, (&anti, &holo)) in key.anti.0.iter().zip(&key.holo.0).enumerate() {
                value *= point[variable].conj().powu(u32::from(anti));
                value *= point[variable].powu(u32::from(holo));
            }
            if reflection_phase_is_i(key, BULK_VARIABLES) {
                value *= Complex64::new(0.0, 1.0);
            }
            value
        })
        .collect::<Vec<_>>();
    let features = block
        .face
        .iter()
        .map(|column| {
            column
                .iter()
                .fold(Complex64::new(0.0, 0.0), |sum, &(position, weight)| {
                    sum + weight as f64 * basis_values[position]
                })
        })
        .collect::<Vec<_>>();
    let mut quadratic = 0.0;
    let mut packed = 0;
    for column in 0..matrix.side {
        for row in column..matrix.side {
            let product = features[row].conj() * features[column];
            quadratic += matrix.lower_triangle_column_major[packed]
                * if row == column {
                    product.re
                } else {
                    2.0 * product.re
                };
            packed += 1;
        }
    }
    let support = block
        .support
        .iter()
        .map(|&(power, weight)| weight as f64 * local_coordinate.powi(i32::from(power)))
        .sum::<f64>();
    support * quadratic
}

#[allow(clippy::too_many_arguments)]
fn integrate_piece(
    moments: &mut [f64],
    basis: &[CostMonomial],
    cell: usize,
    grid: &SplitGrid,
    segment_start_exposure: f64,
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    lower_fraction: f64,
    upper_fraction: f64,
    quadrature: &[(f64, f64)],
    maximum_discarded: &mut f64,
) {
    if upper_fraction <= lower_fraction {
        return;
    }
    let lower_knot = rational_f64(grid.knots()[cell]);
    let width = rational_f64(grid.knots()[cell + 1]) - lower_knot;
    for &(node, weight) in quadrature {
        let fraction = lower_fraction + (upper_fraction - lower_fraction) * node;
        let point = trajectory_point(state, phase, segment_duration, fraction);
        let exposure = segment_start_exposure
            + segment_cost_integral(state, phase, segment_duration, fraction);
        let xi = (exposure / rational_f64(EXPOSURE_UPPER) - lower_knot) / width;
        let values = moment_values(basis, &point, xi, BULK_VARIABLES, maximum_discarded);
        let scale = segment_duration * (upper_fraction - lower_fraction) * weight;
        for (moment, value) in moments.iter_mut().zip(values) {
            *moment += scale * value;
        }
    }
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
            let mut value = xi.powi(i32::from(key.cost_power));
            let mut complex = Complex64::new(value, 0.0);
            for (variable, (&anti, &holo)) in key.anti.0.iter().zip(&key.holo.0).enumerate() {
                complex *= z[variable].conj().powu(u32::from(anti));
                complex *= z[variable].powu(u32::from(holo));
            }
            if reflection_phase_is_i(key, variables) {
                complex *= Complex64::new(0.0, -1.0);
            }
            *maximum_discarded = maximum_discarded.max(complex.im.abs());
            value = complex.re;
            value
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

fn crossing_fraction(
    state: &[Complex64; STATE_VARIABLES],
    phase: f64,
    segment_duration: f64,
    target_exposure: f64,
    lower_fraction: f64,
) -> f64 {
    let mut lower = lower_fraction;
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

#[derive(Clone, Copy, Debug, Serialize)]
pub struct SplitMonotonicityDiagnostic {
    pub split_objective: f64,
    pub monolithic_objective: f64,
    pub tolerance: f64,
    pub margin: f64,
    pub valid: bool,
}

pub fn split_monotonicity_diagnostic(
    split_objective: f64,
    monolithic_objective: f64,
    tolerance: f64,
) -> Result<SplitMonotonicityDiagnostic, String> {
    if !split_objective.is_finite()
        || !monolithic_objective.is_finite()
        || !tolerance.is_finite()
        || tolerance < 0.0
    {
        return Err(
            "monotonicity diagnostic inputs must be finite and tolerance nonnegative".into(),
        );
    }
    let margin = split_objective - monolithic_objective;
    Ok(SplitMonotonicityDiagnostic {
        split_objective,
        monolithic_objective,
        tolerance,
        margin,
        valid: margin >= -tolerance,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_and_canonicalizes_exact_split_grids() {
        let grid = "0,2/64,0.96875,1".parse::<SplitGrid>().unwrap();
        assert_eq!(grid.to_string(), "0,1/32,31/32,1");
        assert_eq!(grid.cell_count(), 3);
        assert_eq!(
            grid.inverse_widths().unwrap(),
            vec![32.into(), Rational::new(16, 15), 32.into()]
        );
        assert_eq!(grid.canonical_hash(), grid.clone().canonical_hash());

        for invalid in ["", "0", "1/32,1", "0,1/2", "0,1/2,1/2,1", "0,3/4,1/2,1"] {
            assert!(invalid.parse::<SplitGrid>().is_err(), "{invalid}");
        }
    }

    #[test]
    fn assembles_order_two_two_cell_problem() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let problem = assemble(2, &grid).unwrap();
        assert_eq!(problem.structure.cell_count, 2);
        assert_eq!(problem.conic.q.len(), 71);
        assert_eq!(problem.conic.cones[0], Cone::Zero(21));
        assert_eq!(
            problem
                .structure
                .psd_block_families
                .iter()
                .filter(|&&family| family == BlockFamily::InterfaceMoment)
                .count(),
            problem.structure.interface_moment_block_count_per_interface
        );
    }

    #[test]
    fn uncapped_order_two_assembly_is_byte_identical_to_the_v1_baseline() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let problem = assemble(2, &grid).unwrap();
        let bytes = serde_json::to_vec(&problem.conic).unwrap();
        assert_eq!(bytes.len(), 7256);
        assert_eq!(
            format!("{:x}", Sha256::digest(bytes)),
            "9cb31c14446f9f3dedf0aa4de90242b4642c03ca39482e77caedf8747bc95227"
        );
        let metadata = serde_json::to_value(problem.structure).unwrap();
        assert!(metadata.get("active_time_cap").is_none());
        assert!(metadata.get("bound_scope").is_none());
        assert!(metadata.get("active_time_cap_row_scaling").is_none());
    }

    #[test]
    fn active_time_cap_restores_full_moment_cones_and_adds_one_mass_inequality() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let baseline = assemble(2, &grid).unwrap();
        let capped = assemble_with_active_time_cap(2, &grid, 8.into()).unwrap();

        assert_eq!(capped.structure.active_time_cap.as_deref(), Some("8"));
        assert_eq!(
            capped.structure.bound_scope,
            Some(ACTIVE_TIME_CAPPED_BOUND_SCOPE)
        );
        assert_ne!(
            capped.structure.formulation_hash,
            baseline.structure.formulation_hash
        );
        assert!(capped.structure.sum_psd_squares > baseline.structure.sum_psd_squares);
        assert_eq!(capped.conic.cones.last(), Some(&Cone::Nonnegative(1)));
        assert_eq!(
            capped
                .conic
                .cones
                .iter()
                .filter(|cone| matches!(cone, Cone::Nonnegative(_)))
                .count(),
            1
        );
        assert_eq!(capped.conic.b.last(), Some(&1.0));

        let Cone::Zero(affine_rows) = baseline.conic.cones[0] else {
            panic!("baseline first cone is not the affine zero cone");
        };
        assert_eq!(capped.conic.cones[0], Cone::Zero(affine_rows));
        assert_eq!(capped.conic.q, baseline.conic.q);
        assert_eq!(
            &capped.conic.b[..affine_rows],
            &baseline.conic.b[..affine_rows]
        );
        assert_eq!(
            capped
                .conic
                .a
                .entries
                .iter()
                .filter(|entry| entry.0 < affine_rows)
                .collect::<Vec<_>>(),
            baseline
                .conic
                .a
                .entries
                .iter()
                .filter(|entry| entry.0 < affine_rows)
                .collect::<Vec<_>>()
        );

        let cap_row = capped.conic.a.rows - 1;
        let cap_entries = capped
            .conic
            .a
            .entries
            .iter()
            .filter(|entry| entry.0 == cap_row)
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(
            cap_entries,
            vec![
                (cap_row, 0, 1.0 / 8.0),
                (
                    cap_row,
                    capped.structure.occupation_moment_count_per_cell,
                    1.0 / 8.0
                ),
            ]
        );
        let rational_cap = active_time_capped_structure(2, &grid, Rational::new(45, 4)).unwrap();
        assert_eq!(rational_cap.active_time_cap.as_deref(), Some("45/4"));
        assert_eq!(rational_cap.occupation_variable_scale.as_deref(), Some("1"));
        assert_eq!(
            active_time_capped_structure(2, &grid, 100.into())
                .unwrap()
                .occupation_variable_scale
                .as_deref(),
            Some("1")
        );
        assert_eq!(
            active_time_capped_structure(2, &grid, 10_000_000.into())
                .unwrap()
                .occupation_variable_scale
                .as_deref(),
            Some("10000")
        );
        assert!(assemble_with_active_time_cap(2, &grid, Rational::ZERO).is_err());

        let pulse: IdealBlockadePulse = serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap();
        let witness =
            diagnose_ideal_blockade_pulse_with_active_time_cap(2, &grid, &pulse, 8.into()).unwrap();
        assert_eq!(witness.active_time_cap.as_deref(), Some("8"));
        assert_eq!(witness.active_time_cap_feasible, Some(true));
        assert!((witness.active_time_cap_slack.unwrap() - (8.0 - pulse.duration)).abs() < 1e-12);
        let transported_mass = witness
            .cells
            .iter()
            .map(|cell| cell.occupation_moments[0])
            .sum::<f64>();
        assert!((transported_mass - pulse.duration).abs() < 1e-11);
    }

    #[test]
    fn equal_anisotropic_degree_reproduces_the_legacy_conic_exactly() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let legacy = assemble(3, &grid).unwrap();
        let anisotropic = assemble_anisotropic(3, 3, &grid).unwrap();
        assert_eq!(anisotropic.conic, legacy.conic);
        assert_eq!(
            anisotropic.structure.occupation_basis_hash,
            legacy.structure.occupation_basis_hash
        );
        assert_eq!(
            anisotropic.structure.liouville_basis_hash,
            legacy.structure.liouville_basis_hash
        );
        assert_eq!(
            anisotropic.structure.psd_block_sides,
            legacy.structure.psd_block_sides
        );
    }

    #[test]
    fn equal_control_degree_reproduces_the_legacy_conic_exactly() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let legacy = assemble(3, &grid).unwrap();
        let control = assemble_u_anisotropic(3, 3, &grid).unwrap();
        assert_eq!(control.conic, legacy.conic);
        assert_eq!(
            control.structure.occupation_basis_hash,
            legacy.structure.occupation_basis_hash
        );
        assert_eq!(
            control.structure.liouville_basis_hash,
            legacy.structure.liouville_basis_hash
        );
        assert_eq!(
            control.structure.psd_block_sides,
            legacy.structure.psd_block_sides
        );
    }

    #[test]
    fn exploratory_occupation_gram_extensions_are_nested() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let baseline = ExactSplitModel::create(3, &grid).unwrap();
        let control = ExactSplitModel::create_with_u_degree(3, 5, &grid).unwrap();
        assert!(
            baseline.base.moments().keys.iter().all(|key| control
                .base
                .moments()
                .keys
                .contains(key))
        );
        assert!(
            control
                .base
                .occupation_gram_dimensions()
                .iter()
                .sum::<usize>()
                > baseline
                    .base
                    .occupation_gram_dimensions()
                    .iter()
                    .sum::<usize>()
        );
        assert_ne!(
            u_anisotropic_structure(3, 5, &grid)
                .unwrap()
                .formulation_hash,
            structure(3, &grid).unwrap().formulation_hash
        );

        let charges = [(0, 0), (0, -1)];
        let localized =
            ExactSplitModel::create_with_rydberg_localizers(3, &grid, &charges).unwrap();
        assert!(
            baseline.base.moments().keys.iter().all(|key| localized
                .base
                .moments()
                .keys
                .contains(key))
        );
        assert_eq!(
            localized.base.occupation_blocks().len(),
            baseline.base.occupation_blocks().len() + 2 * charges.len()
        );
    }

    #[test]
    fn tracked_gap_coordinates_are_liouville_only_in_the_baseline_cone() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let order = 3;
        let exact = ExactSplitModel::create(order, &grid).unwrap();
        let tracked = [
            (&[0, 0, 0, 1, 0][..], &[1, 1, 1, 0, 0][..]),
            (&[0, 2, 0, 0, 0][..], &[1, 0, 0, 0, 1][..]),
        ];
        for (anti, holo) in tracked {
            let position = exact
                .base
                .moments()
                .keys
                .iter()
                .position(|key| key.cost_power == 0 && key.anti.0 == anti && key.holo.0 == holo)
                .unwrap();
            let mut gram_occurrences = 0;
            for (block_index, &side) in exact.base.occupation_gram_dimensions().iter().enumerate() {
                for column in 0..side {
                    for row in 0..=column {
                        exact.base.for_each_gram_entry_coefficient(
                            block_index,
                            row,
                            column,
                            |candidate, coefficient| {
                                if candidate == position && coefficient.to_f64() != 0.0 {
                                    gram_occurrences += 1;
                                }
                            },
                        );
                    }
                }
            }
            assert_eq!(gram_occurrences, 0);
            assert_eq!(
                exact
                    .rows
                    .iter()
                    .filter(|row| {
                        let target = exact.cell_offsets[row.cell] + position;
                        row.coefficients.iter().any(|&(candidate, coefficient)| {
                            candidate == target && coefficient.to_f64() != 0.0
                        })
                    })
                    .count(),
                3 * grid.cell_count()
            );
        }
    }

    #[test]
    fn higher_xi_degree_only_enlarges_the_weighted_split_space() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        assert!(anisotropic_structure(3, 2, &grid).is_err());

        let legacy = ExactSplitModel::create(3, &grid).unwrap();
        let anisotropic = AnisotropicSplitModel::create(3, 5, &grid).unwrap();
        assert!(
            legacy.base.moments().keys.iter().all(|key| anisotropic
                .base
                .moments()
                .keys
                .contains(key))
        );
        assert!(anisotropic.base.moments().keys.len() > legacy.base.moments().keys.len());
        assert!(anisotropic.rows.len() > legacy.rows.len());
        assert!(anisotropic.terminal_count > legacy.terminal_count);
        assert!(anisotropic.base.moments().keys.iter().all(|key| {
            let state_degree = u32::from(key.anti.degree() + key.holo.degree());
            state_degree * 5 + u32::from(key.cost_power) * 3 <= 2 * 3 * 5
        }));
    }

    #[test]
    fn split_structure_matches_order_two_and_four_goldens() {
        let grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        for (order, text) in [
            (
                2,
                include_str!("../../../golden/stationary-torus-hausdorff-split-order-2.json"),
            ),
            (
                4,
                include_str!("../../../golden/stationary-torus-hausdorff-split-order-4.json"),
            ),
        ] {
            let golden: serde_json::Value = serde_json::from_str(text).unwrap();
            let got = structure(order, &grid).unwrap();
            assert_eq!(serde_json::to_value(&got.knots).unwrap(), golden["knots"]);
            for (actual, name) in [
                (got.cell_count, "cell_count"),
                (
                    got.occupation_moment_count_per_cell,
                    "occupation_moment_count_per_cell",
                ),
                (got.occupation_moment_count, "occupation_moment_count"),
                (
                    got.interface_moment_count_per_interface,
                    "interface_moment_count_per_interface",
                ),
                (got.interface_moment_count, "interface_moment_count"),
                (got.terminal_moment_count, "terminal_moment_count"),
                (got.liouville_equality_count, "liouville_equality_count"),
                (got.psd_block_sides.len(), "psd_block_count"),
                (got.largest_psd_side, "largest_psd_side"),
                (got.sum_psd_squares, "sum_psd_squares"),
                (got.sum_psd_cubes, "sum_psd_cubes"),
            ] {
                assert_eq!(actual as u64, golden[name].as_u64().unwrap(), "{name}");
            }
            for (actual, name) in [
                (&got.split_grid_hash, "split_grid_hash"),
                (&got.occupation_basis_hash, "occupation_basis_hash"),
                (&got.interface_basis_hash, "interface_basis_hash"),
                (&got.terminal_basis_hash, "terminal_basis_hash"),
                (&got.liouville_basis_hash, "liouville_basis_hash"),
                (&got.formulation_hash, "formulation_hash"),
            ] {
                assert_eq!(actual, golden[name].as_str().unwrap(), "{name}");
            }
            assert_eq!(
                hash_json(&got.psd_block_sides),
                format!(
                    "sha256:{}",
                    golden["psd_block_sides_canonical_json_sha256"]
                        .as_str()
                        .unwrap()
                )
            );
            assert_eq!(
                hash_json(&got.psd_block_families),
                format!(
                    "sha256:{}",
                    golden["psd_block_families_canonical_json_sha256"]
                        .as_str()
                        .unwrap()
                )
            );
        }
        assert!(
            interface_gram_bases(4)
                .iter()
                .flatten()
                .all(|key| key.cost_power == 0)
        );
    }

    #[test]
    fn charge_enrichment_is_nested_and_leaves_default_hashes_unchanged() {
        let grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        let baseline = structure(3, &grid).unwrap();
        let enrichment = ChargeEnrichment::new(vec![(0, -1), (0, 0)], 1).unwrap();
        let enriched = enriched_structure(3, &grid, &enrichment).unwrap();
        assert_eq!(baseline.enrichment, None);
        assert_eq!(enriched.enrichment, Some(enrichment));
        assert_eq!(
            baseline.liouville_equality_count,
            enriched.liouville_equality_count
        );
        assert_eq!(baseline.liouville_basis_hash, enriched.liouville_basis_hash);
        assert!(enriched.occupation_moment_count > baseline.occupation_moment_count);
        assert!(enriched.sum_psd_cubes > baseline.sum_psd_cubes);
        assert_ne!(enriched.formulation_hash, baseline.formulation_hash);
    }

    #[test]
    fn integrates_split_witness_with_cellwise_liouville_balance() {
        let pulse: IdealBlockadePulse = serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap();
        let grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        let report = diagnose_ideal_blockade_pulse(4, &grid, &pulse).unwrap();
        assert_eq!(report.interfaces.len(), 2);
        assert_eq!(report.terminal_cell, 3);
        assert!((report.trajectory_objective - 2.935_885_902_112_58).abs() < 1e-12);
        assert!(
            report.maximum_liouville_residual < 1e-10,
            "{}",
            report.maximum_liouville_residual
        );
        assert_eq!(report.normalization_residual, 0.0);
    }

    #[test]
    fn integrates_split_witness_in_an_enlarged_xi_test_space() {
        let pulse: IdealBlockadePulse = serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap();
        let grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        let report = diagnose_ideal_blockade_pulse_anisotropic(4, 8, &grid, &pulse).unwrap();
        assert_eq!(report.xi_degree, Some(8));
        assert!((report.trajectory_objective - 2.935_885_902_112_58).abs() < 1e-12);
        assert!(
            report.maximum_liouville_residual < 1e-10,
            "{}",
            report.maximum_liouville_residual
        );
        assert_eq!(report.normalization_residual, 0.0);
    }

    #[test]
    fn integrates_witness_in_enriched_moment_space() {
        let pulse: IdealBlockadePulse = serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap();
        let grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        let enrichment = ChargeEnrichment::new(vec![(0, -1), (0, 0)], 1).unwrap();
        let report = diagnose_enriched_ideal_blockade_pulse(2, &grid, &pulse, &enrichment).unwrap();
        assert_eq!(report.enrichment, Some(enrichment));
        assert!((report.trajectory_objective - 2.935_885_902_112_58).abs() < 1e-12);
        assert!(report.maximum_liouville_residual < 1e-10);
        assert_eq!(report.normalization_residual, 0.0);
    }

    #[test]
    fn integrates_witness_in_exploratory_occupation_gram_extensions() {
        let pulse: IdealBlockadePulse = serde_json::from_str(include_str!(
            "../../../legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        ))
        .unwrap();
        let grid = "0,1/32,31/32,1".parse::<SplitGrid>().unwrap();
        let control = diagnose_u_anisotropic_ideal_blockade_pulse(3, 5, &grid, &pulse).unwrap();
        let localized =
            diagnose_rydberg_localized_ideal_blockade_pulse(3, &grid, &pulse, &[(0, 0), (0, -1)])
                .unwrap();
        for report in [control, localized] {
            assert!((report.trajectory_objective - 2.935_885_902_112_58).abs() < 1e-12);
            assert!(report.maximum_liouville_residual < 1e-10);
            assert_eq!(report.normalization_residual, 0.0);
        }
    }

    #[test]
    fn composed_space_contains_both_single_extensions() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let enrichment = ChargeEnrichment::new(vec![(0, -1), (0, 0)], 1).unwrap();
        let anisotropic = assemble_anisotropic(3, 5, &grid).unwrap();
        let enriched = assemble_enriched(3, &grid, &enrichment).unwrap();
        let composed = assemble_composed(3, 5, &grid, &enrichment).unwrap();

        assert_eq!(composed.structure.xi_degree, 5);
        assert_eq!(composed.structure.enrichment, Some(enrichment));
        assert!(composed.conic.q.len() >= anisotropic.conic.q.len());
        assert!(composed.conic.q.len() >= enriched.conic.q.len());
        assert!(composed.structure.sum_psd_cubes >= anisotropic.structure.sum_psd_cubes);
        assert!(composed.structure.sum_psd_cubes >= enriched.structure.sum_psd_cubes);
        assert_eq!(
            composed.structure.liouville_equality_count,
            anisotropic.structure.liouville_equality_count
        );
    }

    #[test]
    fn flags_a_split_monotonicity_violation() {
        assert!(
            split_monotonicity_diagnostic(2.9, 2.9 + 5e-7, 1e-6)
                .unwrap()
                .valid
        );
        assert!(
            !split_monotonicity_diagnostic(2.9, 2.9 + 2e-6, 1e-6)
                .unwrap()
                .valid
        );
    }
}
