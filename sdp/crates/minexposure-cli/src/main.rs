use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand, ValueEnum};
use minexposure_core::algebra::Rational;
use minexposure_core::assembly::{AssemblyKind, assemble};
use minexposure_core::certificate::{
    ExactTransport, FLOATING_GRAM_ENCODING, FloatingDualSolution, FloatingPsdBlock,
    FloatingPsdGrams, check_transport,
};
use minexposure_core::conic::{Cone, ConicProblem, adapter_regression_problem};
use minexposure_core::finite_blockade::{
    ColeParameters, FinitePulseArtifact, phase_objective, pulse_metrics, simulate_cole_all,
};
use minexposure_core::model::{ModelId, model};
use minexposure_core::provenance::{Artifact, audit};
use minexposure_core::stationary_certificate::{
    ExactAuditReport, ExactDualCertificate, SPLIT_EXACT_SCHEMA_V1,
    SPLIT_SHIFTED_SALVAGE_ERROR_SCHEMA_V1, ShiftedExactDualCertificate, ShiftedSalvageOutcome,
    SplitExactDualCertificate, SplitFaceBlock, SplitNativeBarFacePlan, SplitRotatedKernelState,
    SplitShiftedExactDualCertificate, SplitShiftedSalvageOutcome, apply_split_cone_repair,
    audit_exact_certificate, audit_exact_certificate_with_jobs, audit_shifted_exact_certificate,
    audit_shifted_exact_certificate_with_jobs, audit_split_exact_certificate,
    audit_split_exact_certificate_with_jobs, audit_split_shifted_exact_certificate,
    audit_split_shifted_exact_certificate_with_jobs, augment_split_rotated_kernels_with_zero_rows,
    blend_with_exact_seed, build_split_bar_cone_repair_problem_scaled,
    build_split_bar_cone_repair_problem_scaled_restricted, build_split_native_bar_face_plan,
    check_split_exact_affine_closure, check_split_exact_kernel_closure, export_split_repair_system,
    minimum_reconstructed_split_gram_eigenvalue, project_split_grams_to_rotated_kernels,
    repair_exact_identity, repair_split_exact_identity_componentwise_with_support,
    repair_split_exact_identity_on_faces, repair_split_exact_identity_ordered,
    repair_split_exact_identity_restricted, repair_split_exact_identity_with_support,
    residual_diagnostics, salvage_exact_shifted_certificate,
    salvage_exact_shifted_certificate_with_jobs, salvage_split_shifted_exact_certificate,
    salvage_split_shifted_exact_certificate_with_jobs, select_split_rotated_gram_kernels,
    split_near_null_eigen_diagnostics, split_shifted_original_identity_is_exact,
    validate_split_rotated_gram_kernels, zero_small_split_gram_rows,
};
use minexposure_core::stationary_cost_rate_split::{self, RateGrid};
use minexposure_core::stationary_hausdorff::{self, ChargeEnrichment};
use minexposure_core::stationary_hausdorff_split::{self, SplitGrid};
use minexposure_core::stationary_torus;
use minexposure_core::{estimate, result::RigorStatus};
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(version, about = "Canonical minimum-exposure moment/SOS tooling")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(serde::Deserialize)]
struct SplitFloatingSeed {
    problem: SplitFloatingSeedProblem,
    #[serde(flatten)]
    dual: FloatingDualSolution,
    #[serde(default)]
    interior_margin: Option<serde_json::Value>,
    #[serde(default)]
    primal_objective: Option<f64>,
    #[serde(default)]
    dual_objective: Option<f64>,
}

#[derive(serde::Deserialize)]
struct SplitFloatingSeedProblem {
    order: u8,
    knots: Vec<String>,
    split_grid_hash: String,
    formulation_hash: String,
    #[serde(default)]
    active_time_cap: Option<String>,
    #[serde(default)]
    bound_scope: Option<String>,
}

#[derive(Clone, Copy, ValueEnum)]
enum Kind {
    Primal,
    Dual,
}

#[derive(Subcommand)]
enum Command {
    /// Print an exact model schema.
    Model { model: ModelId },
    /// Deterministic preflight estimate.
    Estimate {
        model: ModelId,
        #[arg(long)]
        order: u8,
        /// Exact rational cumulative-cost knots for the split Hausdorff lane.
        #[arg(long)]
        knots: Option<String>,
        /// Exact rational running-cost-rate knots from 0 through 3/4.
        #[arg(long, requires = "knots")]
        rate_knots: Option<String>,
        /// Weighted Gram-basis degree in local xi; split lane only and at least --order.
        #[arg(long)]
        xi_degree: Option<u8>,
        /// Comma-separated charge sectors in FIRST:SECOND syntax (split lane only).
        #[arg(long, value_name = "LIST", requires = "enrich_degree")]
        enrich_charges: Option<String>,
        /// Extra Gram degree (1 or 2) for --enrich-charges.
        #[arg(long, value_name = "D", requires = "enrich_charges")]
        enrich_degree: Option<u8>,
        /// Weighted control-harmonic degree; exploratory split lane only.
        #[arg(long, value_name = "K", conflicts_with_all = ["xi_degree", "enrich_charges"])]
        u_degree: Option<u8>,
        /// Charge sectors receiving |r1|^2 and |r2|^2 product localizers.
        #[arg(
            long,
            value_name = "LIST",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree"]
        )]
        rydberg_localizer_charges: Option<String>,
    },
    /// Export canonical assembly metadata and hashes.
    Export {
        model: ModelId,
        #[arg(long)]
        order: u8,
        #[arg(long)]
        kappa: Option<String>,
        #[arg(long)]
        horizon: Option<String>,
        /// Exact rational cumulative-cost knots for the split Hausdorff lane.
        #[arg(long)]
        knots: Option<String>,
        /// Exact rational running-cost-rate knots from 0 through 3/4.
        #[arg(long, requires = "knots")]
        rate_knots: Option<String>,
        /// Weighted Gram-basis degree in local xi; split lane only and at least --order.
        #[arg(long)]
        xi_degree: Option<u8>,
        /// Comma-separated charge sectors in FIRST:SECOND syntax (split lane only).
        #[arg(long, value_name = "LIST", requires = "enrich_degree")]
        enrich_charges: Option<String>,
        /// Extra Gram degree (1 or 2) for --enrich-charges.
        #[arg(long, value_name = "D", requires = "enrich_charges")]
        enrich_degree: Option<u8>,
        #[arg(long, value_enum, default_value = "primal")]
        kind: Kind,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Solve a natively assembled discovery problem with Clarabel.rs.
    SolveClarabel {
        model: Option<ModelId>,
        #[arg(long)]
        order: Option<u8>,
        #[arg(long)]
        kappa: Option<String>,
        #[arg(long)]
        horizon: Option<String>,
        /// Exact rational cumulative-cost knots for the split Hausdorff lane.
        #[arg(long)]
        knots: Option<String>,
        /// Exact rational running-cost-rate knots from 0 through 3/4.
        #[arg(long, requires = "knots")]
        rate_knots: Option<String>,
        /// Weighted Gram-basis degree in local xi; split lane only and at least --order.
        #[arg(long)]
        xi_degree: Option<u8>,
        /// Comma-separated charge sectors in FIRST:SECOND syntax (split lane only).
        #[arg(long, value_name = "LIST", requires = "enrich_degree")]
        enrich_charges: Option<String>,
        /// Extra Gram degree (1 or 2) for --enrich-charges.
        #[arg(long, value_name = "D", requires = "enrich_charges")]
        enrich_degree: Option<u8>,
        /// Weighted control-harmonic degree; exploratory split lane only.
        #[arg(
            long,
            value_name = "K",
            conflicts_with_all = ["xi_degree", "enrich_charges", "active_time_cap"]
        )]
        u_degree: Option<u8>,
        /// Charge sectors receiving |r1|^2 and |r2|^2 product localizers.
        #[arg(
            long,
            value_name = "LIST",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree", "active_time_cap"]
        )]
        rydberg_localizer_charges: Option<String>,
        /// Total active-time cap sum_j mu_j[1] (split lane only; not all-duration).
        #[arg(
            long,
            value_name = "RATIONAL",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree", "rydberg_localizer_charges"]
        )]
        active_time_cap: Option<String>,
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Include dual PSD Gram matrices in the JSON result.
        #[arg(long)]
        dump_solution: bool,
    },
    /// Solve the same native Rust problem through the official MOSEK crate.
    SolveMosek {
        model: Option<ModelId>,
        #[arg(long)]
        order: Option<u8>,
        #[arg(long)]
        kappa: Option<String>,
        #[arg(long)]
        horizon: Option<String>,
        /// Exact rational cumulative-cost knots for the split Hausdorff lane.
        #[arg(long)]
        knots: Option<String>,
        /// Exact rational running-cost-rate knots from 0 through 3/4.
        #[arg(long, requires = "knots")]
        rate_knots: Option<String>,
        /// Weighted Gram-basis degree in local xi; split lane only and at least --order.
        #[arg(long)]
        xi_degree: Option<u8>,
        /// Comma-separated charge sectors in FIRST:SECOND syntax (split lane only).
        #[arg(long, value_name = "LIST", requires = "enrich_degree")]
        enrich_charges: Option<String>,
        /// Extra Gram degree (1 or 2) for --enrich-charges.
        #[arg(long, value_name = "D", requires = "enrich_charges")]
        enrich_degree: Option<u8>,
        /// Weighted control-harmonic degree; exploratory split lane only.
        #[arg(
            long,
            value_name = "K",
            conflicts_with_all = ["xi_degree", "enrich_charges", "active_time_cap"]
        )]
        u_degree: Option<u8>,
        /// Charge sectors receiving |r1|^2 and |r2|^2 product localizers.
        #[arg(
            long,
            value_name = "LIST",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree", "active_time_cap"]
        )]
        rydberg_localizer_charges: Option<String>,
        /// Total active-time cap sum_j mu_j[1] (split lane only; not all-duration).
        #[arg(
            long,
            value_name = "RATIONAL",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree", "rydberg_localizer_charges"]
        )]
        active_time_cap: Option<String>,
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Include dual PSD Gram matrices in the JSON result.
        #[arg(long)]
        dump_solution: bool,
        /// Write primal moments and dual multipliers for trajectory diagnostics.
        #[arg(long, value_name = "PATH")]
        diagnostic_dump: Option<PathBuf>,
        /// Stream the complete MOSEK optimizer transcript to stderr.
        #[arg(long)]
        solver_log: bool,
        /// Tighten native conic feasibility and relative-gap tolerances to 1e-10.
        #[arg(long)]
        strict: bool,
        /// Fix the split-dual bound and maximize a common Gram eigenvalue margin.
        #[arg(long, value_name = "RATIONAL")]
        interior_target: Option<String>,
        /// Floating split seed used to exclude numerically zero Gram faces.
        #[arg(long, value_name = "PATH", requires = "interior_target")]
        interior_reference: Option<PathBuf>,
        /// Reference blocks at or below this entry norm receive no margin shift.
        #[arg(long, default_value_t = 0.0, requires = "interior_target")]
        interior_zero_gram_threshold: f64,
        /// Also restrict shifts to reference Grams above this minimum eigenvalue.
        #[arg(long, value_name = "FLOAT", requires = "interior_reference")]
        interior_reference_eigenvalue_threshold: Option<f64>,
        /// Maximize a nonnegative margin for each active Gram instead of one common margin.
        #[arg(long, requires = "interior_target")]
        interior_per_block_margins: bool,
        /// Upper bound for each per-block margin (prevents unbounded sum objectives).
        #[arg(long, value_name = "FLOAT", requires = "interior_per_block_margins")]
        interior_margin_cap: Option<f64>,
        /// Exactification candidate whose selected repair support defines active Grams.
        #[arg(
            long,
            value_name = "PATH",
            requires = "interior_target",
            conflicts_with = "interior_reference"
        )]
        interior_active_gram_support: Option<PathBuf>,
    },
    /// Solve and round a stationary-torus dual into an exact cost-relative certificate.
    ExactifyStationary {
        #[arg(long)]
        order: u8,
        #[arg(long)]
        target: String,
        #[arg(long, default_value_t = 44)]
        dyadic_bits: u32,
        #[arg(long, default_value_t = 4096)]
        gram_shift_ulps: u64,
        #[arg(long)]
        seed: Option<PathBuf>,
        #[arg(long, default_value = "993/1000")]
        blend: String,
        #[arg(long, default_value = "0")]
        residual_upper: String,
        #[arg(short, long)]
        output: PathBuf,
    },
    /// Round and exactly repair a floating cumulative-cost split dual.
    ExactifyHausdorffSplit {
        /// JSON from solve-mosek --dump-solution for the same split model.
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        order: u8,
        /// Exact rational cumulative-cost knots.
        #[arg(long)]
        knots: String,
        #[arg(long)]
        target: String,
        #[arg(long, default_value_t = 44)]
        dyadic_bits: u32,
        #[arg(long, default_value_t = 4096)]
        gram_shift_ulps: u64,
        /// Zero entire numerically inactive Gram blocks before exact repair.
        #[arg(long, default_value_t = 1e-9)]
        zero_gram_threshold: f64,
        /// Diagnose an interior seed with the full nonzero Gram repair graph.
        #[arg(long, conflicts_with = "face_correction_cutoff")]
        unrestricted_repair: bool,
        /// Require a PSD-constrained restricted-graph correction with this reconstructed margin.
        #[arg(long, default_value_t = 0.0)]
        cone_margin: f64,
        /// Scale and validated upper bound for the fixed common cone-repair margin.
        #[arg(long, default_value_t = 1e-4)]
        cone_margin_cap: f64,
        /// Target row scale for the native-bar PSD constraints.
        #[arg(long, default_value_t = 1e-4)]
        cone_gram_scale_target: f64,
        /// Exactly zero Gram rows whose reconstructed diagonal is at most this value.
        #[arg(long, default_value_t = 0.0)]
        cone_facial_zero_threshold: f64,
        /// Impose exact rotated Gram kernels for eligible eigenvalues below this value.
        #[arg(long, default_value_t = 0.0)]
        cone_facial_rotation_threshold: f64,
        /// Dyadic precision for exact rotated Gram kernel vectors.
        #[arg(long, default_value_t = 30)]
        cone_facial_rotation_bits: u32,
        /// Recompute rotated Gram kernels before every cone pass instead of freezing them.
        #[arg(long, requires = "cone_facial_rotation_threshold")]
        cone_facial_rotation_recompute_each_pass: bool,
        /// Dyadic bits used when checkpointing the floating cone correction.
        #[arg(long, default_value_t = 52)]
        cone_correction_bits: u32,
        /// Stream the cone-repair MOSEK transcript to stderr.
        #[arg(long)]
        cone_solver_log: bool,
        /// Interior-point iteration cap for each advisory cone-repair solve.
        #[arg(long, default_value_t = 30)]
        cone_max_iterations: i32,
        /// Resume from the exact pre-cone checkpoint already at --output.
        #[arg(long)]
        resume: bool,
        /// Resume exact affine closure from the post-cone candidate at --output.
        #[arg(long)]
        resume_exact_closure: bool,
        /// Exit after the durable pre-cone exact closure; rerun with --resume.
        #[arg(long)]
        checkpoint_before_cone: bool,
        /// Exit after checkpointing one non-final cone pass; rerun with --resume.
        #[arg(long)]
        checkpoint_after_cone_pass: bool,
        /// Exit after exact closure and its reconstructed-PSD gate, before native audit.
        #[arg(long)]
        checkpoint_before_native_audit: bool,
        /// Reuse the first cone-repair solver result retained in another candidate.
        #[arg(long)]
        cone_solution_from: Option<PathBuf>,
        /// JSON array of repair-pool variable indices (from --export-repair-data)
        /// offered to the exact repair basis selection first.
        #[arg(long)]
        repair_preference: Option<PathBuf>,
        /// Export the assembled exact repair system (residual, sparse columns,
        /// block margins) as JSON for offline LP support selection.
        #[arg(long)]
        export_repair_data: Option<PathBuf>,
        /// Restrict exact Gram corrections to numerical positive eigenspaces above this cutoff.
        #[arg(long, value_name = "FLOAT")]
        face_correction_cutoff: Option<f64>,
        /// Dyadic precision for exactly rounded face bases.
        #[arg(long, default_value_t = 30)]
        face_basis_bits: u32,
        /// Positive seed eigenvalue assigned to admitted near-null or negative face modes.
        #[arg(long, default_value_t = 1e-10)]
        face_eigenvalue_floor: f64,
        /// Build and span-check the exact faces but apply no affine correction.
        #[arg(long, requires = "face_correction_cutoff")]
        face_zero_correction: bool,
        /// Stop face rank selection at a span established by a prior complete scan.
        #[arg(long, value_name = "RANK", requires = "face_correction_cutoff")]
        face_known_span: Option<usize>,
        #[arg(short, long)]
        output: PathBuf,
    },
    /// Check an exact certificate transport contract.
    CertificateCheck {
        path: PathBuf,
        #[arg(long)]
        free_time: bool,
    },
    /// Independently audit a JAN22 exact Q(sqrt(2)) dual without an optimizer.
    AuditExact {
        path: PathBuf,
        /// Number of independent Gram blocks to audit concurrently.
        #[arg(long)]
        audit_jobs: Option<usize>,
    },
    /// Audit the separate split Hausdorff exact schema without an optimizer.
    AuditExactSplit {
        path: PathBuf,
        /// Number of independent Gram blocks to audit concurrently.
        #[arg(long)]
        audit_jobs: Option<usize>,
    },
    /// Audit sound shift-and-discount salvage without an optimizer.
    AuditExactShifted {
        path: PathBuf,
        /// Number of independent Gram blocks to audit concurrently.
        #[arg(long)]
        audit_jobs: Option<usize>,
    },
    /// Convert an identity-closed failed monolithic v1 candidate by exact shifts.
    SalvageExactShifted {
        input: PathBuf,
        #[arg(short, long)]
        output: PathBuf,
        /// Number of independent Gram blocks in the final audit.
        #[arg(long)]
        audit_jobs: Option<usize>,
    },
    /// Audit a sound shifted wrapper around the separate split v1 schema.
    AuditExactSplitShifted {
        path: PathBuf,
        /// Number of independent Gram blocks to audit concurrently.
        #[arg(long)]
        audit_jobs: Option<usize>,
    },
    /// Convert an identity-closed failed split v1 candidate by exact shifts.
    SalvageExactSplitShifted {
        input: PathBuf,
        #[arg(short, long)]
        output: PathBuf,
        /// Number of independent Gram blocks in the search and final audit.
        #[arg(long)]
        audit_jobs: Option<usize>,
    },
    /// Verify every immutable imported artifact.
    ProvenanceAudit {
        #[arg(default_value = "provenance/artifacts.json")]
        manifest: PathBuf,
    },
    /// Emit stable constants for later Lean consumption.
    LeanConstants {
        #[arg(short, long, default_value = "generated/MinExposureConstants.lean")]
        output: PathBuf,
    },
    /// Reproduce the finite-blockade Cole pi-2pi-pi protocol natively in Rust.
    SimulateCole {
        #[arg(long, default_value_t = 36.0756)]
        v_rb_cs_mhz: f64,
        #[arg(long, default_value_t = 0.04420)]
        v_rb_rb_mhz: f64,
        #[arg(long, default_value_t = 1.0)]
        cs_to_rb_ratio: f64,
    },
    /// Print the rigorous finite-blockade CZZ exposure floors.
    FiniteExposureFloor {
        #[arg(long)]
        v_mhz: f64,
    },
    /// Reproduce a finite-blockade piecewise-constant pulse and its exposure.
    ReproduceFinitePulse {
        #[arg(
            default_value = "legacy/finite-677eba8/results/grape_phase_rate/jandura99_omega18_czz_81p5444ns_n99_v1.json"
        )]
        path: PathBuf,
    },
    /// Evaluate the native analytic phase/amplitude GRAPE gradient.
    FinitePulseGradient {
        #[arg(
            default_value = "legacy/finite-677eba8/results/grape_phase_rate/jandura99_omega18_czz_81p5444ns_n99_v1.json"
        )]
        path: PathBuf,
    },
    /// Integrate an ideal-blockade pulse in stationary-torus coordinates.
    DiagnoseStationaryPulse {
        #[arg(long)]
        order: u8,
        #[arg(
            long,
            default_value = "legacy/finite-d59e299/verification/reference_data/jan22_cz_exposure_candidate_396.json"
        )]
        pulse: PathBuf,
        /// Optional JSON produced by solve-mosek --diagnostic-dump.
        #[arg(long)]
        solution: Option<PathBuf>,
        /// Also transport the witness through this exact rational split grid.
        #[arg(long)]
        knots: Option<String>,
        /// Also partition the witness by these exact running-cost-rate knots.
        #[arg(long, requires = "knots")]
        rate_knots: Option<String>,
        /// Use the anisotropic split test space with this local-xi Gram degree.
        #[arg(long)]
        xi_degree: Option<u8>,
        /// Comma-separated charge sectors in FIRST:SECOND syntax (split lane only).
        #[arg(long, value_name = "LIST", requires = "enrich_degree")]
        enrich_charges: Option<String>,
        /// Extra Gram degree (1 or 2) for --enrich-charges.
        #[arg(long, value_name = "D", requires = "enrich_charges")]
        enrich_degree: Option<u8>,
        /// Weighted control-harmonic degree; exploratory split lane only.
        #[arg(
            long,
            value_name = "K",
            conflicts_with_all = ["xi_degree", "enrich_charges", "active_time_cap"]
        )]
        u_degree: Option<u8>,
        /// Charge sectors receiving |r1|^2 and |r2|^2 product localizers.
        #[arg(
            long,
            value_name = "LIST",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree", "active_time_cap"]
        )]
        rydberg_localizer_charges: Option<String>,
        /// Check feasibility against this total active-time cap (split lane only).
        #[arg(
            long,
            value_name = "RATIONAL",
            conflicts_with_all = ["xi_degree", "enrich_charges", "u_degree", "rydberg_localizer_charges"]
        )]
        active_time_cap: Option<String>,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

fn json(value: &impl serde::Serialize) -> Result<String> {
    Ok(serde_json::to_string_pretty(value)? + "\n")
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Model { model: id } => print!("{}", json(&model(id))?),
        Command::Estimate {
            model,
            order,
            knots,
            rate_knots,
            xi_degree,
            enrich_charges,
            enrich_degree,
            u_degree,
            rydberg_localizer_charges,
        } => {
            let estimate = if model == ModelId::StationaryTorusHausdorffSplit {
                let grid = parse_required_split_grid(knots)?;
                if let Some(rate_knots) = rate_knots {
                    reject_rate_split_extensions(xi_degree, enrich_charges, enrich_degree)?;
                    reject_new_split_options(u_degree, rydberg_localizer_charges)?;
                    let rate_grid = parse_rate_grid(&rate_knots)?;
                    stationary_cost_rate_split::estimate(order, &grid, &rate_grid)
                        .map_err(anyhow::Error::msg)?
                } else {
                    let enrichment = parse_charge_enrichment(enrich_charges, enrich_degree)?;
                    let rydberg_localizers = parse_charge_selection(rydberg_localizer_charges)?;
                    match (
                        xi_degree,
                        enrichment.as_ref(),
                        u_degree,
                        rydberg_localizers.as_deref(),
                    ) {
                        (Some(xi_degree), Some(enrichment), None, None) => {
                            stationary_hausdorff_split::composed_estimate(
                                order, xi_degree, &grid, enrichment,
                            )
                        }
                        (Some(xi_degree), None, None, None) => {
                            stationary_hausdorff_split::anisotropic_estimate(
                                order, xi_degree, &grid,
                            )
                        }
                        (None, Some(enrichment), None, None) => {
                            stationary_hausdorff_split::enriched_estimate(order, &grid, enrichment)
                        }
                        (None, None, Some(u_degree), None) => {
                            stationary_hausdorff_split::u_anisotropic_estimate(
                                order, u_degree, &grid,
                            )
                        }
                        (None, None, None, Some(charges)) => {
                            stationary_hausdorff_split::rydberg_localized_estimate(
                                order, &grid, charges,
                            )
                        }
                        (None, None, None, None) => {
                            stationary_hausdorff_split::estimate(order, &grid)
                        }
                        _ => Err("incompatible exploratory split strengthening flags".into()),
                    }
                    .map_err(anyhow::Error::msg)?
                }
            } else {
                reject_new_split_options(u_degree, rydberg_localizer_charges)?;
                reject_irrelevant_split_options(
                    knots,
                    rate_knots,
                    xi_degree,
                    enrich_charges,
                    enrich_degree,
                )?;
                estimate(model, order).map_err(anyhow::Error::msg)?
            };
            print!("{}", json(&estimate)?);
        }
        Command::Export {
            model,
            order,
            kappa,
            horizon,
            knots,
            rate_knots,
            xi_degree,
            enrich_charges,
            enrich_degree,
            kind,
            output,
        } => {
            let kind = match kind {
                Kind::Primal => AssemblyKind::OccupationPrimal,
                Kind::Dual => AssemblyKind::HjbDual,
            };
            let text = if model == ModelId::FiniteCzFixedKappa {
                reject_irrelevant_split_options(
                    knots,
                    rate_knots,
                    xi_degree,
                    enrich_charges,
                    enrich_degree,
                )?;
                if kind != AssemblyKind::OccupationPrimal {
                    bail!("finite_cz_fixed_kappa currently exports the occupation primal only")
                }
                let kappa = kappa
                    .context("finite_cz_fixed_kappa export requires --kappa")?
                    .parse::<Rational>()
                    .map_err(anyhow::Error::msg)?;
                let horizon = horizon
                    .context("finite_cz_fixed_kappa export requires --horizon")?
                    .parse::<Rational>()
                    .map_err(anyhow::Error::msg)?;
                let problem = minexposure_core::finite_sdp::assemble(order, kappa, horizon)
                    .map_err(anyhow::Error::msg)?;
                json(&problem.structure)?
            } else if model == ModelId::StationaryTorusHausdorffSplit {
                if kappa.is_some() || horizon.is_some() {
                    bail!("--kappa and --horizon do not apply to stationary_torus_hausdorff_split")
                }
                let grid = parse_required_split_grid(knots)?;
                if let Some(rate_knots) = rate_knots {
                    reject_rate_split_extensions(xi_degree, enrich_charges, enrich_degree)?;
                    let rate_grid = parse_rate_grid(&rate_knots)?;
                    json(
                        &stationary_cost_rate_split::structure(order, &grid, &rate_grid)
                            .map_err(anyhow::Error::msg)?,
                    )?
                } else {
                    let enrichment = parse_charge_enrichment(enrich_charges, enrich_degree)?;
                    match (xi_degree, enrichment.as_ref()) {
                        (Some(xi_degree), Some(enrichment)) => json(
                            &stationary_hausdorff_split::composed_structure(
                                order, xi_degree, &grid, enrichment,
                            )
                            .map_err(anyhow::Error::msg)?,
                        )?,
                        (Some(xi_degree), None) => json(
                            &stationary_hausdorff_split::anisotropic_structure(
                                order, xi_degree, &grid,
                            )
                            .map_err(anyhow::Error::msg)?,
                        )?,
                        (None, Some(enrichment)) => json(
                            &stationary_hausdorff_split::enriched_structure(
                                order, &grid, enrichment,
                            )
                            .map_err(anyhow::Error::msg)?,
                        )?,
                        (None, None) => json(
                            &stationary_hausdorff_split::structure(order, &grid)
                                .map_err(anyhow::Error::msg)?,
                        )?,
                    }
                }
            } else {
                reject_irrelevant_split_options(
                    knots,
                    rate_knots,
                    xi_degree,
                    enrich_charges,
                    enrich_degree,
                )?;
                if kappa.is_some() || horizon.is_some() {
                    bail!("--kappa and --horizon apply only to finite_cz_fixed_kappa")
                }
                json(&assemble(model, order, kind).map_err(anyhow::Error::msg)?)?
            };
            if let Some(path) = output {
                if let Some(parent) = path.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::write(path, text)?;
            } else {
                print!("{text}");
            }
        }
        Command::SolveClarabel {
            model,
            order,
            kappa,
            horizon,
            knots,
            rate_knots,
            xi_degree,
            enrich_charges,
            enrich_degree,
            u_degree,
            rydberg_localizer_charges,
            active_time_cap,
            output,
            dump_solution,
        } => {
            let (problem, metadata) = solver_problem(
                model,
                order,
                kappa,
                horizon,
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
                u_degree,
                rydberg_localizer_charges,
                active_time_cap,
                dump_solution,
            )?;
            write_solver_result(output, solve_clarabel(&problem, metadata, dump_solution)?)?
        }
        Command::SolveMosek {
            model,
            order,
            kappa,
            horizon,
            knots,
            rate_knots,
            xi_degree,
            enrich_charges,
            enrich_degree,
            u_degree,
            rydberg_localizer_charges,
            active_time_cap,
            output,
            dump_solution,
            diagnostic_dump,
            solver_log,
            strict,
            interior_target,
            interior_reference,
            interior_zero_gram_threshold,
            interior_reference_eigenvalue_threshold,
            interior_per_block_margins,
            interior_margin_cap,
            interior_active_gram_support,
        } => {
            let mut interior_target = interior_target
                .map(|target| {
                    parse_interior_margin_target(
                        model,
                        dump_solution,
                        &target,
                        interior_zero_gram_threshold,
                        interior_reference_eigenvalue_threshold,
                        interior_per_block_margins,
                        interior_margin_cap,
                    )
                })
                .transpose()?;
            if interior_target.is_some() && diagnostic_dump.is_some() {
                bail!("--interior-target cannot be combined with --diagnostic-dump")
            }
            let (problem, metadata) = solver_problem(
                model,
                order,
                kappa,
                horizon,
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
                u_degree,
                rydberg_localizer_charges,
                active_time_cap,
                dump_solution,
            )?;
            if let (Some(target), Some(reference)) = (&mut interior_target, interior_reference) {
                target.load_active_grams(&reference, &problem, &metadata)?;
            }
            if let (Some(target), Some(support)) =
                (&mut interior_target, interior_active_gram_support)
            {
                target.load_active_gram_support(&support, &problem, &metadata)?;
            }
            write_solver_result(
                output,
                solve_mosek(
                    &problem,
                    metadata,
                    dump_solution,
                    diagnostic_dump.as_deref(),
                    solver_log,
                    strict,
                    interior_target.as_ref(),
                )?,
            )?
        }
        Command::ExactifyStationary {
            order,
            target,
            dyadic_bits,
            gram_shift_ulps,
            seed,
            blend,
            residual_upper,
            output,
        } => exactify_stationary(
            order,
            target,
            dyadic_bits,
            gram_shift_ulps,
            seed,
            blend,
            residual_upper,
            output,
        )?,
        Command::ExactifyHausdorffSplit {
            input,
            order,
            knots,
            target,
            dyadic_bits,
            gram_shift_ulps,
            zero_gram_threshold,
            unrestricted_repair,
            cone_margin,
            cone_margin_cap,
            cone_gram_scale_target,
            cone_facial_zero_threshold,
            cone_facial_rotation_threshold,
            cone_facial_rotation_bits,
            cone_facial_rotation_recompute_each_pass,
            cone_correction_bits,
            cone_solver_log,
            cone_max_iterations,
            resume,
            resume_exact_closure,
            checkpoint_before_cone,
            checkpoint_after_cone_pass,
            checkpoint_before_native_audit,
            cone_solution_from,
            repair_preference,
            export_repair_data,
            face_correction_cutoff,
            face_basis_bits,
            face_eigenvalue_floor,
            face_zero_correction,
            face_known_span,
            output,
        } => exactify_hausdorff_split(
            &input,
            order,
            &knots,
            target,
            dyadic_bits,
            gram_shift_ulps,
            zero_gram_threshold,
            unrestricted_repair,
            cone_margin,
            cone_margin_cap,
            cone_gram_scale_target,
            cone_facial_zero_threshold,
            cone_facial_rotation_threshold,
            cone_facial_rotation_bits,
            cone_facial_rotation_recompute_each_pass,
            cone_correction_bits,
            cone_solver_log,
            cone_max_iterations,
            resume,
            resume_exact_closure,
            checkpoint_before_cone,
            checkpoint_after_cone_pass,
            checkpoint_before_native_audit,
            cone_solution_from.as_deref(),
            repair_preference.as_deref(),
            export_repair_data.as_deref(),
            face_correction_cutoff,
            face_basis_bits,
            face_eigenvalue_floor,
            face_zero_correction,
            face_known_span,
            &output,
        )?,
        Command::CertificateCheck { path, free_time } => {
            let certificate: ExactTransport = serde_json::from_slice(&fs::read(path)?)?;
            let report = check_transport(&certificate, free_time);
            print!("{}", json(&report)?);
            if !report.valid {
                std::process::exit(2);
            }
        }
        Command::AuditExact { path, audit_jobs } => {
            let certificate: ExactDualCertificate = serde_json::from_slice(&fs::read(path)?)?;
            let report = match audit_jobs {
                Some(jobs) => audit_exact_certificate_with_jobs(&certificate, jobs)?,
                None => audit_exact_certificate(&certificate)?,
            };
            print!("{}", json(&report)?);
        }
        Command::AuditExactSplit { path, audit_jobs } => {
            let certificate: SplitExactDualCertificate = serde_json::from_slice(&fs::read(path)?)?;
            let report = match audit_jobs {
                Some(jobs) => audit_split_exact_certificate_with_jobs(&certificate, jobs)?,
                None => audit_split_exact_certificate(&certificate)?,
            };
            print!("{}", json(&report)?);
        }
        Command::AuditExactShifted { path, audit_jobs } => {
            let certificate: ShiftedExactDualCertificate =
                serde_json::from_slice(&fs::read(path)?)?;
            let report = match audit_jobs {
                Some(jobs) => audit_shifted_exact_certificate_with_jobs(&certificate, jobs)?,
                None => audit_shifted_exact_certificate(&certificate)?,
            };
            print!("{}", json(&report)?);
        }
        Command::SalvageExactShifted {
            input,
            output,
            audit_jobs,
        } => {
            if input == output
                || (output.exists() && fs::canonicalize(&input)? == fs::canonicalize(&output)?)
            {
                bail!("shifted output must not overwrite the monolithic v1 input")
            }
            let original_bytes = fs::read(&input)?;
            let original: ExactDualCertificate = serde_json::from_slice(&original_bytes)?;
            let outcome = match audit_jobs {
                Some(jobs) => salvage_exact_shifted_certificate_with_jobs(original, jobs),
                None => salvage_exact_shifted_certificate(original),
            }
            .context("could not salvage the identity-closed monolithic candidate")?;
            if let Some(parent) = output.parent() {
                fs::create_dir_all(parent)?;
            }
            match outcome {
                ShiftedSalvageOutcome::Certified { certificate } => {
                    let report = match audit_jobs {
                        Some(jobs) => {
                            audit_shifted_exact_certificate_with_jobs(&certificate, jobs)?
                        }
                        None => audit_shifted_exact_certificate(&certificate)?,
                    };
                    fs::write(output, json(&certificate)?)?;
                    print!("{}", json(&report)?);
                }
                ShiftedSalvageOutcome::Unsalvageable { failure } => {
                    fs::write(&output, json(&failure)?)?;
                    bail!(
                        "candidate is soundly unsalvageable; wrote all exact shifts and reasons to {}",
                        output.display()
                    )
                }
            }
        }
        Command::AuditExactSplitShifted { path, audit_jobs } => {
            let certificate: SplitShiftedExactDualCertificate =
                serde_json::from_slice(&fs::read(path)?)?;
            let report = match audit_jobs {
                Some(jobs) => audit_split_shifted_exact_certificate_with_jobs(&certificate, jobs)?,
                None => audit_split_shifted_exact_certificate(&certificate)?,
            };
            print!("{}", json(&report)?);
        }
        Command::SalvageExactSplitShifted {
            input,
            output,
            audit_jobs,
        } => {
            if input == output
                || (output.exists() && fs::canonicalize(&input)? == fs::canonicalize(&output)?)
            {
                bail!("split shifted output must not overwrite the pinned split v1 input")
            }
            let original: SplitExactDualCertificate = serde_json::from_slice(&fs::read(&input)?)?;
            let outcome = match audit_jobs {
                Some(jobs) => salvage_split_shifted_exact_certificate_with_jobs(original, jobs),
                None => salvage_split_shifted_exact_certificate(original),
            }
            .context("could not salvage the identity-closed split candidate")?;
            if let Some(parent) = output.parent() {
                fs::create_dir_all(parent)?;
            }
            match outcome {
                SplitShiftedSalvageOutcome::Certified { certificate } => {
                    let report = match audit_jobs {
                        Some(jobs) => {
                            audit_split_shifted_exact_certificate_with_jobs(&certificate, jobs)?
                        }
                        None => audit_split_shifted_exact_certificate(&certificate)?,
                    };
                    fs::write(output, json(&certificate)?)?;
                    print!("{}", json(&report)?);
                }
                SplitShiftedSalvageOutcome::Unsalvageable { failure } => {
                    fs::write(&output, json(&failure)?)?;
                    bail!(
                        "split candidate is soundly unsalvageable; wrote every exact shift and reason to {}",
                        output.display()
                    )
                }
            }
        }
        Command::ProvenanceAudit { manifest } => {
            let artifacts: Vec<Artifact> = serde_json::from_slice(&fs::read(&manifest)?)?;
            let findings = audit(std::path::Path::new("."), &artifacts);
            let valid = findings.iter().all(|f| f.valid);
            print!("{}", json(&findings)?);
            if !valid {
                std::process::exit(2);
            }
        }
        Command::LeanConstants { output } => {
            if let Some(parent) = output.parent() {
                fs::create_dir_all(parent)?;
            }
            let status = RigorStatus::LeanInstantiated;
            let text = format!(
                "-- Generated by minexposure {}; do not edit.\nnamespace MinExposure\n\ndef schemaVersion : String := {:?}\ndef freeTimeCzOrder3Projected : Rat := 24077 / 10000\ndef notionCubic : Rat := 3 / 1 -- divide by sqrt 2 in consumer field\ndef notionQuintic : Rat := 12 / 5\ndef notionSeptic : Rat := 11 / 4\ndef generationRigor : String := {:?}\n\nend MinExposure\n",
                env!("CARGO_PKG_VERSION"),
                minexposure_core::SCHEMA_VERSION,
                format!("{status:?}")
            );
            fs::write(output, text)?;
        }
        Command::SimulateCole {
            v_rb_cs_mhz,
            v_rb_rb_mhz,
            cs_to_rb_ratio,
        } => {
            let parameters = ColeParameters::from_cole(v_rb_cs_mhz, v_rb_rb_mhz, cs_to_rb_ratio);
            let results = simulate_cole_all(parameters).map_err(anyhow::Error::msg)?;
            print!(
                "{}",
                json(&serde_json::json!({
                    "model": "finite-blockade Cole CZZ pi-2pi-pi",
                    "parameters": parameters,
                    "states": results,
                    "source_repository": "https://github.com/wanda0929/Finite_blockade_pulse",
                    "source_commit": "677eba8905756a4dd4d1f0c760b0375ebec67161",
                    "rigor": "exploratory"
                }))?
            );
        }
        Command::FiniteExposureFloor { v_mhz } => {
            if !v_mhz.is_finite() || v_mhz <= 0.0 {
                bail!("v_mhz must be positive and finite")
            }
            print!(
                "{}",
                json(&serde_json::json!({
                    "model": "finite-blockade CZZ arbitrary-drive exposure theorem",
                    "main_assumption": "shared Rb laser and V_RbRb=0",
                    "main_dimensionless_floor_V_T_R": 9.0 / 4.0,
                    "main_floor_microseconds": 9.0 / (8.0 * std::f64::consts::PI * v_mhz),
                    "robust_assumption": "arbitrary V_RbRb",
                    "robust_dimensionless_floor_V_T_R": 3.0_f64.sqrt(),
                    "robust_floor_microseconds": 3.0_f64.sqrt() / (2.0 * std::f64::consts::PI * v_mhz),
                    "v_mhz": v_mhz,
                    "rigor": "exploratory",
                    "warning": "source contains an analytic proof and numerical audits, but no machine-checked certificate is imported yet",
                    "proof_source": "Finite_blockade_pulse/Notes/exposure-lower-bound/main.typ at 677eba8905756a4dd4d1f0c760b0375ebec67161"
                }))?
            );
        }
        Command::ReproduceFinitePulse { path } => reproduce_finite_pulse(&path)?,
        Command::FinitePulseGradient { path } => {
            let artifact: FinitePulseArtifact = serde_json::from_slice(&fs::read(path)?)?;
            let objective = phase_objective(
                &artifact.segments().map_err(anyhow::Error::msg)?,
                artifact.theta_rb,
                artifact.theta_cs,
            )
            .map_err(anyhow::Error::msg)?;
            print!("{}", json(&objective)?);
        }
        Command::DiagnoseStationaryPulse {
            order,
            pulse,
            solution,
            knots,
            rate_knots,
            xi_degree,
            enrich_charges,
            enrich_degree,
            u_degree,
            rydberg_localizer_charges,
            active_time_cap,
            output,
        } => {
            let pulse: stationary_torus::IdealBlockadePulse =
                serde_json::from_slice(&fs::read(pulse)?)?;
            let solution = solution
                .map(|path| -> Result<_> {
                    Ok(serde_json::from_slice::<
                        stationary_torus::StationarySolutionDump,
                    >(&fs::read(path)?)?)
                })
                .transpose()?;
            let report = if let Some(knots) = knots {
                let grid = knots.parse::<SplitGrid>().map_err(anyhow::Error::msg)?;
                if let Some(rate_knots) = rate_knots {
                    if solution.is_some() {
                        bail!("cost-rate witness transport does not consume --solution")
                    }
                    if active_time_cap.is_some() {
                        bail!("cost-rate witness transport does not support --active-time-cap")
                    }
                    reject_rate_split_extensions(xi_degree, enrich_charges, enrich_degree)?;
                    reject_new_split_options(u_degree, rydberg_localizer_charges)?;
                    let rate_grid = parse_rate_grid(&rate_knots)?;
                    serde_json::to_value(
                        stationary_cost_rate_split::diagnose_ideal_blockade_pulse(
                            order, &grid, &rate_grid, &pulse,
                        )
                        .map_err(anyhow::Error::msg)?,
                    )?
                } else {
                    let enrichment = parse_charge_enrichment(enrich_charges, enrich_degree)?;
                    let rydberg_localizers = parse_charge_selection(rydberg_localizer_charges)?;
                    let active_time_cap = active_time_cap
                        .map(|value| value.parse::<Rational>().map_err(anyhow::Error::msg))
                        .transpose()?;
                    if let Some(active_time_cap) = active_time_cap {
                        if solution.is_some()
                            || xi_degree.is_some()
                            || enrichment.is_some()
                            || u_degree.is_some()
                            || rydberg_localizers.is_some()
                        {
                            bail!(
                                "--active-time-cap witness transport cannot be combined with --solution or another split strengthening"
                            )
                        }
                        serde_json::to_value(
                            stationary_hausdorff_split::diagnose_ideal_blockade_pulse_with_active_time_cap(
                                order, &grid, &pulse,
                                active_time_cap,
                            )
                            .map_err(anyhow::Error::msg)?,
                        )?
                    } else {
                        match (
                            solution.as_ref(),
                            xi_degree,
                            enrichment.as_ref(),
                            u_degree,
                            rydberg_localizers.as_deref(),
                        ) {
                            (Some(_), Some(_), _, _, _) => {
                                bail!("split charge diagnostics from --solution do not support --xi-degree")
                            }
                            (Some(_), None, None, Some(_), None)
                            | (Some(_), None, None, None, Some(_)) => {
                                bail!("split charge diagnostics from --solution do not yet support the new exploratory Gram families")
                            }
                            (Some(solution), None, enrichment, None, None) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_solution_charge_slack(
                                    order, &grid, &pulse, solution, enrichment,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            (None, Some(xi_degree), Some(enrichment), None, None) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_composed_ideal_blockade_pulse(
                                    order, xi_degree, &grid, &pulse, enrichment,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            (None, Some(xi_degree), None, None, None) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_ideal_blockade_pulse_anisotropic(
                                    order, xi_degree, &grid, &pulse,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            (None, None, Some(enrichment), None, None) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_enriched_ideal_blockade_pulse(
                                    order, &grid, &pulse, enrichment,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            (None, None, None, Some(u_degree), None) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_u_anisotropic_ideal_blockade_pulse(
                                    order, u_degree, &grid, &pulse,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            (None, None, None, None, Some(charges)) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_rydberg_localized_ideal_blockade_pulse(
                                    order, &grid, &pulse, charges,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            (None, None, None, None, None) => serde_json::to_value(
                                stationary_hausdorff_split::diagnose_ideal_blockade_pulse(
                                    order, &grid, &pulse,
                                )
                                .map_err(anyhow::Error::msg)?,
                            )?,
                            _ => bail!("incompatible exploratory split strengthening flags"),
                        }
                    }
                }
            } else {
                if active_time_cap.is_some() {
                    bail!("--active-time-cap witness transport requires --knots")
                }
                reject_new_split_options(u_degree, rydberg_localizer_charges)?;
                reject_irrelevant_split_options(
                    None,
                    rate_knots,
                    xi_degree,
                    enrich_charges,
                    enrich_degree,
                )?;
                serde_json::to_value(
                    stationary_torus::diagnose_ideal_blockade_pulse(
                        order,
                        &pulse,
                        solution.as_ref(),
                    )
                    .map_err(anyhow::Error::msg)?,
                )?
            };
            write_solver_result(output, report)?;
        }
    }
    Ok(())
}

fn reproduce_finite_pulse(path: &std::path::Path) -> Result<()> {
    let artifact: FinitePulseArtifact = serde_json::from_slice(&fs::read(path)?)?;
    let h = artifact.hamiltonian_parameters_mhz;
    let metrics = pulse_metrics(
        &artifact.segments().map_err(anyhow::Error::msg)?,
        artifact.theta_rb,
        artifact.theta_cs,
    )
    .map_err(anyhow::Error::msg)?;
    print!(
        "{}",
        json(&serde_json::json!({
            "model": "finite-blockade Rb-Cs-Rb CZZ",
            "pulse": artifact.identity,
            "segments": artifact.n_segments,
            "duration_us": artifact.duration_us,
            "states": metrics.amplitudes,
            "exposures_per_sector_us": metrics.exposure_per_sector_us,
            "fidelity_reproduced": metrics.fidelity,
            "fidelity_stored": artifact.discrete_staircase_fidelity,
            "fidelity_difference": metrics.fidelity - artifact.discrete_staircase_fidelity,
            "T_R_us": metrics.rydberg_exposure_us,
            "T_R_Omega": 2.0 * std::f64::consts::PI * h.omega_rb * metrics.rydberg_exposure_us,
            "V_T_R": 2.0 * std::f64::consts::PI * h.v_rbcs * metrics.rydberg_exposure_us,
            "source_sha256": "729bbb330c5ff9a591d48348f67e455aa5357fce862240a59d597c903740023b",
            "rigor": "exploratory"
        }))?
    );
    Ok(())
}

fn write_solver_result(output: Option<PathBuf>, result: serde_json::Value) -> Result<()> {
    let text = serde_json::to_string_pretty(&result)? + "\n";
    if let Some(path) = output {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, text)?;
    } else {
        print!("{text}");
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn solver_problem(
    model: Option<ModelId>,
    order: Option<u8>,
    kappa: Option<String>,
    horizon: Option<String>,
    knots: Option<String>,
    rate_knots: Option<String>,
    xi_degree: Option<u8>,
    enrich_charges: Option<String>,
    enrich_degree: Option<u8>,
    u_degree: Option<u8>,
    rydberg_localizer_charges: Option<String>,
    active_time_cap: Option<String>,
    include_gram_metadata: bool,
) -> Result<(ConicProblem, serde_json::Value)> {
    if active_time_cap.is_some() && model != Some(ModelId::StationaryTorusHausdorffSplit) {
        bail!("--active-time-cap applies only to stationary_torus_hausdorff_split")
    }
    match model {
        None => {
            if order.is_some()
                || kappa.is_some()
                || horizon.is_some()
                || knots.is_some()
                || rate_knots.is_some()
                || xi_degree.is_some()
                || enrich_charges.is_some()
                || enrich_degree.is_some()
                || u_degree.is_some()
                || rydberg_localizer_charges.is_some()
                || active_time_cap.is_some()
            {
                bail!("scientific parameters require a model")
            }
            Ok((
                adapter_regression_problem(),
                serde_json::json!({
                    "model": "adapter_regression",
                    "description": "min x subject to diag(1,x) PSD"
                }),
            ))
        }
        Some(ModelId::StationaryTorus) => {
            reject_new_split_options(u_degree, rydberg_localizer_charges)?;
            reject_irrelevant_split_options(
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
            )?;
            if kappa.is_some() || horizon.is_some() {
                bail!("stationary_torus does not accept --kappa or --horizon")
            }
            let order = order.context("stationary_torus requires --order")?;
            let assembled = stationary_torus::assemble(order).map_err(anyhow::Error::msg)?;
            let mut metadata = serde_json::to_value(assembled.structure)?;
            if let Some(reference) = stationary_torus::archived_mosek_result(order) {
                metadata["archived_mosek_result"] = serde_json::to_value(reference)?;
            }
            if include_gram_metadata {
                metadata["gram_blocks_in_assembly_order"] = serde_json::to_value(
                    stationary_torus::gram_block_metadata(order).map_err(anyhow::Error::msg)?,
                )?;
            }
            Ok((assembled.conic, metadata))
        }
        Some(ModelId::StationaryTorusHausdorffLift) => {
            reject_new_split_options(u_degree, rydberg_localizer_charges)?;
            reject_irrelevant_split_options(
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
            )?;
            if kappa.is_some() || horizon.is_some() {
                bail!("stationary_torus_hausdorff_lift does not accept --kappa or --horizon")
            }
            let order = order.context("stationary_torus_hausdorff_lift requires --order")?;
            let assembled = stationary_hausdorff::assemble(order).map_err(anyhow::Error::msg)?;
            let mut metadata = serde_json::to_value(assembled.structure)?;
            if let Some(reference) = stationary_hausdorff::archived_mosek_result(order) {
                metadata["archived_mosek_result"] = serde_json::to_value(reference)?;
            }
            Ok((assembled.conic, metadata))
        }
        Some(ModelId::StationaryTorusHausdorffSplit) => {
            if kappa.is_some() || horizon.is_some() {
                bail!("stationary_torus_hausdorff_split does not accept --kappa or --horizon")
            }
            let order = order.context("stationary_torus_hausdorff_split requires --order")?;
            let grid = parse_required_split_grid(knots)?;
            if let Some(rate_knots) = rate_knots {
                if active_time_cap.is_some() {
                    bail!("cost-rate splitting cannot be combined with --active-time-cap")
                }
                reject_rate_split_extensions(xi_degree, enrich_charges, enrich_degree)?;
                reject_new_split_options(u_degree, rydberg_localizer_charges)?;
                let rate_grid = parse_rate_grid(&rate_knots)?;
                let assembled = stationary_cost_rate_split::assemble(order, &grid, &rate_grid)
                    .map_err(anyhow::Error::msg)?;
                let metadata = serde_json::to_value(assembled.structure)?;
                return Ok((assembled.conic, metadata));
            }
            let enrichment = parse_charge_enrichment(enrich_charges, enrich_degree)?;
            let rydberg_localizers = parse_charge_selection(rydberg_localizer_charges)?;
            let active_time_cap = active_time_cap
                .map(|value| value.parse::<Rational>().map_err(anyhow::Error::msg))
                .transpose()?;
            if let Some(active_time_cap) = active_time_cap {
                if xi_degree.is_some()
                    || enrichment.is_some()
                    || u_degree.is_some()
                    || rydberg_localizers.is_some()
                {
                    bail!(
                        "--active-time-cap currently supports only the baseline split formulation"
                    )
                }
                let assembled = stationary_hausdorff_split::assemble_with_active_time_cap(
                    order,
                    &grid,
                    active_time_cap,
                )
                .map_err(anyhow::Error::msg)?;
                let metadata = serde_json::to_value(assembled.structure)?;
                return Ok((assembled.conic, metadata));
            }
            match (
                xi_degree,
                enrichment.as_ref(),
                u_degree,
                rydberg_localizers.as_deref(),
            ) {
                (Some(xi_degree), Some(enrichment), None, None) => {
                    let assembled = stationary_hausdorff_split::assemble_composed(
                        order, xi_degree, &grid, enrichment,
                    )
                    .map_err(anyhow::Error::msg)?;
                    let metadata = serde_json::to_value(assembled.structure)?;
                    Ok((assembled.conic, metadata))
                }
                (Some(xi_degree), None, None, None) => {
                    let assembled =
                        stationary_hausdorff_split::assemble_anisotropic(order, xi_degree, &grid)
                            .map_err(anyhow::Error::msg)?;
                    let metadata = serde_json::to_value(assembled.structure)?;
                    Ok((assembled.conic, metadata))
                }
                (None, Some(enrichment), None, None) => {
                    let assembled =
                        stationary_hausdorff_split::assemble_enriched(order, &grid, enrichment)
                            .map_err(anyhow::Error::msg)?;
                    let metadata = serde_json::to_value(assembled.structure)?;
                    Ok((assembled.conic, metadata))
                }
                (None, None, Some(u_degree), None) => {
                    let assembled =
                        stationary_hausdorff_split::assemble_u_anisotropic(order, u_degree, &grid)
                            .map_err(anyhow::Error::msg)?;
                    let metadata = serde_json::to_value(assembled.structure)?;
                    Ok((assembled.conic, metadata))
                }
                (None, None, None, Some(charges)) => {
                    let assembled = stationary_hausdorff_split::assemble_rydberg_localized(
                        order, &grid, charges,
                    )
                    .map_err(anyhow::Error::msg)?;
                    let metadata = serde_json::to_value(assembled.structure)?;
                    Ok((assembled.conic, metadata))
                }
                (None, None, None, None) => {
                    let assembled = stationary_hausdorff_split::assemble(order, &grid)
                        .map_err(anyhow::Error::msg)?;
                    let metadata = serde_json::to_value(assembled.structure)?;
                    Ok((assembled.conic, metadata))
                }
                _ => bail!("incompatible exploratory split strengthening flags"),
            }
        }
        Some(ModelId::StationaryTorusStrengthened) => {
            reject_new_split_options(u_degree, rydberg_localizer_charges)?;
            reject_irrelevant_split_options(
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
            )?;
            if kappa.is_some() || horizon.is_some() {
                bail!("stationary_torus_strengthened does not accept --kappa or --horizon")
            }
            let order = order.context("stationary_torus_strengthened requires --order")?;
            let assembled =
                stationary_torus::assemble_strengthened(order).map_err(anyhow::Error::msg)?;
            Ok((assembled.conic, serde_json::to_value(assembled.structure)?))
        }
        Some(ModelId::StationaryTorusSharedControlLift) => {
            reject_new_split_options(u_degree, rydberg_localizer_charges)?;
            reject_irrelevant_split_options(
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
            )?;
            if kappa.is_some() || horizon.is_some() {
                bail!("stationary_torus_shared_control_lift does not accept --kappa or --horizon")
            }
            let order = order.context("stationary_torus_shared_control_lift requires --order")?;
            let assembled = minexposure_core::shared_control_lift::assemble(order)
                .map_err(anyhow::Error::msg)?;
            Ok((assembled.conic, serde_json::to_value(assembled.structure)?))
        }
        Some(ModelId::FiniteCzFixedKappa) => {
            reject_new_split_options(u_degree, rydberg_localizer_charges)?;
            reject_irrelevant_split_options(
                knots,
                rate_knots,
                xi_degree,
                enrich_charges,
                enrich_degree,
            )?;
            let order = order.context("finite_cz_fixed_kappa requires --order")?;
            let kappa = kappa
                .context("finite_cz_fixed_kappa requires --kappa")?
                .parse::<Rational>()
                .map_err(anyhow::Error::msg)?;
            let horizon = horizon
                .context("finite_cz_fixed_kappa requires --horizon")?
                .parse::<Rational>()
                .map_err(anyhow::Error::msg)?;
            let assembled = minexposure_core::finite_sdp::assemble(order, kappa, horizon)
                .map_err(anyhow::Error::msg)?;
            Ok((assembled.conic, serde_json::to_value(assembled.structure)?))
        }
        Some(other) => bail!(
            "native scientific matrix assembly is not implemented for {other}; currently supported: stationary_torus, stationary_torus_strengthened, stationary_torus_shared_control_lift, stationary_torus_hausdorff_lift, stationary_torus_hausdorff_split, finite_cz_fixed_kappa"
        ),
    }
}

fn parse_required_split_grid(knots: Option<String>) -> Result<SplitGrid> {
    knots
        .context("stationary_torus_hausdorff_split requires --knots")?
        .parse::<SplitGrid>()
        .map_err(anyhow::Error::msg)
}

fn reject_irrelevant_split_options(
    knots: Option<String>,
    rate_knots: Option<String>,
    xi_degree: Option<u8>,
    enrich_charges: Option<String>,
    enrich_degree: Option<u8>,
) -> Result<()> {
    if knots.is_some() {
        bail!("--knots applies only to stationary_torus_hausdorff_split")
    }
    if rate_knots.is_some() {
        bail!("--rate-knots applies only to stationary_torus_hausdorff_split")
    }
    if xi_degree.is_some() {
        bail!("--xi-degree applies only to stationary_torus_hausdorff_split")
    }
    if enrich_charges.is_some() || enrich_degree.is_some() {
        bail!("--enrich-charges and --enrich-degree apply only to stationary_torus_hausdorff_split")
    }
    Ok(())
}

fn parse_rate_grid(knots: &str) -> Result<RateGrid> {
    knots.parse::<RateGrid>().map_err(anyhow::Error::msg)
}

fn reject_rate_split_extensions(
    xi_degree: Option<u8>,
    enrich_charges: Option<String>,
    enrich_degree: Option<u8>,
) -> Result<()> {
    if xi_degree.is_some() || enrich_charges.is_some() || enrich_degree.is_some() {
        bail!("--rate-knots cannot currently be combined with xi or charge enrichment")
    }
    Ok(())
}

fn parse_charge_enrichment(
    charges: Option<String>,
    degree: Option<u8>,
) -> Result<Option<ChargeEnrichment>> {
    match (charges, degree) {
        (None, None) => Ok(None),
        (Some(charges), Some(degree)) => ChargeEnrichment::parse(&charges, degree)
            .map(Some)
            .map_err(anyhow::Error::msg),
        _ => bail!("--enrich-charges and --enrich-degree must be supplied together"),
    }
}

fn parse_charge_selection(charges: Option<String>) -> Result<Option<Vec<(i32, i32)>>> {
    charges
        .map(|charges| ChargeEnrichment::parse(&charges, 1).map(|value| value.charges))
        .transpose()
        .map_err(anyhow::Error::msg)
}

fn reject_new_split_options(
    u_degree: Option<u8>,
    rydberg_localizer_charges: Option<String>,
) -> Result<()> {
    if u_degree.is_some() {
        bail!("--u-degree applies only to stationary_torus_hausdorff_split")
    }
    if rydberg_localizer_charges.is_some() {
        bail!("--rydberg-localizer-charges applies only to stationary_torus_hausdorff_split")
    }
    Ok(())
}

#[derive(Clone, Debug)]
struct InteriorMarginTarget {
    exact: String,
    value: f64,
    active_grams: Option<Vec<bool>>,
    zero_gram_threshold: f64,
    reference: Option<PathBuf>,
    reference_eigenvalue_threshold: Option<f64>,
    per_block_margins: bool,
    margin_cap: Option<f64>,
}

fn parse_interior_margin_target(
    model: Option<ModelId>,
    dump_solution: bool,
    target: &str,
    zero_gram_threshold: f64,
    reference_eigenvalue_threshold: Option<f64>,
    per_block_margins: bool,
    margin_cap: Option<f64>,
) -> Result<InteriorMarginTarget> {
    if model != Some(ModelId::StationaryTorusHausdorffSplit) {
        bail!("--interior-target applies only to stationary_torus_hausdorff_split")
    }
    if !dump_solution {
        bail!("--interior-target requires --dump-solution")
    }
    if !zero_gram_threshold.is_finite() || zero_gram_threshold < 0.0 {
        bail!("--interior-zero-gram-threshold must be finite and nonnegative")
    }
    if reference_eigenvalue_threshold.is_some_and(|value| !value.is_finite()) {
        bail!("--interior-reference-eigenvalue-threshold must be finite")
    }
    if margin_cap.is_some_and(|value| !value.is_finite() || value <= 0.0) {
        bail!("--interior-margin-cap must be positive and finite")
    }
    if per_block_margins && margin_cap.is_none() {
        bail!("--interior-per-block-margins requires --interior-margin-cap")
    }
    let target = target.parse::<Rational>().map_err(anyhow::Error::msg)?;
    let value = target.numerator as f64 / target.denominator as f64;
    if !value.is_finite() || value <= 0.0 {
        bail!("--interior-target must be a positive finite rational")
    }
    Ok(InteriorMarginTarget {
        exact: target.to_string(),
        value,
        active_grams: None,
        zero_gram_threshold,
        reference: None,
        reference_eigenvalue_threshold,
        per_block_margins,
        margin_cap,
    })
}

impl InteriorMarginTarget {
    fn load_active_grams(
        &mut self,
        path: &std::path::Path,
        problem: &ConicProblem,
        metadata: &serde_json::Value,
    ) -> Result<()> {
        let payload: serde_json::Value = serde_json::from_slice(&fs::read(path)?)?;
        if payload["problem"]["formulation_hash"] != metadata["formulation_hash"] {
            bail!("--interior-reference formulation hash does not match the requested model")
        }
        let grams: FloatingPsdGrams = serde_json::from_value(payload["dual_psd_grams"].clone())?;
        let expected_sides = problem.cones.iter().filter_map(|cone| match cone {
            Cone::PsdTriangle(side) => Some(*side),
            _ => None,
        });
        if grams
            .blocks
            .iter()
            .map(|block| block.side)
            .ne(expected_sides)
        {
            bail!("--interior-reference Gram sides do not match the requested model")
        }
        let active_grams = grams
            .blocks
            .iter()
            .map(|block| {
                let entry_active = block
                    .upper_triangle
                    .iter()
                    .map(|value| value.abs())
                    .fold(0.0, f64::max)
                    > self.zero_gram_threshold;
                let eigenvalue_active = self.reference_eigenvalue_threshold.is_none_or(|cutoff| {
                    let side = block.side;
                    let mut matrix = nalgebra::DMatrix::zeros(side, side);
                    let mut entry = 0;
                    for column in 0..side {
                        for row in 0..=column {
                            matrix[(row, column)] = block.upper_triangle[entry];
                            matrix[(column, row)] = block.upper_triangle[entry];
                            entry += 1;
                        }
                    }
                    matrix.symmetric_eigen().eigenvalues.min() > cutoff
                });
                entry_active && eigenvalue_active
            })
            .collect::<Vec<_>>();
        if !active_grams.iter().any(|&active| active) {
            bail!("--interior-reference leaves no active Gram blocks")
        }
        self.active_grams = Some(active_grams);
        self.reference = Some(path.to_path_buf());
        Ok(())
    }

    fn gram_is_active(&self, block: usize) -> bool {
        self.active_grams
            .as_ref()
            .is_none_or(|active| active[block])
    }

    fn load_active_gram_support(
        &mut self,
        path: &std::path::Path,
        problem: &ConicProblem,
        metadata: &serde_json::Value,
    ) -> Result<()> {
        let payload: serde_json::Value = serde_json::from_slice(&fs::read(path)?)?;
        if payload["formulation_hash"] != metadata["formulation_hash"] {
            bail!("--interior-active-gram-support formulation hash does not match the model")
        }
        let gram_count = problem
            .cones
            .iter()
            .filter(|cone| matches!(cone, Cone::PsdTriangle(_)))
            .count();
        let blocks = payload["provenance"]["exact_repair_gram_scope"]["selected_support_blocks"]
            .as_array()
            .context("active Gram support candidate has no selected support block array")?;
        let mut active = vec![false; gram_count];
        for block in blocks {
            let block = block
                .as_u64()
                .context("active Gram support index is not unsigned")?;
            let block = usize::try_from(block)?;
            let selected = active
                .get_mut(block)
                .context("active Gram support index is outside model")?;
            if *selected {
                bail!("active Gram support repeats block {block}")
            }
            *selected = true;
        }
        if !active.iter().any(|&selected| selected) {
            bail!("active Gram support is empty")
        }
        self.active_grams = Some(active);
        self.reference = Some(path.to_path_buf());
        self.reference_eigenvalue_threshold = None;
        Ok(())
    }
}

fn solve_clarabel(
    problem: &ConicProblem,
    metadata: serde_json::Value,
    dump_solution: bool,
) -> Result<serde_json::Value> {
    use clarabel::algebra::CscMatrix;
    use clarabel::solver::{DefaultSettings, DefaultSolver, IPSolver, SupportedConeT};
    problem.validate().map_err(anyhow::Error::msg)?;
    let (column_pointers, row_indices, values) = problem.csc();
    let p = CscMatrix::<f64>::zeros((problem.q.len(), problem.q.len()));
    let a = CscMatrix::new(
        problem.a.rows,
        problem.a.cols,
        column_pointers,
        row_indices,
        values,
    );
    let cones = problem
        .cones
        .iter()
        .map(|cone| match *cone {
            Cone::Zero(dimension) => SupportedConeT::ZeroConeT(dimension),
            Cone::Nonnegative(dimension) => SupportedConeT::NonnegativeConeT(dimension),
            Cone::SecondOrder(dimension) => SupportedConeT::SecondOrderConeT(dimension),
            Cone::PsdTriangle(side) => SupportedConeT::PSDTriangleConeT(side),
        })
        .collect::<Vec<_>>();
    let settings = DefaultSettings {
        verbose: false,
        tol_gap_abs: 1e-8,
        tol_gap_rel: 1e-8,
        tol_feas: 1e-8,
        max_iter: 500,
        ..DefaultSettings::default()
    };
    let mut solver = DefaultSolver::new(&p, &problem.q, &a, &problem.b, &cones, settings)?;
    solver.solve();
    let solution = solver.solution;
    let duality_gap = (solution.obj_val - solution.obj_val_dual).abs();
    let mut result = serde_json::json!({
        "schema": "minexposure/discovery-v1", "backend": "clarabel-rust", "backend_version": "0.11",
        "problem": metadata, "status": format!("{:?}", solution.status),
        "objective": solution.obj_val,
        "primal_objective": solution.obj_val,
        "dual_objective": solution.obj_val_dual,
        "absolute_duality_gap": duality_gap,
        "iterations": solution.iterations, "solve_time_seconds": solution.solve_time,
        "primal_residual": solution.r_prim, "dual_residual": solution.r_dual,
        "rigor": "exploratory", "warning": "floating discovery solve; exact certification is separate"
    });
    if dump_solution {
        let (solution, nonnegative_cone_multipliers) =
            clarabel_floating_dual(problem, &metadata, &solution.z)?;
        result["dual_equality_multipliers"] =
            serde_json::to_value(&solution.dual_equality_multipliers)?;
        if let Some(normalization) = solution.dual_normalization_multiplier {
            result["dual_normalization_multiplier"] = serde_json::to_value(normalization)?;
        }
        result["dual_psd_grams"] = serde_json::to_value(&solution.dual_psd_grams)?;
        if let Some(&scaled_multiplier) = nonnegative_cone_multipliers.first() {
            result["dual_nonnegative_cone_multipliers"] =
                serde_json::to_value(nonnegative_cone_multipliers)?;
            result["scaled_cap_row_multiplier"] = scaled_multiplier.into();
            result["active_time_cap_multiplier"] =
                physical_active_time_cap_multiplier(&metadata, scaled_multiplier)?.into();
        }
    }
    label_active_time_capped_result(&mut result);
    Ok(result)
}

fn label_active_time_capped_result(result: &mut serde_json::Value) {
    let Some(active_time_cap) = result
        .pointer("/problem/active_time_cap")
        .and_then(serde_json::Value::as_str)
        .map(str::to_owned)
    else {
        return;
    };
    let bound_scope = result
        .pointer("/problem/bound_scope")
        .and_then(serde_json::Value::as_str)
        .unwrap_or(stationary_hausdorff_split::ACTIVE_TIME_CAPPED_BOUND_SCOPE)
        .to_owned();
    result["active_time_cap"] = active_time_cap.into();
    result["bound_scope"] = bound_scope.into();
}

fn physical_active_time_cap_multiplier(
    metadata: &serde_json::Value,
    scaled_multiplier: f64,
) -> Result<f64> {
    let cap = metadata
        .get("active_time_cap")
        .and_then(serde_json::Value::as_str)
        .context("nonnegative cap row has no active_time_cap metadata")?
        .parse::<Rational>()
        .map_err(anyhow::Error::msg)?;
    Ok(scaled_multiplier * cap.denominator as f64 / cap.numerator as f64)
}

fn rescale_active_time_capped_primal_variables(
    metadata: &serde_json::Value,
    primal_variables: &mut [f64],
) -> Result<()> {
    let Some(scale) = metadata
        .get("occupation_variable_scale")
        .and_then(serde_json::Value::as_str)
    else {
        return Ok(());
    };
    let scale = scale.parse::<Rational>().map_err(anyhow::Error::msg)?;
    if scale == Rational::ONE {
        return Ok(());
    }
    let cells = metadata["cell_count"]
        .as_u64()
        .context("capped split metadata has no cell_count")?;
    let per_cell = metadata["occupation_moment_count_per_cell"]
        .as_u64()
        .context("capped split metadata has no occupation_moment_count_per_cell")?;
    let occupation_count = usize::try_from(
        cells
            .checked_mul(per_cell)
            .context("capped split occupation moment count overflows metadata integer range")?,
    )?;
    if occupation_count > primal_variables.len() {
        bail!("capped split occupation moment count exceeds primal vector length")
    }
    let scale = scale.numerator as f64 / scale.denominator as f64;
    for value in &mut primal_variables[..occupation_count] {
        *value *= scale;
    }
    Ok(())
}

fn positional_dual_scalars(
    values: &[f64],
    metadata: &serde_json::Value,
) -> Result<(Vec<f64>, Option<f64>)> {
    let Some(count) = metadata
        .get("liouville_equality_count")
        .and_then(serde_json::Value::as_u64)
        .map(usize::try_from)
        .transpose()?
    else {
        return Ok((values.to_vec(), None));
    };
    if metadata.get("terminal_moment_count").is_some() {
        if values.len() != count + 1 {
            bail!(
                "lifted zero-cone multiplier count {} does not match {count} Liouville equalities plus normalization",
                values.len()
            )
        }
        Ok((values[..count].to_vec(), Some(values[count])))
    } else if values.len() == count {
        Ok((values.to_vec(), None))
    } else if values.len() == 2 * count {
        Ok((values.iter().step_by(2).copied().collect(), None))
    } else {
        bail!(
            "zero-cone multiplier count {} does not match {count} Liouville equalities",
            values.len()
        )
    }
}

fn partition_scalar_multipliers(values: &[f64], nonnegative: &[bool]) -> (Vec<f64>, Vec<f64>) {
    assert_eq!(values.len(), nonnegative.len());
    let mut zero = Vec::new();
    let mut nonnegative_values = Vec::new();
    for (&value, &is_nonnegative) in values.iter().zip(nonnegative) {
        if is_nonnegative {
            nonnegative_values.push(value);
        } else {
            zero.push(value);
        }
    }
    (zero, nonnegative_values)
}

fn clarabel_floating_dual(
    problem: &ConicProblem,
    metadata: &serde_json::Value,
    dual: &[f64],
) -> Result<(FloatingDualSolution, Vec<f64>)> {
    let mut offset = 0;
    let mut zero_values = Vec::new();
    let mut nonnegative_values = Vec::new();
    let mut blocks = Vec::new();
    for cone in &problem.cones {
        let dimension = cone.dimension();
        match *cone {
            Cone::Zero(_) => zero_values.extend_from_slice(&dual[offset..offset + dimension]),
            Cone::Nonnegative(_) => {
                nonnegative_values.extend_from_slice(&dual[offset..offset + dimension])
            }
            Cone::PsdTriangle(side) => {
                let upper_triangle = dual[offset..offset + dimension]
                    .iter()
                    .enumerate()
                    .map(|(index, &value)| {
                        let mut column = ((8.0 * index as f64 + 1.0).sqrt() as usize - 1) / 2;
                        while (column + 1) * (column + 2) / 2 <= index {
                            column += 1;
                        }
                        let row = index - column * (column + 1) / 2;
                        if row == column {
                            value
                        } else {
                            value / std::f64::consts::SQRT_2
                        }
                    })
                    .collect();
                blocks.push(FloatingPsdBlock {
                    side,
                    upper_triangle,
                });
            }
            _ => bail!("--dump-solution currently requires a Zero/PSD-only SDP"),
        }
        offset += dimension;
    }
    let (dual_equality_multipliers, dual_normalization_multiplier) =
        positional_dual_scalars(&zero_values, metadata)?;
    let result = FloatingDualSolution {
        dual_equality_multipliers,
        dual_normalization_multiplier,
        dual_psd_grams: FloatingPsdGrams {
            matrix_count: blocks.len(),
            encoding: FLOATING_GRAM_ENCODING.into(),
            blocks,
        },
    };
    result.validate().map_err(anyhow::Error::msg)?;
    Ok((result, nonnegative_values))
}

fn solve_mosek(
    problem: &ConicProblem,
    metadata: serde_json::Value,
    dump_solution: bool,
    diagnostic_dump: Option<&std::path::Path>,
    solver_log: bool,
    strict: bool,
    interior_target: Option<&InteriorMarginTarget>,
) -> Result<serde_json::Value> {
    if problem.cones.iter().all(|cone| {
        matches!(
            cone,
            Cone::Zero(_) | Cone::Nonnegative(_) | Cone::PsdTriangle(_)
        )
    }) {
        return solve_mosek_dual_sdp(
            problem,
            metadata,
            dump_solution,
            diagnostic_dump,
            solver_log,
            strict,
            interior_target,
            NativeSdpMode::Standard,
            None,
        );
    }
    if dump_solution || diagnostic_dump.is_some() || strict || interior_target.is_some() {
        bail!(
            "solution dumps, --strict, and --interior-target currently require a Zero/PSD-only SDP"
        )
    }
    solve_mosek_affine_conic(problem, metadata, solver_log, false, false)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NativeSdpMode {
    Standard,
    /// Advisory cone-repair feasibility solve; `max_iterations` caps the
    /// interior-point iterations and an unknown-status iterate is accepted.
    ConeRepair {
        max_iterations: i32,
    },
}

fn mosek_solution_is_usable(status: i32, mode: NativeSdpMode) -> bool {
    status == mosek::Solsta::OPTIMAL
        || (matches!(mode, NativeSdpMode::ConeRepair { .. }) && status == mosek::Solsta::UNKNOWN)
}

#[allow(clippy::too_many_arguments)]
fn solve_mosek_dual_sdp(
    problem: &ConicProblem,
    metadata: serde_json::Value,
    dump_dual: bool,
    diagnostic_dump: Option<&std::path::Path>,
    solver_log: bool,
    strict: bool,
    interior_target: Option<&InteriorMarginTarget>,
    mode: NativeSdpMode,
    native_bar_faces: Option<&SplitNativeBarFacePlan>,
) -> Result<serde_json::Value> {
    use mosek::{
        Boundkey, Dinfitem, Dparam, Iinfitem, Iparam, Objsense, Solsta, Soltype, Streamtype, Task,
    };
    problem.validate().map_err(anyhow::Error::msg)?;
    let cone_repair = matches!(mode, NativeSdpMode::ConeRepair { .. });

    if interior_target.is_some()
        && problem
            .cones
            .iter()
            .scan(0_usize, |offset, cone| {
                let start = *offset;
                *offset += cone.dimension();
                Some((start, cone))
            })
            .any(|(start, cone)| {
                matches!(cone, Cone::PsdTriangle(_))
                    && problem.b[start..start + cone.dimension()]
                        .iter()
                        .any(|&value| value != 0.0)
            })
    {
        bail!("--interior-target requires zero right-hand sides on every PSD cone")
    }
    let identity_constraint_count = problem.q.len();
    let target_constraint = interior_target.map(|_| identity_constraint_count);
    let face_constraint_start = identity_constraint_count + usize::from(interior_target.is_some());
    let face_constraint_count = native_bar_faces.map_or(0, |plan| plan.blocks.len());
    let constraints = i32::try_from(face_constraint_start + face_constraint_count)
        .context("too many MOSEK constraints")?;
    let mut scalar_row_indices = vec![None; problem.a.rows];
    let mut scalar_nonnegative = Vec::new();
    let mut psd_rows = Vec::new();
    let mut scalar_variables = 0_usize;
    let mut row_offset = 0_usize;
    for cone in &problem.cones {
        match *cone {
            Cone::Zero(dimension) => {
                for row_index in scalar_row_indices
                    .iter_mut()
                    .skip(row_offset)
                    .take(dimension)
                {
                    *row_index = Some(scalar_variables);
                    scalar_nonnegative.push(false);
                    scalar_variables += 1;
                }
            }
            Cone::Nonnegative(dimension) => {
                for row_index in scalar_row_indices
                    .iter_mut()
                    .skip(row_offset)
                    .take(dimension)
                {
                    *row_index = Some(scalar_variables);
                    scalar_nonnegative.push(true);
                    scalar_variables += 1;
                }
            }
            Cone::PsdTriangle(side) => {
                psd_rows.push((row_offset, row_offset + cone.dimension(), side))
            }
            _ => unreachable!("native SDP adapter accepts only zero, nonnegative, and PSD cones"),
        }
        row_offset += cone.dimension();
    }
    let equality_variable_count = scalar_variables;
    let margin_variable = interior_target
        .filter(|target| !target.per_block_margins)
        .map(|_| {
            let variable = scalar_variables;
            scalar_variables += 1;
            variable
        });
    let mut per_block_margin_variables = vec![None; psd_rows.len()];
    if let Some(target) = interior_target.filter(|target| target.per_block_margins) {
        for (block, variable) in per_block_margin_variables.iter_mut().enumerate() {
            if target.gram_is_active(block) {
                *variable = Some(scalar_variables);
                scalar_variables += 1;
            }
        }
    }

    let mut task = Task::new().context("create native MOSEK task")?;
    let tight_feasibility_tolerances = strict || cone_repair;
    if tight_feasibility_tolerances {
        for parameter in [
            Dparam::INTPNT_CO_TOL_PFEAS,
            Dparam::INTPNT_CO_TOL_DFEAS,
            Dparam::INTPNT_CO_TOL_REL_GAP,
        ] {
            task.put_dou_param(parameter, 1e-10).native()?;
        }
    }
    if let NativeSdpMode::ConeRepair { max_iterations } = mode {
        // This is a feasibility problem with an identically zero original
        // objective. Once the recovered iterate is accurate, further native-
        // dual iterations only chase an irrelevant analytic-dual gap. Exact
        // affine closure and LDL remain the authoritative acceptance gates.
        task.put_int_param(Iparam::INTPNT_MAX_ITERATIONS, max_iterations)
            .native()?;
    }
    task.append_cons(constraints).native()?;
    if scalar_variables != 0 {
        let variables =
            i32::try_from(scalar_variables).context("too many MOSEK scalar variables")?;
        task.append_vars(variables).native()?;
        let equality_variables =
            i32::try_from(equality_variable_count).context("too many MOSEK equality variables")?;
        let indices = (0..equality_variables).collect::<Vec<_>>();
        let bound_keys = scalar_nonnegative
            .iter()
            .map(|&nonnegative| {
                if nonnegative {
                    Boundkey::LO
                } else {
                    Boundkey::FR
                }
            })
            .collect::<Vec<_>>();
        task.put_var_bound_list(
            &indices,
            &bound_keys,
            &vec![0.0; equality_variable_count],
            &vec![0.0; equality_variable_count],
        )
        .native()?;
        if let Some(variable) = margin_variable {
            task.put_var_bound(i32::try_from(variable)?, Boundkey::FR, 0.0, 0.0)
                .native()?;
        }
        for variable in per_block_margin_variables.iter().flatten() {
            if let Some(cap) = interior_target.and_then(|target| target.margin_cap) {
                task.put_var_bound(i32::try_from(*variable)?, Boundkey::RA, 0.0, cap)
                    .native()?;
            } else {
                task.put_var_bound(i32::try_from(*variable)?, Boundkey::LO, 0.0, 0.0)
                    .native()?;
            }
        }
    }
    let bar_sides = psd_rows
        .iter()
        .map(|&(_, _, side)| i32::try_from(side))
        .collect::<Result<Vec<_>, _>>()?;
    let mut face_projectors: Vec<Option<&[Vec<f64>]>> = vec![None; psd_rows.len()];
    if let Some(plan) = native_bar_faces {
        if plan.gram_count != psd_rows.len() {
            bail!(
                "native-bar face plan has {} Grams, expected {}",
                plan.gram_count,
                psd_rows.len()
            )
        }
        for face in &plan.blocks {
            let side = psd_rows
                .get(face.block)
                .map(|&(_, _, side)| side)
                .context("native-bar face block is outside the PSD partition")?;
            if face.range_projector.len() != side
                || face
                    .range_projector
                    .iter()
                    .any(|row| row.len() != side || row.iter().any(|value| !value.is_finite()))
            {
                bail!(
                    "native-bar face projector for block {} is not a finite {side}x{side} matrix",
                    face.block
                )
            }
            if face_projectors[face.block]
                .replace(&face.range_projector)
                .is_some()
            {
                bail!("native-bar face plan repeats block {}", face.block)
            }
        }
    }
    task.append_barvars(&bar_sides).native()?;
    task.put_obj_sense(Objsense::MAXIMIZE).native()?;

    let mut scalar_objective = vec![0.0; scalar_variables];
    if let Some(margin_variable) = margin_variable {
        scalar_objective[margin_variable] = 1.0;
    } else if per_block_margin_variables.iter().any(Option::is_some) {
        let active_count = per_block_margin_variables.iter().flatten().count() as f64;
        for variable in per_block_margin_variables.iter().flatten() {
            scalar_objective[*variable] = 1.0 / active_count;
        }
    } else {
        for (row, scalar) in scalar_row_indices.iter().enumerate() {
            if let Some(scalar) = scalar {
                scalar_objective[*scalar] = -problem.b[row];
            }
        }
    }
    if scalar_variables != 0 {
        task.put_c_slice(0, i32::try_from(scalar_variables)?, &scalar_objective)
            .native()?;
    }

    let constraint_indices = (0..i32::try_from(identity_constraint_count)?).collect::<Vec<_>>();
    let constraint_values = problem.q.iter().map(|value| -*value).collect::<Vec<_>>();
    task.put_con_bound_list(
        &constraint_indices,
        &vec![Boundkey::FX; constraint_indices.len()],
        &constraint_values,
        &constraint_values,
    )
    .native()?;
    if let (Some(target), Some(constraint)) = (interior_target, target_constraint) {
        task.put_con_bound(
            i32::try_from(constraint)?,
            Boundkey::FX,
            target.value,
            target.value,
        )
        .native()?;
    }
    for offset in 0..face_constraint_count {
        task.put_con_bound(
            i32::try_from(face_constraint_start + offset)?,
            Boundkey::FX,
            0.0,
            0.0,
        )
        .native()?;
    }

    let mut scalar_constraints = Vec::new();
    let mut scalar_columns = Vec::new();
    let mut scalar_values = Vec::new();
    for &(row, column, value) in &problem.a.entries {
        if let Some(scalar) = scalar_row_indices[row] {
            scalar_constraints.push(i32::try_from(column)?);
            scalar_columns.push(i32::try_from(scalar)?);
            scalar_values.push(value);
        }
    }
    if !scalar_values.is_empty() {
        task.put_aij_list(&scalar_constraints, &scalar_columns, &scalar_values)
            .native()?;
    }
    if let Some(constraint) = target_constraint {
        let mut target_constraints = Vec::new();
        let mut target_columns = Vec::new();
        let mut target_values = Vec::new();
        for (row, scalar) in scalar_row_indices.iter().enumerate() {
            if let Some(scalar) = scalar {
                let value = -problem.b[row];
                if value != 0.0 {
                    target_constraints.push(i32::try_from(constraint)?);
                    target_columns.push(i32::try_from(*scalar)?);
                    target_values.push(value);
                }
            }
        }
        task.put_aij_list(&target_constraints, &target_columns, &target_values)
            .native()?;
    }
    if let Some(margin_variable) = margin_variable {
        let coefficients = common_gram_margin_coefficients(
            problem,
            &scalar_row_indices,
            &psd_rows,
            interior_target.expect("margin variable requires an interior target"),
            &face_projectors,
        )?;
        let mut margin_constraints = Vec::with_capacity(coefficients.len());
        let mut margin_columns = Vec::with_capacity(coefficients.len());
        let mut margin_values = Vec::with_capacity(coefficients.len());
        for (constraint, value) in coefficients {
            margin_constraints.push(i32::try_from(constraint)?);
            margin_columns.push(i32::try_from(margin_variable)?);
            margin_values.push(value);
        }
        task.put_aij_list(&margin_constraints, &margin_columns, &margin_values)
            .native()?;
    }
    let per_block_margin_coefficients = if per_block_margin_variables.iter().any(Option::is_some) {
        Some(gram_margin_coefficients_by_block(
            problem,
            &scalar_row_indices,
            &psd_rows,
            &face_projectors,
        )?)
    } else {
        None
    };
    for (block, variable) in per_block_margin_variables.iter().enumerate() {
        let Some(variable) = variable else {
            continue;
        };
        let coefficients = &per_block_margin_coefficients
            .as_ref()
            .expect("per-block margin coefficients were assembled")[block];
        let mut margin_constraints = Vec::with_capacity(coefficients.len());
        let mut margin_columns = Vec::with_capacity(coefficients.len());
        let mut margin_values = Vec::with_capacity(coefficients.len());
        for &(constraint, value) in coefficients {
            margin_constraints.push(i32::try_from(constraint)?);
            margin_columns.push(i32::try_from(*variable)?);
            margin_values.push(value);
        }
        task.put_aij_list(&margin_constraints, &margin_columns, &margin_values)
            .native()?;
    }

    const BAR_BATCH_SIZE: usize = 1_000_000;
    let mut bar_constraints = Vec::with_capacity(BAR_BATCH_SIZE);
    let mut bar_variables = Vec::with_capacity(BAR_BATCH_SIZE);
    let mut bar_rows = Vec::with_capacity(BAR_BATCH_SIZE);
    let mut bar_columns = Vec::with_capacity(BAR_BATCH_SIZE);
    let mut bar_values = Vec::with_capacity(BAR_BATCH_SIZE);
    let flush_bar_entries = |task: &mut Task,
                             bar_constraints: &mut Vec<i32>,
                             bar_variables: &mut Vec<i32>,
                             bar_rows: &mut Vec<i32>,
                             bar_columns: &mut Vec<i32>,
                             bar_values: &mut Vec<f64>|
     -> Result<()> {
        if !bar_values.is_empty() {
            task.put_bara_block_triplet(
                bar_constraints,
                bar_variables,
                bar_rows,
                bar_columns,
                bar_values,
            )
            .native()?;
            bar_constraints.clear();
            bar_variables.clear();
            bar_rows.clear();
            bar_columns.clear();
            bar_values.clear();
        }
        Ok(())
    };
    for &(row, column, value) in &problem.a.entries {
        if scalar_row_indices[row].is_some() {
            continue;
        }
        let constraint = i32::try_from(column)?;
        // MOSEK replaces a bar-A matrix element when that same (constraint,
        // bar-variable) pair is submitted again. Since entries are sorted by
        // constraint, flush only between constraints so a matrix is never
        // split across API calls.
        if bar_values.len() >= BAR_BATCH_SIZE
            && bar_constraints
                .last()
                .is_some_and(|&previous| previous != constraint)
        {
            flush_bar_entries(
                &mut task,
                &mut bar_constraints,
                &mut bar_variables,
                &mut bar_rows,
                &mut bar_columns,
                &mut bar_values,
            )?;
        }
        let bar_variable = psd_rows.partition_point(|&(_, end, _)| end <= row);
        let &(start, end, side) = psd_rows
            .get(bar_variable)
            .context("PSD row is outside the cone partition")?;
        if row < start || row >= end {
            bail!("nonzero entry belongs to an unsupported cone")
        }
        let (matrix_row, matrix_column, matrix_value) =
            upper_svec_to_lower_entry(row - start, side, value)?;
        bar_constraints.push(constraint);
        bar_variables.push(i32::try_from(bar_variable)?);
        bar_rows.push(i32::try_from(matrix_row)?);
        bar_columns.push(i32::try_from(matrix_column)?);
        bar_values.push(matrix_value);
    }
    flush_bar_entries(
        &mut task,
        &mut bar_constraints,
        &mut bar_variables,
        &mut bar_rows,
        &mut bar_columns,
        &mut bar_values,
    )?;
    if let Some(plan) = native_bar_faces {
        for (offset, face) in plan.blocks.iter().enumerate() {
            let side = face.range_projector.len();
            let capacity = side * (side + 1) / 2;
            let constraint = i32::try_from(face_constraint_start + offset)?;
            let bar_variable = i32::try_from(face.block)?;
            let mut constraints = Vec::with_capacity(capacity);
            let mut variables = Vec::with_capacity(capacity);
            let mut rows = Vec::with_capacity(capacity);
            let mut columns = Vec::with_capacity(capacity);
            let mut values = Vec::with_capacity(capacity);
            for row in 0..side {
                for column in 0..=row {
                    let identity = if row == column { 1.0 } else { 0.0 };
                    let value = identity - face.range_projector[row][column];
                    if value == 0.0 {
                        continue;
                    }
                    constraints.push(constraint);
                    variables.push(bar_variable);
                    rows.push(i32::try_from(row)?);
                    columns.push(i32::try_from(column)?);
                    values.push(value);
                }
            }
            task.put_bara_block_triplet(&constraints, &variables, &rows, &columns, &values)
                .native()?;
        }
    }

    let mut objective_variables = Vec::new();
    let mut objective_rows = Vec::new();
    let mut objective_columns = Vec::new();
    let mut objective_values = Vec::new();
    for (bar_variable, &(start, end, side)) in psd_rows.iter().enumerate() {
        for (local_row, &value) in problem.b[start..end].iter().enumerate() {
            if value == 0.0 {
                continue;
            }
            let (matrix_row, matrix_column, matrix_value) =
                upper_svec_to_lower_entry(local_row, side, -value)?;
            objective_variables.push(i32::try_from(bar_variable)?);
            objective_rows.push(i32::try_from(matrix_row)?);
            objective_columns.push(i32::try_from(matrix_column)?);
            objective_values.push(matrix_value);
        }
    }
    if !objective_values.is_empty() {
        task.put_barc_block_triplet(
            &objective_variables,
            &objective_rows,
            &objective_columns,
            &objective_values,
        )
        .native()?;
    }

    let termination = if solver_log {
        task.with_stream_callback(Streamtype::LOG, &|message| eprint!("{message}"), |task| {
            task.optimize()
        })
        .native()?
    } else {
        task.optimize().native()?
    };
    let status = task.get_sol_sta(Soltype::ITR).native()?;
    let advisory_unknown = cone_repair && status == Solsta::UNKNOWN;
    if !mosek_solution_is_usable(status, mode) {
        bail!("MOSEK returned solution status {status} (termination {termination})");
    }
    let objective = task.get_primal_obj(Soltype::ITR).native()?;
    let dual_objective = task.get_dual_obj(Soltype::ITR).native()?;
    let iterations = task.get_int_inf(Iinfitem::INTPNT_ITER).native()?;
    let solve_time = task.get_dou_inf(Dinfitem::INTPNT_TIME).native()?;
    let primal_residual = task.get_dou_inf(Dinfitem::INTPNT_PRIMAL_FEAS).native()?;
    let dual_residual = task.get_dou_inf(Dinfitem::INTPNT_DUAL_FEAS).native()?;
    let optimizer_threads = task.get_int_inf(Iinfitem::INTPNT_NUM_THREADS).native()?;
    let mut cone_scalar_values = vec![0.0; equality_variable_count];
    if equality_variable_count != 0 {
        task.get_xx_slice(
            Soltype::ITR,
            0,
            i32::try_from(equality_variable_count)?,
            &mut cone_scalar_values,
        )
        .native()?;
    }
    let (zero_cone_multipliers, nonnegative_cone_multipliers) =
        partition_scalar_multipliers(&cone_scalar_values, &scalar_nonnegative);
    let margins = if interior_target.is_some() {
        let mut values = vec![0.0; scalar_variables];
        task.get_xx(Soltype::ITR, &mut values).native()?;
        Some(
            per_block_margin_variables
                .iter()
                .enumerate()
                .map(|(block, variable)| {
                    variable
                        .map(|variable| values[variable])
                        .or_else(|| {
                            margin_variable.and_then(|variable| {
                                interior_target
                                    .is_some_and(|target| target.gram_is_active(block))
                                    .then_some(values[variable])
                            })
                        })
                        .unwrap_or(0.0)
                })
                .collect::<Vec<_>>(),
        )
    } else {
        None
    };
    if let Some(path) = diagnostic_dump {
        let mut constraint_duals = vec![0.0; problem.q.len()];
        task.get_y(Soltype::ITR, &mut constraint_duals).native()?;
        // The native task is the analytic dual of A*x+s=b. Its equality-
        // constraint multipliers have the opposite sign from the original x.
        let mut primal_variables = constraint_duals
            .into_iter()
            .map(|value| -value)
            .collect::<Vec<_>>();
        rescale_active_time_capped_primal_variables(&metadata, &mut primal_variables)?;
        let mut psd_blocks = Vec::with_capacity(psd_rows.len());
        for (index, &(_, _, side)) in psd_rows.iter().enumerate() {
            let mut lower_triangle = vec![0.0; side * (side + 1) / 2];
            task.get_barx_j(Soltype::ITR, i32::try_from(index)?, &mut lower_triangle)
                .native()?;
            psd_blocks.push(serde_json::json!({
                "side": side,
                "lower_triangle_column_major": lower_triangle
            }));
        }
        let mut dump = serde_json::json!({
            "schema": "minexposure/mosek-solution-v1",
            "mosek_form": "dualized_native_sdp",
            "problem": &metadata,
            "objective": objective,
            "primal_variables": primal_variables,
            "dual": {
                "zero_cone_multipliers": zero_cone_multipliers,
                "psd_blocks": psd_blocks
            },
            "note": "PSD matrices use MOSEK lower-triangular column-major packed order"
        });
        if !nonnegative_cone_multipliers.is_empty() {
            dump["dual"]["nonnegative_cone_multipliers"] =
                serde_json::to_value(&nonnegative_cone_multipliers)?;
            dump["scaled_cap_row_multiplier"] = nonnegative_cone_multipliers[0].into();
            dump["active_time_cap_multiplier"] =
                physical_active_time_cap_multiplier(&metadata, nonnegative_cone_multipliers[0])?
                    .into();
            label_active_time_capped_result(&mut dump);
        }
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, serde_json::to_string_pretty(&dump)? + "\n")?;
    }
    let source_reproduction = source_reproduction(&metadata, objective);
    let dual_solution = if dump_dual {
        let mut scalar_values = vec![0.0; scalar_variables];
        task.get_xx(Soltype::ITR, &mut scalar_values).native()?;
        let (equalities, _) = partition_scalar_multipliers(
            &scalar_values[..equality_variable_count],
            &scalar_nonnegative,
        );
        let mut blocks = Vec::with_capacity(bar_sides.len());
        for (bar_index, &side) in bar_sides.iter().enumerate() {
            let side = usize::try_from(side)?;
            let mut packed = vec![0.0; side * (side + 1) / 2];
            task.get_barx_j(Soltype::ITR, i32::try_from(bar_index)?, &mut packed)
                .native()?;
            let mut upper_triangle = Vec::with_capacity(packed.len());
            for column in 0..side {
                for row in 0..=column {
                    let lower_column_offset = row * side - row * row.saturating_sub(1) / 2;
                    let mut value = packed[lower_column_offset + column - row];
                    if interior_target.is_some_and(|target| target.gram_is_active(bar_index)) {
                        let margin = margins
                            .as_ref()
                            .and_then(|margins| margins.get(bar_index))
                            .copied()
                            .unwrap_or(0.0);
                        value = shifted_bar_entry(
                            value,
                            row,
                            column,
                            margin,
                            face_projectors[bar_index],
                        );
                    }
                    upper_triangle.push(value);
                }
            }
            blocks.push(FloatingPsdBlock {
                side,
                upper_triangle,
            });
        }
        let (dual_equality_multipliers, dual_normalization_multiplier) =
            positional_dual_scalars(&equalities, &metadata)?;
        let solution = FloatingDualSolution {
            dual_equality_multipliers,
            dual_normalization_multiplier,
            dual_psd_grams: FloatingPsdGrams {
                matrix_count: blocks.len(),
                encoding: FLOATING_GRAM_ENCODING.into(),
                blocks,
            },
        };
        solution.validate().map_err(anyhow::Error::msg)?;
        Some(solution)
    } else {
        None
    };
    let gram_minimum_eigenvalues = if interior_target.is_some() {
        Some(
            dual_solution
                .as_ref()
                .expect("--interior-target requires a dual dump")
                .full_gram_matrices()
                .map_err(anyhow::Error::msg)?
                .into_iter()
                .map(|matrix| {
                    let side = matrix.len();
                    nalgebra::DMatrix::from_fn(side, side, |row, column| matrix[row][column])
                        .symmetric_eigen()
                        .eigenvalues
                        .min()
                })
                .collect::<Vec<_>>(),
        )
    } else {
        None
    };
    let mut result = serde_json::json!({
        "schema": "minexposure/discovery-v1", "backend": "mosek-rust", "backend_version": "11.2.3",
        "mosek_form": "dualized_native_sdp", "problem": metadata,
        "status": if status == Solsta::OPTIMAL { "Optimal" } else { "UnknownAdvisoryCandidate" },
        "solution_status_code": status,
        "accepted_unknown_iterate_for_exact_repair": advisory_unknown,
        "termination": termination,
        "objective": objective, "primal_objective": objective, "dual_objective": dual_objective,
        "iterations": iterations, "solve_time_seconds": solve_time,
        "optimizer_threads": optimizer_threads,
        "solver_settings": if tight_feasibility_tolerances {
            serde_json::json!({
                "strict": strict,
                "cone_repair_tight_feasibility_tolerances": cone_repair,
                "MSK_DPAR_INTPNT_CO_TOL_PFEAS": 1e-10,
                "MSK_DPAR_INTPNT_CO_TOL_DFEAS": 1e-10,
                "MSK_DPAR_INTPNT_CO_TOL_REL_GAP": 1e-10,
                "MSK_IPAR_INTPNT_MAX_ITERATIONS": match mode {
                    NativeSdpMode::ConeRepair { max_iterations } => Some(max_iterations),
                    NativeSdpMode::Standard => None,
                },
            })
        } else {
            serde_json::json!({"strict": false, "parameters": "MOSEK defaults"})
        },
        "primal_residual": primal_residual, "dual_residual": dual_residual,
        "source_reproduction": source_reproduction,
        "rigor": "exploratory",
        "warning": if advisory_unknown {
            "MOSEK returned an unknown advisory iterate; exact reconstruction and the independent native audit must reject or certify it"
        } else {
            "floating discovery solve; exact certification is separate"
        }
    });
    if let Some(plan) = native_bar_faces {
        result["native_bar_faces"] = serde_json::json!({
            "formulation": "G=X+margin*P, X positive semidefinite, <I-P,X>=0",
            "constraint_count": plan.blocks.len(),
            "rotated_block_count": plan.blocks.iter().filter(|face| face.rotated).count(),
            "coordinate_face_block_count": plan.blocks.iter().filter(|face| !face.rotated).count(),
            "kernel_rank_sum": plan.blocks.iter().map(|face| face.kernel_rank).sum::<usize>(),
            "correction_signature_kernel_row_count": 0,
        });
    }
    if cone_repair {
        let mut constraint_duals = vec![0.0; usize::try_from(constraints)?];
        task.get_y(Soltype::ITR, &mut constraint_duals).native()?;
        result["primal_variables"] = serde_json::to_value(
            constraint_duals
                .into_iter()
                .take(problem.q.len())
                .map(|value| -value)
                .collect::<Vec<_>>(),
        )?;
    }
    if let Some(solution) = dual_solution {
        result["dual_equality_multipliers"] =
            serde_json::to_value(&solution.dual_equality_multipliers)?;
        if let Some(normalization) = solution.dual_normalization_multiplier {
            result["dual_normalization_multiplier"] = serde_json::to_value(normalization)?;
        }
        result["dual_psd_grams"] = serde_json::to_value(solution.dual_psd_grams)?;
    }
    if !nonnegative_cone_multipliers.is_empty() {
        result["dual_nonnegative_cone_multipliers"] =
            serde_json::to_value(&nonnegative_cone_multipliers)?;
        result["scaled_cap_row_multiplier"] = nonnegative_cone_multipliers[0].into();
        result["active_time_cap_multiplier"] = physical_active_time_cap_multiplier(
            &result["problem"],
            nonnegative_cone_multipliers[0],
        )?
        .into();
    }
    label_active_time_capped_result(&mut result);
    if let (Some(target), Some(margins)) = (interior_target, margins) {
        let shifted_gram_count = (0..psd_rows.len())
            .filter(|&block| target.gram_is_active(block))
            .count();
        let requested_active_gram_blocks = (0..psd_rows.len())
            .filter(|&block| target.gram_is_active(block))
            .collect::<Vec<_>>();
        let repair_active_gram_blocks = requested_active_gram_blocks
            .iter()
            .copied()
            .filter(|&block| !target.per_block_margins || margins[block] > 1e-8)
            .collect::<Vec<_>>();
        let minimum_margin = requested_active_gram_blocks
            .iter()
            .map(|&block| margins[block])
            .fold(f64::INFINITY, f64::min);
        let gram_minimum_eigenvalues =
            gram_minimum_eigenvalues.expect("interior solve has Gram diagnostics");
        let minimum_active_eigenvalue = gram_minimum_eigenvalues
            .iter()
            .enumerate()
            .filter_map(|(block, &value)| target.gram_is_active(block).then_some(value))
            .fold(f64::INFINITY, f64::min);
        let minimum_inactive_eigenvalue = gram_minimum_eigenvalues
            .iter()
            .enumerate()
            .filter_map(|(block, &value)| (!target.gram_is_active(block)).then_some(value))
            .fold(f64::INFINITY, f64::min);
        result["interior_margin"] = serde_json::json!({
            "fixed_bound_target": target.exact,
            "fixed_bound_target_float": target.value,
            "margin_mode": if target.per_block_margins { "per_block_average" } else { "uniform_minimum" },
            "per_block_margin_cap": target.margin_cap,
            "uniform_gram_margin": (!target.per_block_margins).then_some(minimum_margin),
            "minimum_requested_gram_margin": minimum_margin,
            "per_block_gram_margins": margins,
            "shifted_gram_count": shifted_gram_count,
            "unshifted_gram_count": psd_rows.len() - shifted_gram_count,
            "requested_active_gram_blocks": requested_active_gram_blocks,
            "active_gram_blocks": repair_active_gram_blocks,
            "zero_gram_threshold": target.zero_gram_threshold,
            "reference_eigenvalue_threshold": target.reference_eigenvalue_threshold,
            "active_set_reference": target.reference,
            "minimum_active_reconstructed_eigenvalue": minimum_active_eigenvalue,
            "minimum_inactive_reconstructed_eigenvalue": minimum_inactive_eigenvalue,
            "gram_minimum_reconstructed_eigenvalues": gram_minimum_eigenvalues,
            "representation": if native_bar_faces.is_some() {
                "active G_i = X_i + lambda*P_i with <I-P_i,X_i>=0 and X_i positive semidefinite; inactive G_i=X_i; the common lambda is maximized; exact affine, kernel, and PSD audits remain mandatory"
            } else if target.per_block_margins {
                "active Z_i = Y_i + lambda_i*I with lambda_i >= 0; inactive Z_i = Y_i; all Y_i positive semidefinite; objective maximizes the average lambda_i"
            } else {
                "active Z_i = Y_i + lambda*I; inactive Z_i = Y_i; all Y_i positive semidefinite"
            },
        });
    }
    Ok(result)
}

fn common_gram_margin_coefficients(
    problem: &ConicProblem,
    scalar_row_indices: &[Option<usize>],
    psd_rows: &[(usize, usize, usize)],
    target: &InteriorMarginTarget,
    projectors: &[Option<&[Vec<f64>]>],
) -> Result<Vec<(usize, f64)>> {
    use std::collections::BTreeMap;

    let mut coefficients = BTreeMap::<usize, f64>::new();
    for (block, block_coefficients) in
        gram_margin_coefficients_by_block(problem, scalar_row_indices, psd_rows, projectors)?
            .into_iter()
            .enumerate()
    {
        if target.gram_is_active(block) {
            for (constraint, value) in block_coefficients {
                *coefficients.entry(constraint).or_default() += value;
            }
        }
    }
    Ok(coefficients
        .into_iter()
        .filter(|(_, value)| *value != 0.0)
        .collect())
}

fn gram_margin_coefficients_by_block(
    problem: &ConicProblem,
    scalar_row_indices: &[Option<usize>],
    psd_rows: &[(usize, usize, usize)],
    projectors: &[Option<&[Vec<f64>]>],
) -> Result<Vec<Vec<(usize, f64)>>> {
    use std::collections::BTreeMap;

    if projectors.len() != psd_rows.len() {
        bail!("Gram margin projector count does not match the PSD partition")
    }
    let mut coefficients = vec![BTreeMap::<usize, f64>::new(); psd_rows.len()];
    for &(row, constraint, value) in &problem.a.entries {
        if scalar_row_indices[row].is_some() {
            continue;
        }
        let block = psd_rows.partition_point(|&(_, end, _)| end <= row);
        let &(start, end, side) = psd_rows
            .get(block)
            .context("PSD row is outside the cone partition")?;
        if row < start || row >= end {
            bail!("nonzero entry belongs to an unsupported cone")
        }
        let (matrix_row, matrix_column, matrix_value) =
            upper_svec_to_lower_entry(row - start, side, value)?;
        let projector_value = projectors[block].map_or_else(
            || {
                if matrix_row == matrix_column {
                    1.0
                } else {
                    0.0
                }
            },
            |projector| projector[matrix_row][matrix_column],
        );
        if projector_value != 0.0 {
            let trace_scale = if matrix_row == matrix_column {
                1.0
            } else {
                2.0
            };
            *coefficients[block].entry(constraint).or_default() +=
                trace_scale * matrix_value * projector_value;
        }
    }
    Ok(coefficients
        .into_iter()
        .map(|block| {
            block
                .into_iter()
                .filter(|(_, value)| *value != 0.0)
                .collect()
        })
        .collect())
}

fn dyadic(value: f64, bits: u32) -> Result<String> {
    if bits > 60 {
        bail!("--dyadic-bits must be at most 60")
    }
    if !value.is_finite() {
        bail!("cannot exactify a non-finite solver value")
    }
    let denominator = 1_i128 << bits;
    let scaled = value * denominator as f64;
    if scaled.abs() > i128::MAX as f64 {
        bail!("solver value is too large for dyadic exactification")
    }
    let numerator = scaled.round() as i128;
    Ok(Rational::new(numerator, denominator).to_string())
}

#[derive(serde::Serialize)]
struct SplitFaceBuildReport {
    eigenvalue_cutoff: f64,
    seeded_eigenvalue_floor: f64,
    basis_dyadic_bits: u32,
    coordinate_dyadic_bits: u32,
    total_face_rank: usize,
    full_face_block_count: usize,
    partial_face_block_count: usize,
    zero_face_block_count: usize,
    minimum_retained_floating_eigenvalue: f64,
    minimum_seeded_floating_eigenvalue: f64,
    maximum_discarded_floating_eigenvalue: f64,
    representation: &'static str,
}

fn build_split_face_blocks(
    matrices: &[Vec<Vec<f64>>],
    inactive: &[bool],
    cutoff: f64,
    eigenvalue_floor: f64,
    basis_bits: u32,
    coordinate_bits: u32,
) -> Result<(Vec<SplitFaceBlock>, SplitFaceBuildReport)> {
    if matrices.len() != inactive.len() {
        bail!("internal face builder Gram-mask count mismatch")
    }
    let mut faces = Vec::with_capacity(matrices.len());
    let mut total_face_rank = 0;
    let mut full_face_block_count = 0;
    let mut partial_face_block_count = 0;
    let mut zero_face_block_count = 0;
    let mut minimum_retained = f64::INFINITY;
    let mut minimum_seeded = f64::INFINITY;
    let mut maximum_discarded = f64::NEG_INFINITY;
    for (block, (matrix, &inactive)) in matrices.iter().zip(inactive).enumerate() {
        let side = matrix.len();
        let numeric = nalgebra::DMatrix::from_fn(side, side, |row, column| matrix[row][column]);
        let eigen = numeric.symmetric_eigen();
        if eigen.eigenvalues.iter().any(|value| !value.is_finite()) {
            bail!("Gram block {block} has a non-finite eigenvalue")
        }
        let retained = if inactive {
            Vec::new()
        } else {
            eigen
                .eigenvalues
                .iter()
                .enumerate()
                .filter_map(|(index, &value)| (value > cutoff).then_some(index))
                .collect::<Vec<_>>()
        };
        for (index, &value) in eigen.eigenvalues.iter().enumerate() {
            if retained.contains(&index) {
                minimum_retained = minimum_retained.min(value);
            } else {
                maximum_discarded = maximum_discarded.max(value);
            }
        }
        let rank = retained.len();
        for &index in &retained {
            minimum_seeded = minimum_seeded
                .max(0.0)
                .min(eigen.eigenvalues[index].max(eigenvalue_floor));
        }
        total_face_rank += rank;
        if rank == 0 {
            zero_face_block_count += 1;
            faces.push(SplitFaceBlock {
                basis: vec![Vec::new(); side],
                coordinates: Vec::new(),
            });
            continue;
        }
        if rank == side {
            full_face_block_count += 1;
            let minimum = retained
                .iter()
                .map(|&index| eigen.eigenvalues[index].max(eigenvalue_floor))
                .fold(f64::INFINITY, f64::min);
            let (scale, exact_scale) = dyadic_with_value(minimum.sqrt(), basis_bits)?;
            if exact_scale == 0.0 {
                bail!(
                    "Gram block {block} full-face scale rounded to zero; increase --face-basis-bits"
                )
            }
            let mut basis = vec![vec!["0".into(); side]; side];
            for (index, row) in basis.iter_mut().enumerate() {
                row[index] = scale.clone();
            }
            let scale_squared = exact_scale * exact_scale;
            let seeded = if retained
                .iter()
                .all(|&index| eigen.eigenvalues[index] >= eigenvalue_floor)
            {
                nalgebra::DMatrix::from_fn(side, side, |row, column| matrix[row][column])
            } else {
                let diagonal = nalgebra::DMatrix::from_diagonal(
                    &eigen.eigenvalues.map(|value| value.max(eigenvalue_floor)),
                );
                &eigen.eigenvectors * diagonal * eigen.eigenvectors.transpose()
            };
            let coordinates = symmetric_dyadic_matrix(side, coordinate_bits, |row, column| {
                seeded[(row, column)] / scale_squared
            })?;
            faces.push(SplitFaceBlock { basis, coordinates });
            continue;
        }
        partial_face_block_count += 1;
        let mut basis = vec![vec![String::new(); rank]; side];
        for (face_column, &eigen_column) in retained.iter().enumerate() {
            let scale = eigen.eigenvalues[eigen_column].max(eigenvalue_floor).sqrt();
            for (row, values) in basis.iter_mut().enumerate() {
                values[face_column] =
                    dyadic(eigen.eigenvectors[(row, eigen_column)] * scale, basis_bits)?;
            }
            if basis.iter().all(|row| row[face_column] == "0") {
                bail!(
                    "Gram block {block} face column {face_column} rounded to zero; increase --face-basis-bits"
                )
            }
        }
        let mut coordinates = vec![vec!["0".into(); rank]; rank];
        for (index, row) in coordinates.iter_mut().enumerate() {
            row[index] = "1".into();
        }
        faces.push(SplitFaceBlock { basis, coordinates });
    }
    if minimum_retained == f64::INFINITY {
        minimum_retained = 0.0;
    }
    if maximum_discarded == f64::NEG_INFINITY {
        maximum_discarded = 0.0;
    }
    if minimum_seeded == f64::INFINITY {
        minimum_seeded = 0.0;
    }
    Ok((
        faces,
        SplitFaceBuildReport {
            eigenvalue_cutoff: cutoff,
            seeded_eigenvalue_floor: eigenvalue_floor,
            basis_dyadic_bits: basis_bits,
            coordinate_dyadic_bits: coordinate_bits,
            total_face_rank,
            full_face_block_count,
            partial_face_block_count,
            zero_face_block_count,
            minimum_retained_floating_eigenvalue: minimum_retained,
            minimum_seeded_floating_eigenvalue: minimum_seeded,
            maximum_discarded_floating_eigenvalue: maximum_discarded,
            representation: "exact dyadic F K F^T; full faces use scaled identity F, partial faces use rounded positive eigenvectors weighted by sqrt(eigenvalue)",
        },
    ))
}

fn dyadic_with_value(value: f64, bits: u32) -> Result<(String, f64)> {
    let exact = dyadic(value, bits)?;
    let parsed = exact.parse::<Rational>().map_err(anyhow::Error::msg)?;
    let reconstructed = parsed.numerator as f64 / parsed.denominator as f64;
    Ok((exact, reconstructed))
}

#[allow(clippy::needless_range_loop)]
fn symmetric_dyadic_matrix(
    side: usize,
    bits: u32,
    mut value: impl FnMut(usize, usize) -> f64,
) -> Result<Vec<Vec<String>>> {
    let mut matrix = vec![vec![String::new(); side]; side];
    for column in 0..side {
        for row in 0..=column {
            let exact = dyadic(value(row, column), bits)?;
            matrix[row][column] = exact.clone();
            matrix[column][row] = exact;
        }
    }
    Ok(matrix)
}

#[allow(clippy::needless_range_loop)]
fn replace_split_certificate_from_floating(
    certificate: &mut SplitExactDualCertificate,
    structure: &stationary_hausdorff_split::StationaryHausdorffSplitStructure,
    dual: &FloatingDualSolution,
    dyadic_bits: u32,
) -> Result<()> {
    dual.validate().map_err(anyhow::Error::msg)?;
    if dual.dual_equality_multipliers.len() != structure.liouville_equality_count {
        bail!("direct native-bar solution has the wrong Liouville multiplier count")
    }
    let normalization = dual
        .dual_normalization_multiplier
        .context("direct native-bar solution has no normalization multiplier")?;
    if dual
        .dual_psd_grams
        .blocks
        .iter()
        .map(|block| block.side)
        .ne(structure.psd_block_sides.iter().copied())
    {
        bail!("direct native-bar solution Gram sides do not match the split structure")
    }
    certificate.liouville_multipliers_by_cell = dual
        .dual_equality_multipliers
        .chunks(structure.liouville_equality_count_per_cell)
        .map(|cell| {
            cell.iter()
                .map(|&value| dyadic(value, dyadic_bits))
                .collect::<Result<Vec<_>>>()
        })
        .collect::<Result<Vec<_>>>()?;
    certificate.normalization = dyadic(normalization, dyadic_bits)?;
    let mut certificate_grams = certificate
        .occupation_grams_by_cell
        .iter_mut()
        .flatten()
        .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
        .chain(certificate.terminal_grams_by_cell.iter_mut().flatten());
    for block in &dual.dual_psd_grams.blocks {
        let mut matrix = vec![vec![String::new(); block.side]; block.side];
        let mut position = 0;
        for column in 0..block.side {
            for row in 0..=column {
                let exact = dyadic(block.upper_triangle[position], dyadic_bits)?;
                matrix[row][column] = exact.clone();
                matrix[column][row] = exact;
                position += 1;
            }
        }
        *certificate_grams
            .next()
            .expect("validated direct native-bar Gram count") = matrix;
    }
    debug_assert!(certificate_grams.next().is_none());
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn repair_split_candidate_on_faces(
    certificate: &mut SplitExactDualCertificate,
    faces: Vec<SplitFaceBlock>,
    build_report: SplitFaceBuildReport,
    face_correction_cutoff: f64,
    face_basis_bits: u32,
    face_eigenvalue_floor: f64,
    dyadic_bits: u32,
    face_zero_correction: bool,
    face_known_span: Option<usize>,
    output: &std::path::Path,
) -> Result<serde_json::Value> {
    certificate.provenance.as_mut().expect("provenance exists")["face_build"] =
        serde_json::to_value(build_report)?;
    let face_report = match repair_split_exact_identity_on_faces(
        certificate,
        &faces,
        dyadic_bits,
        face_zero_correction,
        face_known_span,
    ) {
        Ok(report) => report,
        Err(error) => {
            certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                "failed_face_exact_identity_repair".into();
            certificate.provenance.as_mut().expect("provenance exists")["failure"] =
                error.to_string().into();
            write_split_candidate(output, certificate)?;
            return Err(error).context("split candidate failed face-parameterized repair");
        }
    };
    let face_scope = serde_json::json!({
        "mode": "exact_face_parameterized_F_K_F_transpose",
        "face_cutoff": face_correction_cutoff,
        "face_basis_bits": face_basis_bits,
        "face_eigenvalue_floor": face_eigenvalue_floor,
        "identity_span": face_report.identity_span,
        "identity_span_scan_complete": face_report.identity_span_scan_complete,
        "known_span": face_known_span,
        "coefficient_count": face_report.coefficient_count,
        "face_variable_count": face_report.face_variable_count,
        "zero_correction": face_zero_correction,
    });
    certificate.provenance.as_mut().expect("provenance exists")["face_repair"] =
        serde_json::to_value(&face_report)?;
    if face_zero_correction {
        let failure = format!(
            "zero-correction sanity leaves {} nonzero exact coefficient identities; face span is {}/{}",
            face_report.nonzero_exact_residual_count_after_repair,
            face_report.identity_span,
            face_report.coefficient_count
        );
        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
            "face_zero_correction_sanity_expected_failure".into();
        certificate.provenance.as_mut().expect("provenance exists")["failure"] =
            failure.clone().into();
        certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
            "rejected zero-correction candidate; proves no bound".into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_gram_scope"] =
            face_scope;
        write_split_candidate(output, certificate)?;
        bail!(failure)
    }
    if !face_report.coordinate_matrices_exactly_positive_semidefinite {
        let failure = format!(
            "face correction left a non-PSD exact coordinate matrix: {}; minimum reconstructed coordinate eigenvalue is {}",
            face_report
                .coordinate_psd_failure
                .as_deref()
                .unwrap_or("exact LDL failed without a recorded reason"),
            face_report.minimum_reconstructed_coordinate_eigenvalue
        );
        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
            "failed_face_coordinate_psd".into();
        certificate.provenance.as_mut().expect("provenance exists")["failure"] =
            failure.clone().into();
        certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
            "rejected exact candidate; proves no bound".into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_gram_scope"] =
            face_scope;
        write_split_candidate(output, certificate)?;
        bail!(failure)
    }
    if !face_report.exact_identity_closed {
        let failure = format!(
            "face correction spans {}/{} coefficient identities and leaves {} nonzero exact residuals",
            face_report.identity_span,
            face_report.coefficient_count,
            face_report.nonzero_exact_residual_count_after_repair
        );
        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
            "failed_face_identity_span_or_closure".into();
        certificate.provenance.as_mut().expect("provenance exists")["failure"] =
            failure.clone().into();
        certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
            "rejected exact candidate; proves no bound".into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_gram_scope"] =
            face_scope;
        write_split_candidate(output, certificate)?;
        bail!(failure)
    }
    Ok(face_scope)
}

#[allow(clippy::too_many_arguments)]
fn exactify_stationary(
    order: u8,
    target: String,
    dyadic_bits: u32,
    gram_shift_ulps: u64,
    seed: Option<PathBuf>,
    blend: String,
    residual_upper: String,
    output: PathBuf,
) -> Result<()> {
    if dyadic_bits > 60 {
        bail!("--dyadic-bits must be at most 60")
    }
    let assembled = stationary_torus::assemble_exactification(order).map_err(anyhow::Error::msg)?;
    let metadata = serde_json::to_value(&assembled.structure)?;
    let solved = solve_mosek_dual_sdp(
        &assembled.conic,
        metadata,
        true,
        None,
        false,
        false,
        None,
        NativeSdpMode::Standard,
        None,
    )?;
    let dual = FloatingDualSolution {
        dual_equality_multipliers: serde_json::from_value(
            solved["dual_equality_multipliers"].clone(),
        )?,
        dual_normalization_multiplier: None,
        dual_psd_grams: serde_json::from_value(solved["dual_psd_grams"].clone())?,
    };
    let equalities = dual
        .dual_equality_multipliers
        .iter()
        .map(|&value| dyadic(value, dyadic_bits))
        .collect::<Result<Vec<_>>>()?;
    let grams = dual
        .full_gram_matrices()
        .map_err(anyhow::Error::msg)?
        .iter()
        .map(|matrix| {
            matrix
                .iter()
                .enumerate()
                .map(|(row_index, row)| {
                    row.iter()
                        .enumerate()
                        .map(|(column_index, &value)| {
                            let mut value = value;
                            if row_index == column_index {
                                value += gram_shift_ulps as f64 / (1_u64 << dyadic_bits) as f64;
                            }
                            dyadic(value, dyadic_bits)
                        })
                        .collect::<Result<Vec<_>>>()
                })
                .collect::<Result<Vec<_>>>()
        })
        .collect::<Result<Vec<_>>>()?;
    let objective = solved["objective"]
        .as_f64()
        .context("MOSEK result has no objective")?;
    let target_float = target.parse::<Rational>().map_err(anyhow::Error::msg)?;
    let target_float = target_float.numerator as f64 / target_float.denominator as f64;
    let mut certificate = ExactDualCertificate {
        schema: "minexposure/stationary-exact-dual-v2".into(),
        order,
        bound_target: target,
        equalities,
        grams,
        residual_policy: Some("cost_relative".into()),
        residual_upper: Some(residual_upper),
        formulation_hash: Some(assembled.structure.formulation_hash.clone()),
        provenance: Some(serde_json::json!({
            "solver": "MOSEK 11.2.3 via native Rust API",
            "solver_form": "dualized native SDP in source-ordered integer facial basis",
            "floating_objective": objective,
            "exactification_loss": objective - target_float,
            "dyadic_bits": dyadic_bits,
            "gram_diagonal_shift_ulps": gram_shift_ulps,
            "formulation_hash": assembled.structure.formulation_hash,
        })),
        exposure_upper: None,
        normalization: None,
        occupation_grams: Vec::new(),
        terminal_grams: Vec::new(),
    };
    if let Some(seed) = seed {
        let seed: ExactDualCertificate = serde_json::from_slice(&fs::read(seed)?)?;
        let blend = blend.parse::<Rational>().map_err(anyhow::Error::msg)?;
        blend_with_exact_seed(&seed, &mut certificate, blend.numerator, blend.denominator)
            .context("could not blend the rounded dual with the exact interior seed")?;
        if let Some(provenance) = certificate.provenance.as_mut() {
            provenance["exact_seed_blend"] = blend.to_string().into();
        }
    }
    let before_repair = residual_diagnostics(&certificate)?;
    repair_exact_identity(&mut certificate)
        .context("could not project the rounded dual onto the exact coefficient identity")?;
    if let Some(provenance) = certificate.provenance.as_mut() {
        provenance["pre_repair_low_degree_terms"] = before_repair.0.into();
        provenance["pre_repair_coefficient_upper"] = before_repair.1.into();
    }
    let report = audit_exact_certificate(&certificate)
        .context("rounded payload failed its optimizer-free exact audit")?;
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&output, json(&certificate)?)?;
    print!("{}", json(&report)?);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn exactify_hausdorff_split(
    input: &std::path::Path,
    order: u8,
    knots: &str,
    target: String,
    dyadic_bits: u32,
    gram_shift_ulps: u64,
    zero_gram_threshold: f64,
    unrestricted_repair: bool,
    cone_margin: f64,
    cone_margin_cap: f64,
    cone_gram_scale_target: f64,
    cone_facial_zero_threshold: f64,
    cone_facial_rotation_threshold: f64,
    cone_facial_rotation_bits: u32,
    cone_facial_rotation_recompute_each_pass: bool,
    cone_correction_bits: u32,
    cone_solver_log: bool,
    cone_max_iterations: i32,
    resume: bool,
    resume_exact_closure: bool,
    checkpoint_before_cone: bool,
    checkpoint_after_cone_pass: bool,
    checkpoint_before_native_audit: bool,
    cone_solution_from: Option<&std::path::Path>,
    repair_preference: Option<&std::path::Path>,
    export_repair_data: Option<&std::path::Path>,
    face_correction_cutoff: Option<f64>,
    face_basis_bits: u32,
    face_eigenvalue_floor: f64,
    face_zero_correction: bool,
    face_known_span: Option<usize>,
    output: &std::path::Path,
) -> Result<()> {
    let pipeline_started = std::time::Instant::now();
    if dyadic_bits > 60 {
        bail!("--dyadic-bits must be at most 60")
    }
    if cone_correction_bits > 60 {
        bail!("--cone-correction-bits must be at most 60")
    }
    if repair_preference.is_some() && cone_margin > 0.0 {
        bail!("--repair-preference requires --cone-margin 0: the cone path has its own repair")
    }
    if face_basis_bits > 60 {
        bail!("--face-basis-bits must be at most 60")
    }
    if !zero_gram_threshold.is_finite() || zero_gram_threshold < 0.0 {
        bail!("--zero-gram-threshold must be finite and nonnegative")
    }
    if !cone_margin.is_finite() || cone_margin < 0.0 {
        bail!("--cone-margin must be finite and nonnegative")
    }
    if cone_max_iterations <= 0 {
        bail!("--cone-max-iterations must be positive")
    }
    if !cone_margin_cap.is_finite() || cone_margin_cap <= 0.0 {
        bail!("--cone-margin-cap must be finite and positive")
    }
    if cone_margin > cone_margin_cap {
        bail!("--cone-margin cannot exceed --cone-margin-cap")
    }
    if !cone_gram_scale_target.is_finite() || cone_gram_scale_target <= 0.0 {
        bail!("--cone-gram-scale-target must be finite and positive")
    }
    if !cone_facial_zero_threshold.is_finite() || cone_facial_zero_threshold < 0.0 {
        bail!("--cone-facial-zero-threshold must be finite and nonnegative")
    }
    if !cone_facial_rotation_threshold.is_finite() || cone_facial_rotation_threshold < 0.0 {
        bail!("--cone-facial-rotation-threshold must be finite and nonnegative")
    }
    if cone_facial_rotation_bits > 60 {
        bail!("--cone-facial-rotation-bits must be at most 60")
    }
    if cone_margin == 0.0 && cone_gram_scale_target != 1e-4 {
        bail!("--cone-gram-scale-target requires a positive --cone-margin")
    }
    if cone_margin == 0.0 && cone_facial_zero_threshold != 0.0 {
        bail!("--cone-facial-zero-threshold requires a positive --cone-margin")
    }
    if cone_facial_rotation_threshold > 0.0 && cone_margin == 0.0 {
        bail!("--cone-facial-rotation-threshold requires a positive --cone-margin")
    }
    if cone_facial_rotation_recompute_each_pass && cone_facial_rotation_threshold == 0.0 {
        bail!(
            "--cone-facial-rotation-recompute-each-pass requires a positive --cone-facial-rotation-threshold"
        )
    }
    if resume && resume_exact_closure {
        bail!("--resume and --resume-exact-closure are mutually exclusive")
    }
    if checkpoint_before_cone && (cone_margin == 0.0 || resume || resume_exact_closure) {
        bail!(
            "--checkpoint-before-cone requires a positive --cone-margin and cannot be combined with a resume flag"
        )
    }
    if checkpoint_after_cone_pass && (cone_margin == 0.0 || resume_exact_closure) {
        bail!(
            "--checkpoint-after-cone-pass requires a positive --cone-margin and cannot be combined with --resume-exact-closure"
        )
    }
    if cone_solution_from.is_some() && (!resume || cone_margin == 0.0) {
        bail!("--cone-solution-from requires --resume and a positive --cone-margin")
    }
    if face_correction_cutoff.is_some_and(|cutoff| !cutoff.is_finite()) {
        bail!("--face-correction-cutoff must be finite")
    }
    if !face_eigenvalue_floor.is_finite() || face_eigenvalue_floor <= 0.0 {
        bail!("--face-eigenvalue-floor must be positive and finite")
    }
    if face_correction_cutoff.is_some() && unrestricted_repair {
        bail!("--face-correction-cutoff cannot be combined with --unrestricted-repair")
    }
    if face_correction_cutoff.is_some()
        && (repair_preference.is_some() || export_repair_data.is_some())
    {
        bail!(
            "--face-correction-cutoff cannot be combined with --repair-preference or --export-repair-data: the face path has its own repair"
        )
    }
    if face_correction_cutoff.is_some()
        && (cone_margin > 0.0 || resume || resume_exact_closure || cone_solution_from.is_some())
    {
        bail!("--face-correction-cutoff cannot be combined with cone repair or resume flags")
    }
    let grid = knots.parse::<SplitGrid>().map_err(anyhow::Error::msg)?;
    let structure =
        stationary_hausdorff_split::structure(order, &grid).map_err(anyhow::Error::msg)?;
    let canonical_target = target
        .parse::<Rational>()
        .map_err(anyhow::Error::msg)?
        .to_string();
    let mut resumed_cone_pass_count = 0_usize;
    let mut resume_after_cone = resume_exact_closure;
    let resumed_certificate = if resume || resume_exact_closure {
        let file = fs::File::open(output).with_context(|| {
            format!(
                "resume requires an existing split checkpoint at {}",
                output.display()
            )
        })?;
        let certificate: SplitExactDualCertificate =
            serde_json::from_reader(std::io::BufReader::new(file))?;
        if certificate.order != order
            || certificate.knots != structure.knots
            || certificate.split_grid_hash != structure.split_grid_hash
            || certificate.formulation_hash != structure.formulation_hash
            || certificate.bound_target != canonical_target
        {
            bail!("split checkpoint metadata do not match the requested exact model")
        }
        let checkpoint_status = certificate
            .provenance
            .as_ref()
            .and_then(|provenance| provenance.get("exactification_status"))
            .and_then(serde_json::Value::as_str);
        if resume
            && matches!(
                checkpoint_status,
                Some(
                    "cone_face_selected_pending_psd_reclosure"
                        | "axis_cone_face_stalled_pending_rotated_repair"
                        | "rotated_kernel_face_selected_pending_cone_repair"
                )
            )
        {
            resumed_cone_pass_count = certificate
                .provenance
                .as_ref()
                .and_then(|provenance| provenance.get("cone_repair_passes"))
                .and_then(serde_json::Value::as_array)
                .map(Vec::len)
                .or_else(|| {
                    (checkpoint_status == Some("rotated_kernel_face_selected_pending_cone_repair"))
                        .then_some(0)
                })
                .context("mid-cone checkpoint has no completed cone-pass history")?;
            let minimum = minimum_reconstructed_split_gram_eigenvalue(&certificate)
                .context("mid-cone checkpoint failed reconstructed Gram validation")?;
            if !minimum.is_finite() {
                bail!("mid-cone checkpoint has a non-finite reconstructed Gram eigenvalue")
            }
            if cone_solution_from.is_some() {
                bail!("--cone-solution-from cannot be used after a completed cone pass")
            }
        } else if resume
            && matches!(
                checkpoint_status,
                Some(
                    "passed_reconstructed_cone_margin_pending_exact_closure"
                        | "reconstructed_semidefinite_cone_face_pending_exact_closure"
                )
            )
        {
            resume_after_cone = true;
            resumed_cone_pass_count = certificate
                .provenance
                .as_ref()
                .and_then(|provenance| provenance.get("cone_repair_passes"))
                .and_then(serde_json::Value::as_array)
                .map(Vec::len)
                .unwrap_or(0);
            let minimum = minimum_reconstructed_split_gram_eigenvalue(&certificate)
                .context("post-cone checkpoint failed reconstructed Gram validation")?;
            if !minimum.is_finite() || minimum < -1e-8 {
                bail!(
                    "post-cone checkpoint has reconstructed minimum Gram eigenvalue {minimum:e}, below resume gate -1e-8"
                )
            }
        } else if resume {
            check_split_exact_affine_closure(&certificate)
                .context("pre-cone checkpoint failed exact affine resume validation")?;
        } else {
            let minimum = minimum_reconstructed_split_gram_eigenvalue(&certificate)
                .context("post-cone checkpoint failed reconstructed Gram validation")?;
            if !minimum.is_finite() || minimum < -1e-8 {
                bail!(
                    "post-cone checkpoint has reconstructed minimum Gram eigenvalue {minimum:e}, below resume gate -1e-8"
                )
            }
        }
        Some(certificate)
    } else {
        None
    };
    let seed_active_gram_blocks;
    let mut face_configuration = None;
    let mut certificate = if let Some(certificate) = resumed_certificate {
        seed_active_gram_blocks = certificate
            .provenance
            .as_ref()
            .and_then(|provenance| provenance.pointer("/interior_margin_seed/active_gram_blocks"))
            .map(|blocks| {
                blocks
                    .as_array()
                    .context("split checkpoint active Gram list is not an array")?
                    .iter()
                    .map(|block| {
                        block
                            .as_u64()
                            .context("split checkpoint active Gram index is not unsigned")
                            .and_then(|block| usize::try_from(block).map_err(anyhow::Error::from))
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .transpose()?;
        certificate
    } else {
        let file = fs::File::open(input)?;
        let seed: SplitFloatingSeed = serde_json::from_reader(std::io::BufReader::new(file))?;
        if let Some(active_time_cap) = &seed.problem.active_time_cap {
            bail!(
                "active-time-capped seed (T={active_time_cap}, scope={}) cannot be exactified as an all-duration split v1 certificate",
                seed.problem
                    .bound_scope
                    .as_deref()
                    .unwrap_or(stationary_hausdorff_split::ACTIVE_TIME_CAPPED_BOUND_SCOPE)
            )
        }
        if seed.problem.order != order
            || seed.problem.knots != structure.knots
            || seed.problem.split_grid_hash != structure.split_grid_hash
            || seed.problem.formulation_hash != structure.formulation_hash
        {
            bail!("floating seed metadata do not match the requested exact split model")
        }
        let SplitFloatingSeed {
            dual,
            interior_margin,
            primal_objective,
            dual_objective,
            ..
        } = seed;
        dual.validate().map_err(anyhow::Error::msg)?;
        if dual.dual_equality_multipliers.len() != structure.liouville_equality_count {
            bail!("floating seed has the wrong split Liouville multiplier count")
        }
        let normalization = dual
            .dual_normalization_multiplier
            .context("floating split seed has no normalization multiplier")?;
        if dual
            .dual_psd_grams
            .blocks
            .iter()
            .map(|block| block.side)
            .ne(structure.psd_block_sides.iter().copied())
        {
            bail!("floating seed Gram sides do not match the split structure")
        }

        let active_gram_blocks = interior_margin
            .as_ref()
            .and_then(|margin| margin.get("active_gram_blocks"))
            .map(|blocks| {
                blocks
                    .as_array()
                    .context("interior seed active Gram list is not an array")?
                    .iter()
                    .map(|block| {
                        block
                            .as_u64()
                            .context("interior seed active Gram index is not unsigned")
                            .and_then(|block| usize::try_from(block).map_err(anyhow::Error::from))
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .transpose()?;
        if active_gram_blocks.as_ref().is_some_and(|blocks| {
            blocks
                .iter()
                .any(|&block| block >= structure.psd_block_sides.len())
        }) {
            bail!("interior seed active Gram index is out of range")
        }
        let active_gram_mask = active_gram_blocks.as_ref().map(|blocks| {
            let mut mask = vec![false; structure.psd_block_sides.len()];
            for &block in blocks {
                mask[block] = true;
            }
            mask
        });
        seed_active_gram_blocks = active_gram_blocks;

        let spectral_started = std::time::Instant::now();
        let mut floating_grams = dual.full_gram_matrices().map_err(anyhow::Error::msg)?;
        let gram_spectra = floating_grams
            .iter()
            .map(|matrix| {
                let side = matrix.len();
                let eigenvalues =
                    nalgebra::DMatrix::from_fn(side, side, |row, column| matrix[row][column])
                        .symmetric_eigen()
                        .eigenvalues;
                let maximum_absolute_entry = matrix
                    .iter()
                    .flatten()
                    .map(|value| value.abs())
                    .fold(0.0, f64::max);
                (eigenvalues.min(), eigenvalues.max(), maximum_absolute_entry)
            })
            .collect::<Vec<_>>();
        let minimum_eigenvalue_before_face_reduction = gram_spectra
            .iter()
            .map(|entry| entry.0)
            .fold(f64::INFINITY, f64::min);
        let spectral_seconds = spectral_started.elapsed().as_secs_f64();
        let inactive_grams = gram_spectra
            .iter()
            .map(|entry| entry.2 <= zero_gram_threshold)
            .collect::<Vec<_>>();
        let margin_active_grams = inactive_grams
            .iter()
            .enumerate()
            .map(|(block, &inactive)| {
                !inactive && active_gram_mask.as_ref().is_none_or(|mask| mask[block])
            })
            .collect::<Vec<_>>();
        let minimum_active_eigenvalue_before_shift = gram_spectra
            .iter()
            .zip(&margin_active_grams)
            .filter_map(|(entry, &active)| active.then_some(entry.0))
            .fold(f64::INFINITY, f64::min);
        let denominator = (1_u64 << dyadic_bits) as f64;
        let gram_shift = gram_shift_ulps as f64 / denominator;
        for ((matrix, &inactive), &margin_active) in floating_grams
            .iter_mut()
            .zip(&inactive_grams)
            .zip(&margin_active_grams)
        {
            if inactive {
                for value in matrix.iter_mut().flatten() {
                    *value = 0.0;
                }
            } else if margin_active {
                for (index, row) in matrix.iter_mut().enumerate() {
                    row[index] += gram_shift;
                }
            }
        }
        let minimum_active_eigenvalue_after_shift =
            minimum_active_eigenvalue_before_shift + gram_shift;
        if cone_margin == 0.0
            && (!minimum_active_eigenvalue_after_shift.is_finite()
                || minimum_active_eigenvalue_after_shift <= 0.0)
        {
            bail!(
                "requested Gram shift is not strict on the retained floating face: minimum active eigenvalue before shift {minimum_active_eigenvalue_before_shift:e}, after shift {minimum_active_eigenvalue_after_shift:e}"
            )
        }
        face_configuration = face_correction_cutoff
            .map(|cutoff| {
                build_split_face_blocks(
                    &floating_grams,
                    &inactive_grams,
                    cutoff,
                    face_eigenvalue_floor,
                    face_basis_bits,
                    dyadic_bits,
                )
            })
            .transpose()?;
        let exact_grams = floating_grams
            .iter()
            .map(|matrix| {
                matrix
                    .iter()
                    .map(|row| {
                        row.iter()
                            .map(|&value| dyadic(value, dyadic_bits))
                            .collect::<Result<Vec<_>>>()
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .collect::<Result<Vec<_>>>()?;
        let mut exact_grams = exact_grams.into_iter();
        let occupation_grams_by_cell = (0..structure.cell_count)
            .map(|_| {
                (0..structure.occupation_moment_block_count_per_cell
                    + structure.occupation_interval_block_count_per_cell
                    + structure.occupation_interval_diagonal_count_per_cell)
                    .map(|_| exact_grams.next().expect("validated occupation Gram count"))
                    .collect()
            })
            .collect();
        let interface_grams_by_knot = (0..structure.cell_count.saturating_sub(1))
            .map(|_| {
                (0..structure.interface_moment_block_count_per_interface)
                    .map(|_| exact_grams.next().expect("validated interface Gram count"))
                    .collect()
            })
            .collect();
        let terminal_grams_by_cell = (0..structure.cell_count)
            .map(|_| {
                (0..2)
                    .map(|_| exact_grams.next().expect("validated terminal Gram count"))
                    .collect()
            })
            .collect();
        debug_assert!(exact_grams.next().is_none());
        let per_cell_equalities = structure.liouville_equality_count_per_cell;
        let liouville_multipliers_by_cell = dual
            .dual_equality_multipliers
            .chunks(per_cell_equalities)
            .map(|cell| {
                cell.iter()
                    .map(|&value| dyadic(value, dyadic_bits))
                    .collect::<Result<Vec<_>>>()
            })
            .collect::<Result<Vec<_>>>()?;
        let target_value = target.parse::<Rational>().map_err(anyhow::Error::msg)?;
        let target_float = target_value.numerator as f64 / target_value.denominator as f64;
        let floating_lower = if let Some(interior_margin) = &interior_margin {
            let fixed_target = interior_margin["fixed_bound_target"]
                .as_str()
                .context("interior seed has no exact fixed target")?
                .parse::<Rational>()
                .map_err(anyhow::Error::msg)?;
            if fixed_target != target_value {
                bail!(
                    "interior seed fixed target {} does not match exactification target {}",
                    fixed_target,
                    target_value
                )
            }
            target_float
        } else {
            primal_objective
                .zip(dual_objective)
                .map(|(primal, dual)| primal.min(dual))
                .context("floating seed has no primal/dual objective pair")?
        };
        let exact_normalization = dyadic(normalization, dyadic_bits)?;
        SplitExactDualCertificate {
            schema: SPLIT_EXACT_SCHEMA_V1.into(),
            order,
            knots: structure.knots.clone(),
            split_grid_hash: structure.split_grid_hash.clone(),
            formulation_hash: structure.formulation_hash.clone(),
            exposure_upper: structure.exposure_upper.to_string(),
            bound_target: target,
            equality_order: "cell_major_liouville_v1".into(),
            liouville_multipliers_by_cell,
            normalization: exact_normalization,
            gram_order: "occupation_by_cell_then_interface_by_knot_then_terminal_pair_by_cell_v1"
                .into(),
            occupation_grams_by_cell,
            interface_grams_by_knot,
            terminal_grams_by_cell,
            provenance: Some(serde_json::json!({
                "rigor": "candidate pending independent exact audit",
                "source_floating_seed": input,
                "solver": "MOSEK 11.2.3 via native Rust API",
                "solver_form": "dualized native split SDP",
                "floating_lower_objective": floating_lower,
                "exactification_loss_to_target": floating_lower - target_float,
                "interior_margin_seed": interior_margin,
                "dyadic_bits": dyadic_bits,
                "gram_diagonal_shift_ulps": gram_shift_ulps,
                "gram_diagonal_shift": gram_shift,
                "zero_gram_threshold": zero_gram_threshold,
                "zero_gram_count": inactive_grams.iter().filter(|&&inactive| inactive).count(),
                "minimum_floating_gram_eigenvalue_before_face_reduction": minimum_eigenvalue_before_face_reduction,
                "minimum_active_gram_eigenvalue_before_shift": minimum_active_eigenvalue_before_shift,
                "minimum_active_gram_eigenvalue_after_shift": minimum_active_eigenvalue_after_shift,
                "strict_floating_seed_on_retained_face_after_shift": minimum_active_eigenvalue_after_shift > 0.0,
                "cone_margin_requested": cone_margin,
                "cone_margin_cap": cone_margin_cap,
                "cone_correction_bits": cone_correction_bits,
                "seed_transport_and_spectral_seconds": spectral_seconds,
                "split_grid_hash": structure.split_grid_hash,
                "formulation_hash": structure.formulation_hash,
            })),
        }
    };
    let mut cone_repair_gram_blocks = certificate
        .provenance
        .as_ref()
        .and_then(|provenance| {
            provenance
                .get("cone_repair_gram_blocks")
                .or_else(|| provenance.get("pre_cone_exact_repair_gram_blocks"))
        })
        .map(|blocks| {
            blocks
                .as_array()
                .context("pre-cone exact-repair Gram support is not an array")?
                .iter()
                .map(|block| {
                    block
                        .as_u64()
                        .context("pre-cone exact-repair Gram index is not unsigned")
                        .and_then(|block| usize::try_from(block).map_err(anyhow::Error::from))
                })
                .collect::<Result<Vec<_>>>()
        })
        .transpose()?;
    if let (Some(repair_blocks), Some(interior_blocks)) = (
        cone_repair_gram_blocks.as_mut(),
        seed_active_gram_blocks.as_deref(),
    ) {
        repair_blocks.extend_from_slice(interior_blocks);
        repair_blocks.sort_unstable();
        repair_blocks.dedup();
    }
    if let Some(repair_blocks) = cone_repair_gram_blocks.as_ref() {
        certificate.provenance.as_mut().expect("provenance exists")["cone_repair_gram_blocks"] =
            serde_json::to_value(repair_blocks)?;
    }
    if cone_gram_scale_target != 1e-4 {
        certificate.provenance.as_mut().expect("provenance exists")["cone_gram_scale_target"] =
            cone_gram_scale_target.into();
    }
    if cone_facial_zero_threshold != 0.0 {
        certificate.provenance.as_mut().expect("provenance exists")["cone_facial_zero_threshold"] =
            cone_facial_zero_threshold.into();
    }
    let stored_rotation_configuration = certificate
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.get("cone_facial_rotation"))
        .and_then(|rotation| rotation.get("configuration"));
    let adopt_rotation_on_mid_cone_resume = resume
        && cone_facial_rotation_threshold > 0.0
        && stored_rotation_configuration.is_none()
        && resumed_cone_pass_count > 0
        && certificate
            .provenance
            .as_ref()
            .and_then(|provenance| provenance.get("exactification_status"))
            .and_then(serde_json::Value::as_str)
            .is_some_and(|status| {
                matches!(
                    status,
                    "cone_face_selected_pending_psd_reclosure"
                        | "axis_cone_face_stalled_pending_rotated_repair"
                )
            });
    if resume || resume_exact_closure {
        match (
            stored_rotation_configuration,
            cone_facial_rotation_threshold > 0.0,
        ) {
            (None, false) => {}
            (None, true) if adopt_rotation_on_mid_cone_resume => {}
            (Some(configuration), true)
                if configuration
                    .get("threshold")
                    .and_then(serde_json::Value::as_f64)
                    == Some(cone_facial_rotation_threshold)
                    && configuration
                        .get("bits")
                        .and_then(serde_json::Value::as_u64)
                        == Some(u64::from(cone_facial_rotation_bits))
                    && configuration
                        .get("recompute_each_pass")
                        .and_then(serde_json::Value::as_bool)
                        == Some(cone_facial_rotation_recompute_each_pass) => {}
            _ => bail!(
                "split checkpoint rotated-face configuration does not match the requested flags"
            ),
        }
    }
    if cone_facial_rotation_threshold > 0.0 && stored_rotation_configuration.is_none() {
        certificate.provenance.as_mut().expect("provenance exists")["cone_facial_rotation"] = serde_json::json!({
            "configuration": {
                "threshold": cone_facial_rotation_threshold,
                "bits": cone_facial_rotation_bits,
                "recompute_each_pass": cone_facial_rotation_recompute_each_pass,
                "frozen_after_first_pass": !cone_facial_rotation_recompute_each_pass,
            },
            "rigor": "candidate face only; exact affine closure and exact PSD audits remain mandatory",
            "adopted_on_mid_cone_resume": adopt_rotation_on_mid_cone_resume,
            "adopted_after_cone_pass_count": adopt_rotation_on_mid_cone_resume.then_some(resumed_cone_pass_count),
        });
    }
    let exact_repair_started = std::time::Instant::now();
    let mut checkpoint_serialization_wall_seconds = 0.0;
    let mut checkpoint_write_count = 0_usize;
    macro_rules! write_checkpoint {
        ($candidate:expr) => {{
            let started = std::time::Instant::now();
            let result = write_split_candidate(output, $candidate);
            checkpoint_serialization_wall_seconds += started.elapsed().as_secs_f64();
            checkpoint_write_count += 1;
            result
        }};
    }
    if let Some((faces, build_report)) = face_configuration {
        let repair_scope = repair_split_candidate_on_faces(
            &mut certificate,
            faces,
            build_report,
            face_correction_cutoff.expect("face configuration requires a cutoff"),
            face_basis_bits,
            face_eigenvalue_floor,
            dyadic_bits,
            face_zero_correction,
            face_known_span,
            output,
        )?;
        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
            "exact_identity_repaired_pending_audit".into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_identity_repaired"] =
            true.into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_wall_seconds"] =
            exact_repair_started.elapsed().as_secs_f64().into();
        certificate.provenance.as_mut().expect("provenance exists")["nonzero_exact_residual_count"] =
            0.into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_gram_scope"] =
            repair_scope;
    } else {
        let mut rotated_kernels = if cone_facial_rotation_threshold > 0.0 {
            certificate
                .provenance
                .as_ref()
                .and_then(|provenance| provenance.pointer("/cone_facial_rotation/states"))
                .map(|states| -> Result<Vec<SplitRotatedKernelState>> {
                    let states: Vec<SplitRotatedKernelState> =
                        serde_json::from_value(states.clone())
                            .context("could not parse rotated-kernel checkpoint states")?;
                    validate_split_rotated_gram_kernels(&certificate, &states)
                        .context("could not validate rotated-kernel checkpoint states")?;
                    Ok(states)
                })
                .transpose()?
        } else {
            None
        };
        if cone_margin > 0.0 && !resume_after_cone {
            if resume {
                let key = if resumed_cone_pass_count == 0 {
                    "resumed_from_exact_pre_cone_checkpoint"
                } else {
                    "resumed_from_cone_pass_checkpoint"
                };
                certificate.provenance.as_mut().expect("provenance exists")[key] = true.into();
            } else {
                let pre_cone_repair_started = std::time::Instant::now();
                let pre_cone_repair_result =
                    repair_split_exact_identity_componentwise_with_support(&mut certificate);
                let (pre_cone_repair, repair_gram_blocks) = match pre_cone_repair_result {
                    Ok(result) => result,
                    Err(error) => {
                        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                            "failed_pre_cone_exact_identity_repair".into();
                        certificate.provenance.as_mut().expect("provenance exists")["failure"] =
                            error.to_string().into();
                        write_split_candidate(output, &certificate)?;
                        return Err(error).context("split candidate failed pre-cone exact closure");
                    }
                };
                let exact_repair_gram_blocks = repair_gram_blocks;
                cone_repair_gram_blocks = Some(exact_repair_gram_blocks.clone());
                if let (Some(repair_blocks), Some(interior_blocks)) = (
                    cone_repair_gram_blocks.as_mut(),
                    seed_active_gram_blocks.as_deref(),
                ) {
                    repair_blocks.extend_from_slice(interior_blocks);
                    repair_blocks.sort_unstable();
                    repair_blocks.dedup();
                }
                let pre_cone_reconstructed_minimum =
                    minimum_reconstructed_split_gram_eigenvalue(&certificate)?;
                certificate.provenance.as_mut().expect("provenance exists")["pre_cone_exact_repair"] =
                    serde_json::to_value(&pre_cone_repair)?;
                certificate.provenance.as_mut().expect("provenance exists")["pre_cone_exact_repair_gram_blocks"] =
                    serde_json::to_value(&exact_repair_gram_blocks)?;
                certificate.provenance.as_mut().expect("provenance exists")["cone_repair_gram_blocks"] =
                    serde_json::to_value(
                        cone_repair_gram_blocks
                            .as_ref()
                            .expect("cone-repair Gram support exists"),
                    )?;
                certificate.provenance.as_mut().expect("provenance exists")["pre_cone_exact_repair_wall_seconds"] =
                    pre_cone_repair_started.elapsed().as_secs_f64().into();
                certificate.provenance.as_mut().expect("provenance exists")["pre_cone_reconstructed_minimum_gram_eigenvalue"] =
                    pre_cone_reconstructed_minimum.into();
                certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                    "pre_cone_exact_identity_repaired".into();
                write_checkpoint!(&certificate)?;
                if checkpoint_before_cone {
                    eprintln!(
                        "pre-cone exact closure checkpointed at {}; rerun with --resume",
                        output.display()
                    );
                    return Ok(());
                }
            }

            let mut reused_first_solution = cone_solution_from
                .map(|path| -> Result<serde_json::Value> {
                    let payload: serde_json::Value = serde_json::from_slice(&fs::read(path)?)?;
                    Ok(payload
                        .pointer("/provenance/cone_repair/solver")
                        .cloned()
                        .unwrap_or(payload))
                })
                .transpose()?;
            let mut cone_passes = if resumed_cone_pass_count == 0 {
                Vec::new()
            } else {
                certificate
                    .provenance
                    .as_ref()
                    .and_then(|provenance| provenance.get("cone_repair_passes"))
                    .and_then(serde_json::Value::as_array)
                    .cloned()
                    .expect("validated mid-cone checkpoint has pass history")
            };
            const MAX_CONE_REFINEMENT_PASSES: usize = 8;
            for pass in resumed_cone_pass_count..MAX_CONE_REFINEMENT_PASSES {
                let stage_started = std::time::Instant::now();
                let build_started = std::time::Instant::now();
                let rotation_enabled = cone_facial_rotation_threshold > 0.0;
                let near_null_before_rotation = rotation_enabled
                    .then(|| split_near_null_eigen_diagnostics(&certificate, 1e-6))
                    .transpose()?;
                let axis_face_stalled = adopt_rotation_on_mid_cone_resume
                    || cone_passes.last().is_some_and(|diagnostics| {
                        diagnostics
                            .get("gram_facial_zero_row_count")
                            .and_then(serde_json::Value::as_u64)
                            == Some(0)
                            && diagnostics
                                .get("reconstructed_minimum_gram_eigenvalue")
                                .and_then(serde_json::Value::as_f64)
                                .is_some_and(|minimum| minimum < -1e-8)
                    });
                let mut pre_rotation_zero_row_count = 0;
                let mut rotation_build = None;
                if rotation_enabled
                    && axis_face_stalled
                    && (rotated_kernels.is_none() || cone_facial_rotation_recompute_each_pass)
                {
                    let rotation_selection_started = std::time::Instant::now();
                    pre_rotation_zero_row_count =
                        zero_small_split_gram_rows(&mut certificate, cone_facial_zero_threshold)
                            .context(
                                "could not apply Gram-row reduction before rotated face selection",
                            )?;
                    let (states, report) = select_split_rotated_gram_kernels(
                        &certificate,
                        cone_facial_rotation_threshold,
                        cone_margin,
                        cone_facial_rotation_bits,
                    )
                    .context("could not select exact rotated Gram kernels")?;
                    certificate.provenance.as_mut().expect("provenance exists")["cone_facial_rotation"]
                        ["states"] = serde_json::to_value(&states)?;
                    let kernel_equation_count = states
                        .iter()
                        .map(|state| {
                            state.kernel.len() * state.kernel.first().map_or(0, std::vec::Vec::len)
                        })
                        .sum::<usize>();
                    let report = serde_json::to_value(report)?;
                    let rotation = &mut certificate.provenance.as_mut().expect("provenance exists")
                        ["cone_facial_rotation"];
                    rotation["selection"] = report.clone();
                    rotation["selection_wall_seconds"] =
                        rotation_selection_started.elapsed().as_secs_f64().into();
                    rotation["kernel_equation_count"] = kernel_equation_count.into();
                    rotation["near_null_eigenvectors_before_selection"] =
                        serde_json::to_value(&near_null_before_rotation)?;
                    rotation["pre_rotation_gram_zero_row_count"] =
                        pre_rotation_zero_row_count.into();
                    certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                        "rotated_kernel_face_selected_pending_cone_repair".into();
                    // Persist the candidate face and axis-vs-rotated
                    // diagnostic before the expensive native-bar build/solve
                    // so an OOM or interruption retains actionable evidence.
                    write_checkpoint!(&certificate)?;
                    rotation_build = Some(report);
                    rotated_kernels = Some(states);
                } else if rotation_enabled && rotated_kernels.is_none() {
                    let rotation = &mut certificate.provenance.as_mut().expect("provenance exists")
                        ["cone_facial_rotation"];
                    rotation["deferred_until_axis_face_stalls"] = true.into();
                    rotation["near_null_eigenvectors_before_deferred_pass"] =
                        serde_json::to_value(&near_null_before_rotation)?;
                    rotation["kernel_equation_count"] = 0.into();
                    certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                        "rotated_kernel_face_deferred_pending_axis_cone_repair".into();
                    write_checkpoint!(&certificate)?;
                }
                enum ConePassPlan {
                    Correction(minexposure_core::stationary_certificate::SplitConeRepairPlan),
                    Direct(SplitNativeBarFacePlan),
                }
                let (
                    repair_problem,
                    plan,
                    build_diagnostics,
                    problem_metadata,
                    direct_interior_target,
                ) = if let Some(kernels) = rotated_kernels.as_deref() {
                    let direct = stationary_hausdorff_split::assemble(order, &grid)
                        .map_err(anyhow::Error::msg)
                        .context(
                            "could not assemble the original split SDP for direct-bar repair",
                        )?;
                    let faces = build_split_native_bar_face_plan(&certificate, kernels)
                        .context("could not build the direct native-bar face plan")?;
                    let mut active_grams = vec![false; faces.gram_count];
                    for state in kernels {
                        active_grams[state.block] = state.kernel.first().map_or(0, Vec::len)
                            < structure.psd_block_sides[state.block];
                    }
                    if !active_grams.iter().any(|&active| active) {
                        bail!("direct native-bar repair has no nonzero rotated range face")
                    }
                    let interior_target = InteriorMarginTarget {
                        exact: certificate.bound_target.clone(),
                        value: certificate
                            .bound_target
                            .parse::<Rational>()
                            .map_err(anyhow::Error::msg)
                            .map(|value| value.numerator as f64 / value.denominator as f64)?,
                        active_grams: Some(active_grams),
                        zero_gram_threshold: 0.0,
                        reference: None,
                        reference_eigenvalue_threshold: None,
                        per_block_margins: false,
                        margin_cap: None,
                    };
                    let build = serde_json::json!({
                        "formulation": "original_split_sdp_direct_native_bar_faces",
                        "identity_constraint_count": direct.conic.q.len(),
                        "cone_row_count": direct.conic.a.rows,
                        "sparse_entry_count": direct.conic.a.entries.len(),
                        "bar_variable_count": structure.psd_block_sides.len(),
                        "native_bar_face_constraint_count": faces.blocks.len(),
                        "rotated_kernel_gram_count": kernels.len(),
                        "rotated_kernel_direction_count": kernels.iter().map(|state| state.kernel.first().map_or(0, Vec::len)).sum::<usize>(),
                        "rotated_kernel_equation_count": 0,
                        "correction_signature_kernel_row_count": 0,
                    });
                    let metadata = serde_json::to_value(&direct.structure)?;
                    (
                        direct.conic,
                        ConePassPlan::Direct(faces),
                        build,
                        metadata,
                        Some(interior_target),
                    )
                } else if pass == 0
                    && let Some(blocks) = cone_repair_gram_blocks.as_deref()
                {
                    let (problem, plan, diagnostics) =
                        build_split_bar_cone_repair_problem_scaled_restricted(
                            &certificate,
                            cone_margin,
                            cone_margin_cap,
                            cone_gram_scale_target,
                            blocks,
                        )?;
                    (
                        problem,
                        ConePassPlan::Correction(plan),
                        serde_json::to_value(diagnostics)?,
                        serde_json::json!({
                            "model": "stationary_torus_hausdorff_split_exact_support_first_pass_bar_cone_repair",
                            "order": order,
                            "knots": structure.knots,
                            "formulation_hash": structure.formulation_hash,
                            "target": certificate.bound_target,
                        }),
                        None,
                    )
                } else {
                    let (problem, plan, diagnostics) = build_split_bar_cone_repair_problem_scaled(
                        &certificate,
                        cone_margin,
                        cone_margin_cap,
                        cone_gram_scale_target,
                    )?;
                    (
                        problem,
                        ConePassPlan::Correction(plan),
                        serde_json::to_value(diagnostics)?,
                        serde_json::json!({
                            "model": "stationary_torus_hausdorff_split_exact_support_first_pass_bar_cone_repair",
                            "order": order,
                            "knots": structure.knots,
                            "formulation_hash": structure.formulation_hash,
                            "target": certificate.bound_target,
                        }),
                        None,
                    )
                };
                let build_wall = build_started.elapsed().as_secs_f64();
                if rotation_enabled {
                    eprintln!(
                        "cone pass {} model built in {:.3}s: {} model columns, {} cone rows, {} sparse entries, {} bar variables, {} rotated Grams, {} signature kernel rows",
                        pass + 1,
                        build_wall,
                        repair_problem.q.len(),
                        repair_problem.a.rows,
                        repair_problem.a.entries.len(),
                        structure.psd_block_sides.len(),
                        rotated_kernels.as_ref().map_or(0, Vec::len),
                        0,
                    );
                }
                certificate.provenance.as_mut().expect("provenance exists")["cone_repair_build"] =
                    build_diagnostics.clone();
                certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                    "cone_repair_problem_built".into();
                let solve_started = std::time::Instant::now();
                let reused_solution = pass == 0 && reused_first_solution.is_some();
                if reused_solution && matches!(plan, ConePassPlan::Direct(_)) {
                    bail!(
                        "a correction-model checkpoint cannot be reused by direct native-bar repair"
                    )
                }
                let mut solved = if let Some(solved) = reused_first_solution.take() {
                    if solved.get("problem") != Some(&problem_metadata) {
                        bail!(
                            "reused cone solution metadata do not match the current repair problem"
                        )
                    }
                    solved
                } else {
                    solve_mosek_dual_sdp(
                        &repair_problem,
                        problem_metadata,
                        matches!(plan, ConePassPlan::Direct(_)),
                        None,
                        cone_solver_log,
                        false,
                        direct_interior_target.as_ref(),
                        NativeSdpMode::ConeRepair {
                            max_iterations: cone_max_iterations,
                        },
                        match &plan {
                            ConePassPlan::Correction(_) => None,
                            ConePassPlan::Direct(faces) => Some(faces),
                        },
                    )
                    .context("split cone repair failed")?
                };
                let solve_wall = solve_started.elapsed().as_secs_f64();
                let direct_dual = if matches!(plan, ConePassPlan::Direct(_)) {
                    Some(FloatingDualSolution {
                        dual_equality_multipliers: serde_json::from_value(
                            solved["dual_equality_multipliers"].take(),
                        )?,
                        dual_normalization_multiplier: Some(serde_json::from_value(
                            solved["dual_normalization_multiplier"].take(),
                        )?),
                        dual_psd_grams: serde_json::from_value(solved["dual_psd_grams"].take())?,
                    })
                } else {
                    None
                };
                let apply_started = std::time::Instant::now();
                let gram_facial_zero_threshold = cone_facial_zero_threshold;
                let (floating_corrections, corrections, rounded_margin) = match &plan {
                    ConePassPlan::Correction(plan) => {
                        let floating: Vec<f64> = serde_json::from_value(
                            solved
                                .get("primal_variables")
                                .cloned()
                                .context("cone repair returned no primal variables")?,
                        )?;
                        let corrections = floating
                            .iter()
                            .map(|&value| dyadic(value, cone_correction_bits))
                            .collect::<Result<Vec<_>>>()?;
                        let margin = apply_split_cone_repair(&mut certificate, plan, &corrections)
                            .context("could not apply the rounded split cone correction")?;
                        (floating, corrections, margin)
                    }
                    ConePassPlan::Direct(_) => {
                        replace_split_certificate_from_floating(
                            &mut certificate,
                            &structure,
                            direct_dual
                                .as_ref()
                                .expect("direct plan has a dual solution"),
                            cone_correction_bits,
                        )?;
                        project_split_grams_to_rotated_kernels(
                            &mut certificate,
                            rotated_kernels.as_deref().expect("direct plan has kernels"),
                        )
                        .context("could not project direct native-bar Grams onto exact faces")?;
                        let margin = solved
                            .pointer("/interior_margin/uniform_gram_margin")
                            .and_then(serde_json::Value::as_f64)
                            .context("direct native-bar repair returned no common face margin")?;
                        let (_, rounded_margin) = dyadic_with_value(margin, cone_correction_bits)?;
                        (Vec::new(), Vec::new(), rounded_margin)
                    }
                };
                let gram_facial_zero_row_count =
                    zero_small_split_gram_rows(&mut certificate, gram_facial_zero_threshold)
                        .context("could not apply post-cone Gram-row facial reduction")?;
                if let Some(kernels) = rotated_kernels.as_mut() {
                    augment_split_rotated_kernels_with_zero_rows(&certificate, kernels)
                        .context("could not extend rotated kernels with zero Gram rows")?;
                    certificate.provenance.as_mut().expect("provenance exists")["cone_facial_rotation"]
                        ["states"] = serde_json::to_value(kernels)?;
                }
                let reconstructed_margin =
                    minimum_reconstructed_split_gram_eigenvalue(&certificate)?;
                let near_null_after_repair = rotation_enabled
                    .then(|| split_near_null_eigen_diagnostics(&certificate, 1e-6))
                    .transpose()?;
                let apply_and_postprocess_wall = apply_started.elapsed().as_secs_f64();
                let strict_margin_goal_met =
                    rounded_margin.is_finite() && rounded_margin >= cone_margin;
                let mut cone_diagnostics = serde_json::json!({
                    "pass": pass + 1,
                    "build": build_diagnostics,
                    "solver": solved,
                    "reused_solver_checkpoint": reused_solution,
                    "reused_solver_checkpoint_path": reused_solution.then(|| cone_solution_from.expect("reused path exists")),
                    "build_wall_seconds": build_wall,
                    "solve_wall_seconds": solve_wall,
                    "solver_max_iterations": cone_max_iterations,
                    "apply_and_postprocess_wall_seconds": apply_and_postprocess_wall,
                    "stage_wall_seconds": stage_started.elapsed().as_secs_f64(),
                    "rounded_common_margin": rounded_margin,
                    "reconstructed_minimum_gram_eigenvalue": reconstructed_margin,
                    "requested_minimum_margin": cone_margin,
                    "strict_margin_goal_met": strict_margin_goal_met,
                    "gram_facial_zero_threshold": gram_facial_zero_threshold,
                    "gram_facial_zero_row_count": gram_facial_zero_row_count,
                });
                if rotation_enabled {
                    cone_diagnostics["near_null_eigenvectors_before_rotation"] =
                        serde_json::to_value(near_null_before_rotation)?;
                    cone_diagnostics["near_null_eigenvectors_after_repair"] =
                        serde_json::to_value(near_null_after_repair)?;
                    cone_diagnostics["rotated_kernel_build"] =
                        rotation_build.unwrap_or(serde_json::Value::Null);
                    cone_diagnostics["pre_rotation_gram_zero_row_count"] =
                        pre_rotation_zero_row_count.into();
                }
                cone_passes.push(cone_diagnostics.clone());
                certificate.provenance.as_mut().expect("provenance exists")["cone_repair"] =
                    cone_diagnostics;
                certificate.provenance.as_mut().expect("provenance exists")["cone_repair_passes"] =
                    serde_json::Value::Array(cone_passes.clone());
                // Native-bar tasks and the assembled conic model are each
                // several GiB at high order. Drop every pass-local owner before
                // starting the next pass, then ask glibc to return its freed
                // arenas to the OS instead of accumulating one solve's heap per
                // refinement pass. This changes resource lifetime only; the
                // checkpoint and every exact acceptance gate are unchanged.
                drop(corrections);
                drop(floating_corrections);
                drop(direct_dual);
                drop(solved);
                drop(plan);
                drop(repair_problem);
                trim_process_heap();
                // This is only an early floating screen before exact affine
                // closure. Keep enough slack for a tolerance-scale advisory MOSEK
                // iterate; certification still requires the optimizer-free exact
                // LDL audit below.
                let reconstructed_psd_gate_tolerance = 1e-8;
                if gram_facial_zero_row_count == 0 {
                    if !reconstructed_margin.is_finite()
                        || reconstructed_margin < -reconstructed_psd_gate_tolerance
                    {
                        if rotation_enabled && rotated_kernels.is_none() {
                            certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                                "axis_cone_face_stalled_pending_rotated_repair".into();
                            certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
                                "floating axis-only cone repair stalled; proves no bound; rotated candidate face remains pending".into();
                            write_checkpoint!(&certificate)?;
                            if checkpoint_after_cone_pass {
                                eprintln!(
                                    "axis-only cone pass {} stalled at reconstructed minimum {reconstructed_margin:e}; checkpointed at {} for rotated repair",
                                    pass + 1,
                                    output.display()
                                );
                                return Ok(());
                            }
                            continue;
                        }
                        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                            "failed_reconstructed_cone_margin".into();
                        certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
                            "rejected floating cone repair; proves no bound".into();
                        write_split_candidate(output, &certificate)?;
                        bail!(
                            "cone pass {} has common margin {rounded_margin:e} and global reconstructed minimum eigenvalue {reconstructed_margin:e}; requested margin {cone_margin:e}, PSD gate tolerance {reconstructed_psd_gate_tolerance:e}",
                            pass + 1
                        )
                    }
                    certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                        if strict_margin_goal_met {
                            "passed_reconstructed_cone_margin_pending_exact_closure"
                        } else {
                            "reconstructed_semidefinite_cone_face_pending_exact_closure"
                        }
                        .into();
                    write_checkpoint!(&certificate)?;
                    break;
                }
                if pass + 1 == MAX_CONE_REFINEMENT_PASSES {
                    certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                        "failed_to_stabilize_cone_face".into();
                    certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
                        "rejected floating cone repair; proves no bound".into();
                    write_split_candidate(output, &certificate)?;
                    bail!(
                        "cone face still selected {gram_facial_zero_row_count} new rows after {MAX_CONE_REFINEMENT_PASSES} PSD-constrained passes"
                    )
                }
                certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                    "cone_face_selected_pending_psd_reclosure".into();
                write_checkpoint!(&certificate)?;
                if checkpoint_after_cone_pass {
                    eprintln!(
                        "cone pass {} checkpointed at {}; rerun with --resume",
                        pass + 1,
                        output.display()
                    );
                    return Ok(());
                }
            }
        }
        if resume_after_cone {
            certificate.provenance.as_mut().expect("provenance exists")["resumed_from_post_cone_checkpoint"] =
                true.into();
        }
        if let Some(path) = export_repair_data {
            let summary = export_split_repair_system(&certificate, path)
                .context("could not export the assembled split repair system")?;
            certificate.provenance.as_mut().expect("provenance exists")["repair_system_export"] =
                serde_json::to_value(&summary)?;
            certificate.provenance.as_mut().expect("provenance exists")["repair_system_export_path"] =
                path.display().to_string().into();
            write_split_candidate(output, &certificate)?;
        }
        let repair_preference_indices = repair_preference
            .map(|path| -> Result<Vec<usize>> {
                let indices: Vec<usize> =
                    serde_json::from_slice(&fs::read(path).with_context(|| {
                        format!("could not read repair preference {}", path.display())
                    })?)
                    .with_context(|| {
                        format!(
                            "repair preference {} is not a JSON array of pool indices",
                            path.display()
                        )
                    })?;
                if indices.is_empty() {
                    bail!("repair preference {} is an empty array", path.display())
                }
                Ok(indices)
            })
            .transpose()?;
        let rotation_enabled = cone_facial_rotation_threshold > 0.0;
        let mut rotated_repair_report = None;
        if rotation_enabled {
            let kernels = rotated_kernels.as_deref().unwrap_or(&[]);
            if check_split_exact_affine_closure(&certificate).is_err()
                || check_split_exact_kernel_closure(&certificate, kernels).is_err()
            {
                project_split_grams_to_rotated_kernels(&mut certificate, kernels)
                    .context("could not restore exact rotated Gram faces before affine closure")?;
                let rotated_blocks = kernels
                    .iter()
                    .map(|state| state.block)
                    .collect::<std::collections::HashSet<_>>();
                let unselected_blocks = (0..structure.psd_block_sides.len())
                    .filter(|block| !rotated_blocks.contains(block))
                    .collect::<Vec<_>>();
                match repair_split_exact_identity_restricted(&mut certificate, &unselected_blocks) {
                    Ok(report) => rotated_repair_report = Some(report),
                    Err(error) => {
                        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                            "failed_exact_identity_repair".into();
                        certificate.provenance.as_mut().expect("provenance exists")["failure"] =
                            error.to_string().into();
                        write_split_candidate(output, &certificate)?;
                        return Err(error).context("split candidate failed exact affine repair outside the frozen rotated Grams");
                    }
                }
            }
        }
        let repair_result = if rotation_enabled
            || check_split_exact_affine_closure(&certificate).is_ok()
        {
            Ok((None, None))
        } else if let Some(preference) = repair_preference_indices.as_deref() {
            repair_split_exact_identity_ordered(&mut certificate, preference)
                .map(|(diagnostics, support)| (Some(diagnostics), Some(support)))
        } else if unrestricted_repair && cone_margin == 0.0 {
            repair_split_exact_identity_with_support(&mut certificate)
                .map(|support| (None, Some(support)))
        } else if cone_margin == 0.0 {
            match seed_active_gram_blocks.as_deref() {
                Some(blocks) => repair_split_exact_identity_restricted(&mut certificate, blocks)
                    .map(|diagnostics| (Some(diagnostics), None)),
                None => repair_split_exact_identity_componentwise_with_support(&mut certificate)
                    .map(|(diagnostics, support)| (Some(diagnostics), Some(support))),
            }
        } else {
            repair_split_exact_identity_componentwise_with_support(&mut certificate)
                .map(|(diagnostics, support)| (Some(diagnostics), Some(support)))
        };
        let (repair_diagnostics, repair_support) = match repair_result {
            Ok(result) => result,
            Err(error) => {
                certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
                    "failed_exact_identity_repair".into();
                certificate.provenance.as_mut().expect("provenance exists")["failure"] =
                    error.to_string().into();
                write_split_candidate(output, &certificate)?;
                return Err(error).context("split candidate failed exact coefficient repair");
            }
        };
        if let Some(kernels) = rotated_kernels.as_deref() {
            check_split_exact_affine_closure(&certificate)
                .context("rotated-kernel candidate did not close the exact affine identity")?;
            check_split_exact_kernel_closure(&certificate, kernels)
                .context("rotated-kernel candidate did not close G*N=0 exactly")?;
        }
        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
            "exact_identity_repaired_pending_audit".into();
        certificate.provenance.as_mut().expect("provenance exists")["exact_identity_repaired"] =
            true.into();
        if let Some(report) = rotated_repair_report.as_ref() {
            certificate.provenance.as_mut().expect("provenance exists")["exact_repair"] =
                serde_json::to_value(report)?;
        } else if !rotation_enabled {
            certificate.provenance.as_mut().expect("provenance exists")["exact_repair"] =
                serde_json::to_value(&repair_diagnostics)?;
        }
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_wall_seconds"] =
            exact_repair_started.elapsed().as_secs_f64().into();
        if let Some(preference) = repair_preference_indices.as_deref() {
            certificate.provenance.as_mut().expect("provenance exists")["exact_repair_preference"] = serde_json::json!({
                "path": repair_preference.expect("preference path exists").display().to_string(),
                "preferred_variable_count": preference.len(),
                "basis_selection": "advisory modular scan in preference order",
            });
        }
        certificate.provenance.as_mut().expect("provenance exists")["nonzero_exact_residual_count"] =
            0.into();
        let restricted_scope = (cone_margin == 0.0 && !unrestricted_repair)
            .then_some(seed_active_gram_blocks)
            .flatten();
        certificate.provenance.as_mut().expect("provenance exists")["exact_repair_gram_scope"] =
            if rotation_enabled {
                serde_json::json!({
                    "mode": "direct_native_bar_faces_then_unselected_gram_exact_closure",
                    "kernel_rows_in_correction_signatures": 0,
                    "frozen_after_first_pass": !cone_facial_rotation_recompute_each_pass,
                })
            } else {
                match (restricted_scope, repair_support) {
                    (_, Some(blocks)) => serde_json::json!({
                        "mode": "all_nonzero_gram_blocks",
                        "selected_support_block_count": blocks.len(),
                        "selected_support_blocks": blocks,
                    }),
                    (Some(blocks), None) => serde_json::json!({
                        "mode": "interior_active_gram_blocks",
                        "block_count": blocks.len(),
                        "blocks": blocks,
                    }),
                    (None, None) => serde_json::json!({"mode": "all_nonzero_gram_blocks"}),
                }
            };
    }
    // Exact-repair parsing and sparse reconstruction own another high-order
    // copy of the Gram data. Return those freed arenas before the independent
    // audit so its exact residual/LDL workspace does not stack on top of them.
    trim_process_heap();
    let reconstructed_eigenvalue_started = std::time::Instant::now();
    let reconstructed_minimum = minimum_reconstructed_split_gram_eigenvalue(&certificate)?;
    let reconstructed_psd_gate_tolerance = 1e-9;
    certificate.provenance.as_mut().expect("provenance exists")["reconstructed_eigenvalue_wall_seconds"] =
        reconstructed_eigenvalue_started
            .elapsed()
            .as_secs_f64()
            .into();
    certificate.provenance.as_mut().expect("provenance exists")["minimum_reconstructed_gram_eigenvalue_after_exact_repair"] =
        reconstructed_minimum.into();
    certificate.provenance.as_mut().expect("provenance exists")["reconstructed_grams_numerically_psd_after_exact_repair"] =
        (reconstructed_minimum >= 0.0).into();
    certificate.provenance.as_mut().expect("provenance exists")["checkpoint_serialization_wall_seconds_before_final_exact_candidate"] =
        checkpoint_serialization_wall_seconds.into();
    certificate.provenance.as_mut().expect("provenance exists")["checkpoint_write_count_before_final_exact_candidate"] =
        checkpoint_write_count.into();
    write_checkpoint!(&certificate)?;
    if !reconstructed_minimum.is_finite()
        || reconstructed_minimum < -reconstructed_psd_gate_tolerance
    {
        let reconstructed_psd_gate = -reconstructed_psd_gate_tolerance;
        certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
            "failed_reconstructed_psd_gate".into();
        certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
            "rejected exact candidate before LDL audit; proves no bound".into();
        write_split_candidate(output, &certificate)?;
        write_adjacent_split_shifted_outcome(output, &certificate).with_context(|| {
            "retained the reconstructed-PSD-gate failure, but could not write its adjacent shifted-salvage outcome"
        })?;
        bail!(
            "exactly closed split candidate reconstructs with minimum Gram eigenvalue {reconstructed_minimum:e}, below advisory gate {reconstructed_psd_gate:e}"
        )
    }
    if checkpoint_before_native_audit {
        eprintln!(
            "exact closure checkpointed at {}; rerun with --resume-exact-closure to run the native audit",
            output.display()
        );
        return Ok(());
    }
    trim_process_heap();
    let audit_started = std::time::Instant::now();
    let report = audit_split_candidate_with_retention(output, &mut certificate)?;
    certificate.provenance.as_mut().expect("provenance exists")["exactification_status"] =
        "passed_native_exact_audit".into();
    certificate.provenance.as_mut().expect("provenance exists")["rigor"] =
        "optimizer-independent exact certificate".into();
    certificate.provenance.as_mut().expect("provenance exists")["native_exact_audit_wall_seconds"] =
        audit_started.elapsed().as_secs_f64().into();
    certificate.provenance.as_mut().expect("provenance exists")["pipeline_wall_seconds"] =
        pipeline_started.elapsed().as_secs_f64().into();
    certificate.provenance.as_mut().expect("provenance exists")["checkpoint_serialization_wall_seconds_before_final_output"] =
        checkpoint_serialization_wall_seconds.into();
    certificate.provenance.as_mut().expect("provenance exists")["checkpoint_write_count_before_final_output"] =
        checkpoint_write_count.into();
    write_split_candidate(output, &certificate)?;
    print!("{}", json(&report)?);
    Ok(())
}

fn audit_split_candidate_with_retention(
    output: &std::path::Path,
    certificate: &mut SplitExactDualCertificate,
) -> Result<ExactAuditReport> {
    match audit_split_exact_certificate(certificate) {
        Ok(report) => Ok(report),
        Err(error) => {
            let failure = error.to_string();
            let provenance = certificate
                .provenance
                .get_or_insert_with(|| serde_json::json!({}));
            provenance["exactification_status"] = "failed_native_exact_audit".into();
            provenance["failure"] = failure.clone().into();
            provenance["exact_audit_failure"] = failure.into();
            provenance["rigor"] = "rejected exact candidate; proves no bound".into();
            write_split_candidate(output, certificate)
                .context("could not retain the split candidate and exact audit failure")?;
            write_adjacent_split_shifted_outcome(output, certificate).with_context(|| {
                format!(
                    "retained the failed split v1 candidate, but could not write its adjacent shifted-salvage outcome; original audit failure: {error}"
                )
            })?;
            Err(error).context("split candidate failed native exact audit")
        }
    }
}

fn adjacent_split_shifted_path(output: &std::path::Path) -> Result<PathBuf> {
    let mut file_name = output
        .file_name()
        .context("split candidate output has no file name")?
        .to_os_string();
    file_name.push(".shifted.json");
    Ok(output.with_file_name(file_name))
}

#[derive(serde::Serialize)]
struct SplitShiftedSalvageErrorRecord {
    schema: &'static str,
    status: &'static str,
    failure_stage: &'static str,
    original_identity_exact: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    original_identity_check_failure: Option<String>,
    source_candidate: String,
    failure: String,
}

fn split_shifted_salvage_error_record(
    output: &std::path::Path,
    certificate: &SplitExactDualCertificate,
    failure: String,
) -> SplitShiftedSalvageErrorRecord {
    let (failure_stage, original_identity_exact, original_identity_check_failure) =
        match split_shifted_original_identity_is_exact(certificate) {
            Ok(true) => ("post_identity_split_shifted_salvage", Some(true), None),
            Ok(false) => ("raw_identity_validation", Some(false), None),
            Err(error) => ("raw_identity_check_error", None, Some(error.to_string())),
        };
    SplitShiftedSalvageErrorRecord {
        schema: SPLIT_SHIFTED_SALVAGE_ERROR_SCHEMA_V1,
        status: "salvage_error",
        failure_stage,
        original_identity_exact,
        original_identity_check_failure,
        source_candidate: output.display().to_string(),
        failure,
    }
}

fn write_adjacent_split_shifted_outcome(
    output: &std::path::Path,
    certificate: &SplitExactDualCertificate,
) -> Result<PathBuf> {
    let shifted_path = adjacent_split_shifted_path(output)?;
    let payload = match salvage_split_shifted_exact_certificate(certificate.clone()) {
        Ok(SplitShiftedSalvageOutcome::Certified { certificate }) => json(&certificate)?,
        Ok(SplitShiftedSalvageOutcome::Unsalvageable { failure }) => json(&failure)?,
        Err(error) => json(&split_shifted_salvage_error_record(
            output,
            certificate,
            error.to_string(),
        ))?,
    };
    fs::write(&shifted_path, payload)?;
    Ok(shifted_path)
}

fn write_split_candidate(
    output: &std::path::Path,
    certificate: &SplitExactDualCertificate,
) -> Result<()> {
    use std::io::Write;

    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut temporary = output.as_os_str().to_owned();
    temporary.push(".tmp");
    let temporary = PathBuf::from(temporary);
    let file = fs::File::create(&temporary)?;
    let mut writer = std::io::BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, certificate)?;
    writer.write_all(b"\n")?;
    writer.flush()?;
    drop(writer);
    fs::rename(temporary, output)?;
    Ok(())
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn trim_process_heap() {
    unsafe extern "C" {
        fn malloc_trim(pad: usize) -> i32;
    }

    // SAFETY: malloc_trim(0) has no pointer arguments and is safe to call
    // between pass-local deallocations on glibc. Its return value is advisory.
    let _ = unsafe { malloc_trim(0) };
}

#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
fn trim_process_heap() {}

fn source_reproduction(metadata: &serde_json::Value, objective: f64) -> Option<serde_json::Value> {
    let archived = metadata.get("archived_mosek_result")?;
    let expected = archived.get("objective")?.as_f64()?;
    let tolerance = archived.get("reproduction_tolerance")?.as_f64()?;
    let absolute_difference = (objective - expected).abs();
    Some(serde_json::json!({
        "expected_objective": expected,
        "absolute_difference": absolute_difference,
        "tolerance": tolerance,
        "matches": absolute_difference <= tolerance,
        "source_path": archived.get("source_path")?,
    }))
}

fn upper_svec_to_lower_entry(index: usize, side: usize, value: f64) -> Result<(usize, usize, f64)> {
    let mut column = ((8.0 * index as f64 + 1.0).sqrt() as usize - 1) / 2;
    while (column + 1) * (column + 2) / 2 <= index {
        column += 1;
    }
    while column * (column + 1) / 2 > index {
        column -= 1;
    }
    let row = index - column * (column + 1) / 2;
    if column >= side {
        bail!("svec index {index} is outside a triangle of side {side}")
    }
    let value = if row == column {
        value
    } else {
        value / std::f64::consts::SQRT_2
    };
    Ok((column, row, value))
}

fn shifted_bar_entry(
    value: f64,
    row: usize,
    column: usize,
    margin: f64,
    projector: Option<&[Vec<f64>]>,
) -> f64 {
    value
        + projector.map_or_else(
            || {
                if row == column { 1.0 } else { 0.0 }
            },
            |projector| projector[row][column],
        ) * margin
}

fn solve_mosek_affine_conic(
    problem: &ConicProblem,
    metadata: serde_json::Value,
    solver_log: bool,
    dump_primal: bool,
    strict: bool,
) -> Result<serde_json::Value> {
    use mosek::{
        Boundkey, Dinfitem, Dparam, Iinfitem, Objsense, Solsta, Soltype, Streamtype, Task,
    };
    problem.validate().map_err(anyhow::Error::msg)?;
    let variables = i32::try_from(problem.q.len()).context("too many MOSEK variables")?;
    let rows = i64::try_from(problem.a.rows).context("too many MOSEK AFE rows")?;
    let mut task = Task::new().context("create native MOSEK task")?;
    if strict {
        for parameter in [
            Dparam::INTPNT_CO_TOL_PFEAS,
            Dparam::INTPNT_CO_TOL_DFEAS,
            Dparam::INTPNT_CO_TOL_REL_GAP,
        ] {
            task.put_dou_param(parameter, 1e-10).native()?;
        }
    }
    task.append_vars(variables).native()?;
    task.put_var_bound_slice_const(0, variables, Boundkey::FR, 0.0, 0.0)
        .native()?;
    task.put_c_slice(0, variables, &problem.q).native()?;
    task.put_obj_sense(Objsense::MINIMIZE).native()?;

    task.append_afes(rows).native()?;
    let afe_rows = problem
        .a
        .entries
        .iter()
        .map(|&(row, _, _)| i64::try_from(row))
        .collect::<Result<Vec<_>, _>>()?;
    let columns = problem
        .a
        .entries
        .iter()
        .map(|&(_, column, _)| i32::try_from(column))
        .collect::<Result<Vec<_>, _>>()?;
    let values = problem
        .a
        .entries
        .iter()
        .map(|&(_, _, value)| -value)
        .collect::<Vec<_>>();
    task.put_afe_f_entry_list(&afe_rows, &columns, &values)
        .native()?;
    task.put_afe_g_slice(0, rows, &problem.b).native()?;

    let mut offset = 0_i64;
    for cone in &problem.cones {
        let (domain, afe_indices) = match *cone {
            Cone::Zero(dimension) => (
                task.append_rzero_domain(dimension as i64).native()?,
                Vec::new(),
            ),
            Cone::Nonnegative(dimension) => (
                task.append_rplus_domain(dimension as i64).native()?,
                Vec::new(),
            ),
            Cone::SecondOrder(dimension) => (
                task.append_quadratic_cone_domain(dimension as i64)
                    .native()?,
                Vec::new(),
            ),
            Cone::PsdTriangle(side) => {
                let domain = task
                    .append_svec_psd_cone_domain(cone.dimension() as i64)
                    .native()?;
                // Shared/Clarabel rows are upper-triangular column-major.
                // MOSEK's svec domain expects lower-triangular column-major.
                let indices = mosek_psd_permutation(side, offset)?;
                (domain, indices)
            }
        };
        let afe_indices = match cone {
            Cone::PsdTriangle(_) => afe_indices,
            _ => (0..i64::try_from(cone.dimension())?)
                .map(|index| offset + index)
                .collect(),
        };
        task.append_acc(domain, &afe_indices, &vec![0.0; cone.dimension()])
            .native()?;
        offset += i64::try_from(cone.dimension())?;
    }

    let termination = if solver_log {
        task.with_stream_callback(Streamtype::LOG, &|message| eprint!("{message}"), |task| {
            task.optimize()
        })
        .native()?
    } else {
        task.optimize().native()?
    };
    let status = task.get_sol_sta(Soltype::ITR).native()?;
    if status != Solsta::OPTIMAL {
        bail!("MOSEK returned solution status {status} (termination {termination})");
    }
    let objective = task.get_primal_obj(Soltype::ITR).native()?;
    let iterations = task.get_int_inf(Iinfitem::INTPNT_ITER).native()?;
    let solve_time = task.get_dou_inf(Dinfitem::INTPNT_TIME).native()?;
    let primal_residual = task.get_dou_inf(Dinfitem::INTPNT_PRIMAL_FEAS).native()?;
    let dual_residual = task.get_dou_inf(Dinfitem::INTPNT_DUAL_FEAS).native()?;
    let mut result = serde_json::json!({
        "schema": "minexposure/discovery-v1", "backend": "mosek-rust", "backend_version": "11.2.3",
        "problem": metadata, "status": "Optimal", "termination": termination,
        "objective": objective, "iterations": iterations, "solve_time_seconds": solve_time,
        "primal_residual": primal_residual, "dual_residual": dual_residual,
        "solver_settings": if strict {
            serde_json::json!({
                "strict": true,
                "MSK_DPAR_INTPNT_CO_TOL_PFEAS": 1e-10,
                "MSK_DPAR_INTPNT_CO_TOL_DFEAS": 1e-10,
                "MSK_DPAR_INTPNT_CO_TOL_REL_GAP": 1e-10,
            })
        } else {
            serde_json::json!({"strict": false, "parameters": "MOSEK defaults"})
        },
        "rigor": "exploratory",
        "warning": "floating discovery solve; exact certification is separate"
    });
    if dump_primal {
        let mut primal = vec![0.0; problem.q.len()];
        task.get_xx(Soltype::ITR, &mut primal).native()?;
        result["primal_variables"] = serde_json::to_value(primal)?;
    }
    Ok(result)
}

fn mosek_psd_permutation(side: usize, offset: i64) -> Result<Vec<i64>> {
    let mut indices = Vec::with_capacity(side * (side + 1) / 2);
    for column in 0..side {
        for row in column..side {
            let upper_index = row * (row + 1) / 2 + column;
            indices.push(offset + i64::try_from(upper_index)?);
        }
    }
    Ok(indices)
}

trait MosekResultExt<T> {
    fn native(self) -> Result<T>;
}

impl<T> MosekResultExt<T> for std::result::Result<T, String> {
    fn native(self) -> Result<T> {
        self.map_err(anyhow::Error::msg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use minexposure_core::stationary_hausdorff_split::BlockFamily;

    fn zero_matrix(side: usize) -> Vec<Vec<String>> {
        vec![vec!["0".into(); side]; side]
    }

    #[test]
    fn labels_and_rescales_active_time_capped_solver_outputs() {
        let metadata = serde_json::json!({
            "active_time_cap": "10000000",
            "bound_scope": "active-time-capped, NOT all-duration",
            "occupation_variable_scale": "10000",
            "cell_count": 2,
            "occupation_moment_count_per_cell": 2,
        });
        let mut result = serde_json::json!({"problem": metadata.clone()});
        label_active_time_capped_result(&mut result);
        assert_eq!(result["active_time_cap"], "10000000");
        assert_eq!(
            result["bound_scope"],
            "active-time-capped, NOT all-duration"
        );
        assert_eq!(
            physical_active_time_cap_multiplier(&metadata, 20_000_000.0).unwrap(),
            2.0
        );

        let mut primal = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        rescale_active_time_capped_primal_variables(&metadata, &mut primal).unwrap();
        assert_eq!(primal, vec![10_000.0, 20_000.0, 30_000.0, 40_000.0, 5.0]);
    }

    fn split_candidate_with_negative_gram() -> SplitExactDualCertificate {
        let order = 2;
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let structure = stationary_hausdorff_split::structure(order, &grid).unwrap();
        let mut sides = structure.psd_block_sides.iter().copied();
        let occupation_grams_by_cell = (0..structure.cell_count)
            .map(|_| {
                (0..structure.occupation_moment_block_count_per_cell
                    + structure.occupation_interval_block_count_per_cell
                    + structure.occupation_interval_diagonal_count_per_cell)
                    .map(|_| zero_matrix(sides.next().unwrap()))
                    .collect()
            })
            .collect();
        let interface_grams_by_knot = (0..structure.cell_count.saturating_sub(1))
            .map(|_| {
                (0..structure.interface_moment_block_count_per_interface)
                    .map(|_| zero_matrix(sides.next().unwrap()))
                    .collect()
            })
            .collect();
        let terminal_grams_by_cell = (0..structure.cell_count)
            .map(|_| (0..2).map(|_| zero_matrix(sides.next().unwrap())).collect())
            .collect();
        assert!(sides.next().is_none());
        assert!(matches!(
            structure.psd_block_families.first(),
            Some(BlockFamily::Occupation)
        ));
        let mut certificate = SplitExactDualCertificate {
            schema: SPLIT_EXACT_SCHEMA_V1.into(),
            order,
            knots: structure.knots,
            split_grid_hash: structure.split_grid_hash,
            formulation_hash: structure.formulation_hash,
            exposure_upper: structure.exposure_upper.to_string(),
            bound_target: "-1".into(),
            equality_order: "cell_major_liouville_v1".into(),
            liouville_multipliers_by_cell: vec![
                vec![
                    "0".into();
                    structure.liouville_equality_count_per_cell
                ];
                structure.cell_count
            ],
            normalization: "0".into(),
            gram_order: "occupation_by_cell_then_interface_by_knot_then_terminal_pair_by_cell_v1"
                .into(),
            occupation_grams_by_cell,
            interface_grams_by_knot,
            terminal_grams_by_cell,
            provenance: Some(serde_json::json!({"retention_test_marker": 37})),
        };
        certificate.occupation_grams_by_cell[0][0][0][0] = "-1".into();
        certificate
    }

    #[test]
    fn parses_shifted_salvage_and_audit_commands() {
        assert!(
            Cli::try_parse_from([
                "minexposure",
                "salvage-exact-shifted",
                "failed-v1.json",
                "--output",
                "shifted.json",
                "--audit-jobs",
                "2",
            ])
            .is_ok()
        );
        assert!(
            Cli::try_parse_from([
                "minexposure",
                "audit-exact-shifted",
                "shifted.json",
                "--audit-jobs",
                "2",
            ])
            .is_ok()
        );
        assert!(
            Cli::try_parse_from([
                "minexposure",
                "salvage-exact-split-shifted",
                "failed-split-v1.json",
                "--output",
                "split-shifted.json",
                "--audit-jobs",
                "2",
            ])
            .is_ok()
        );
        assert!(
            Cli::try_parse_from([
                "minexposure",
                "audit-exact-split-shifted",
                "split-shifted.json",
                "--audit-jobs",
                "2",
            ])
            .is_ok()
        );
    }

    #[test]
    fn parses_split_cone_pass_checkpoint_mode() {
        let cli = Cli::try_parse_from([
            "minexposure",
            "exactify-hausdorff-split",
            "--input",
            "seed.json",
            "--order",
            "7",
            "--knots",
            "0,1/32,31/32,1",
            "--target",
            "117/40",
            "--cone-margin",
            "5e-6",
            "--checkpoint-after-cone-pass",
            "--checkpoint-before-native-audit",
            "--output",
            "certificate.json",
        ])
        .unwrap();
        let Command::ExactifyHausdorffSplit {
            checkpoint_after_cone_pass,
            checkpoint_before_native_audit,
            cone_facial_rotation_threshold,
            cone_facial_rotation_bits,
            cone_facial_rotation_recompute_each_pass,
            ..
        } = cli.command
        else {
            panic!("parsed the wrong command")
        };
        assert!(checkpoint_after_cone_pass);
        assert!(checkpoint_before_native_audit);
        assert_eq!(cone_facial_rotation_threshold, 0.0);
        assert_eq!(cone_facial_rotation_bits, 30);
        assert!(!cone_facial_rotation_recompute_each_pass);
        assert!(
            Cli::try_parse_from([
                "minexposure",
                "exactify-hausdorff-split",
                "--input",
                "seed.json",
                "--order",
                "8",
                "--knots",
                "0,1/32,31/32,1",
                "--target",
                "733/250",
                "--cone-margin",
                "5e-6",
                "--checkpoint-before-cone",
                "--output",
                "certificate.json",
            ])
            .is_ok()
        );
        assert!(
            Cli::try_parse_from([
                "minexposure",
                "exactify-hausdorff-split",
                "--input",
                "seed.json",
                "--order",
                "7",
                "--knots",
                "0,1/26,1/3,2/3,25/26,1",
                "--target",
                "2931/1000",
                "--cone-margin",
                "5e-6",
                "--cone-facial-rotation-threshold",
                "1e-6",
                "--cone-facial-rotation-bits",
                "30",
                "--cone-facial-rotation-recompute-each-pass",
                "--output",
                "certificate.json",
            ])
            .is_ok()
        );
    }

    #[test]
    fn validates_interior_margin_configuration() {
        let common = parse_interior_margin_target(
            Some(ModelId::StationaryTorusHausdorffSplit),
            true,
            "289/100",
            1e-8,
            Some(1e-6),
            false,
            None,
        )
        .unwrap();
        assert_eq!(common.exact, "289/100");
        assert_eq!(common.value, 2.89);
        assert!(!common.per_block_margins);

        assert!(
            parse_interior_margin_target(
                Some(ModelId::StationaryTorusHausdorffSplit),
                true,
                "289/100",
                0.0,
                None,
                true,
                None,
            )
            .is_err()
        );
        assert!(
            parse_interior_margin_target(
                Some(ModelId::StationaryTorusHausdorffLift),
                true,
                "289/100",
                0.0,
                None,
                false,
                None,
            )
            .is_err()
        );
    }

    #[test]
    fn converts_upper_svec_to_mosek_bar_entries() {
        let converted = (0..6)
            .map(|index| upper_svec_to_lower_entry(index, 3, std::f64::consts::SQRT_2).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            converted,
            vec![
                (0, 0, std::f64::consts::SQRT_2),
                (1, 0, 1.0),
                (1, 1, std::f64::consts::SQRT_2),
                (2, 0, 1.0),
                (2, 1, 1.0),
                (2, 2, std::f64::consts::SQRT_2),
            ]
        );
    }

    #[test]
    fn native_bar_projector_shift_has_the_correct_sign_and_svec_scaling() {
        let problem = ConicProblem {
            q: vec![0.0],
            a: minexposure_core::conic::SparseMatrix {
                rows: 3,
                cols: 1,
                entries: vec![
                    (0, 0, 2.0),
                    (1, 0, 3.0 * std::f64::consts::SQRT_2),
                    (2, 0, 5.0),
                ],
            },
            b: vec![0.0; 3],
            cones: vec![Cone::PsdTriangle(2)],
        };
        let projector = vec![vec![0.5, 0.5], vec![0.5, 0.5]];
        let projectors: Vec<Option<&[Vec<f64>]>> = vec![Some(&projector)];
        let coefficients =
            gram_margin_coefficients_by_block(&problem, &[None; 3], &[(0, 3, 2)], &projectors)
                .unwrap();
        assert_eq!(coefficients, vec![vec![(0, 6.5)]]);

        let x = [[1.0, 0.0], [0.0, 0.0]];
        let margin = 2.0;
        let g = [
            [
                shifted_bar_entry(x[0][0], 0, 0, margin, Some(&projector)),
                shifted_bar_entry(x[0][1], 0, 1, margin, Some(&projector)),
            ],
            [
                shifted_bar_entry(x[1][0], 1, 0, margin, Some(&projector)),
                shifted_bar_entry(x[1][1], 1, 1, margin, Some(&projector)),
            ],
        ];
        let trace_a_x = 2.0 * x[0][0] + 6.0 * x[0][1] + 5.0 * x[1][1];
        let trace_a_g = 2.0 * g[0][0] + 6.0 * g[0][1] + 5.0 * g[1][1];
        assert_eq!(trace_a_x + margin * coefficients[0][0].1, trace_a_g);
        assert_eq!(trace_a_g, 15.0);
    }

    #[test]
    fn native_bar_faces_do_not_enter_correction_column_signatures() {
        let mut certificate = split_candidate_with_negative_gram();
        let (block, matrix) = certificate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(certificate.interface_grams_by_knot.iter_mut().flatten())
            .chain(certificate.terminal_grams_by_cell.iter_mut().flatten())
            .enumerate()
            .find(|(_, matrix)| matrix.len() == 2)
            .expect("test certificate has a two-dimensional Gram");
        *matrix = vec![vec!["2".into(), "0".into()], vec!["0".into(), "3".into()]];
        let kernels = vec![SplitRotatedKernelState {
            block,
            kernel: vec![vec!["1".into()], vec!["1".into()]],
        }];
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let assembled = stationary_hausdorff_split::assemble(2, &grid).unwrap();
        let baseline = (
            assembled.conic.q.len(),
            assembled.conic.a.rows,
            assembled.conic.a.entries.len(),
        );
        let faces = build_split_native_bar_face_plan(&certificate, &kernels).unwrap();
        assert_eq!(
            (
                assembled.conic.q.len(),
                assembled.conic.a.rows,
                assembled.conic.a.entries.len(),
            ),
            baseline
        );
        assert_eq!(faces.blocks.iter().filter(|face| face.rotated).count(), 1);
        assert_eq!(
            faces.blocks[faces
                .blocks
                .iter()
                .position(|face| face.block == block)
                .unwrap()]
            .kernel_rank,
            1
        );
    }

    #[test]
    #[ignore = "requires a working MOSEK runtime"]
    fn native_bar_face_constraint_round_trips_through_mosek() {
        let problem = ConicProblem {
            q: vec![1.0],
            a: minexposure_core::conic::SparseMatrix {
                rows: 3,
                cols: 1,
                entries: vec![(0, 0, -1.0), (2, 0, -1.0)],
            },
            b: vec![0.0; 3],
            cones: vec![Cone::PsdTriangle(2)],
        };
        let plan = SplitNativeBarFacePlan {
            gram_count: 1,
            blocks: vec![
                minexposure_core::stationary_certificate::SplitNativeBarFaceBlock {
                    block: 0,
                    range_projector: vec![vec![0.5, -0.5], vec![-0.5, 0.5]],
                    rotated: true,
                    kernel_rank: 1,
                },
            ],
        };
        let result = solve_mosek_dual_sdp(
            &problem,
            serde_json::json!({}),
            true,
            None,
            false,
            true,
            None,
            NativeSdpMode::Standard,
            Some(&plan),
        )
        .unwrap();
        let grams: FloatingPsdGrams =
            serde_json::from_value(result["dual_psd_grams"].clone()).unwrap();
        let values = &grams.blocks[0].upper_triangle;
        assert!((values[0] - 0.5).abs() < 1e-8);
        assert!((values[1] + 0.5).abs() < 1e-8);
        assert!((values[2] - 0.5).abs() < 1e-8);
        assert!((values[0] + values[1]).abs() < 1e-8);
        assert!((values[1] + values[2]).abs() < 1e-8);

        let shifted_problem = ConicProblem {
            q: vec![0.0],
            a: minexposure_core::conic::SparseMatrix {
                rows: 4,
                cols: 1,
                entries: vec![(0, 0, 1.0), (1, 0, -1.0), (3, 0, -1.0)],
            },
            b: vec![-1.0, 0.0, 0.0, 0.0],
            cones: vec![Cone::Zero(1), Cone::PsdTriangle(2)],
        };
        let target = InteriorMarginTarget {
            exact: "1".into(),
            value: 1.0,
            active_grams: Some(vec![true]),
            zero_gram_threshold: 0.0,
            reference: None,
            reference_eigenvalue_threshold: None,
            per_block_margins: false,
            margin_cap: None,
        };
        let shifted = solve_mosek_dual_sdp(
            &shifted_problem,
            serde_json::json!({}),
            true,
            None,
            false,
            true,
            Some(&target),
            NativeSdpMode::ConeRepair { max_iterations: 30 },
            Some(&plan),
        )
        .unwrap();
        let margin = shifted["interior_margin"]["uniform_gram_margin"]
            .as_f64()
            .unwrap();
        assert!((margin - 1.0).abs() < 1e-8);
        let shifted_grams: FloatingPsdGrams =
            serde_json::from_value(shifted["dual_psd_grams"].clone()).unwrap();
        for (actual, expected) in shifted_grams.blocks[0]
            .upper_triangle
            .iter()
            .zip([0.5, -0.5, 0.5])
        {
            assert!((actual - expected).abs() < 1e-8);
        }
    }

    #[test]
    fn only_cone_repair_may_use_an_unknown_mosek_iterate() {
        assert!(mosek_solution_is_usable(
            mosek::Solsta::OPTIMAL,
            NativeSdpMode::Standard
        ));
        assert!(!mosek_solution_is_usable(
            mosek::Solsta::UNKNOWN,
            NativeSdpMode::Standard
        ));
        assert!(mosek_solution_is_usable(
            mosek::Solsta::UNKNOWN,
            NativeSdpMode::ConeRepair { max_iterations: 30 }
        ));
        assert!(!mosek_solution_is_usable(
            mosek::Solsta::PRIM_INFEAS_CER,
            NativeSdpMode::ConeRepair { max_iterations: 30 }
        ));
    }

    #[test]
    fn reports_source_reproduction_within_tolerance() {
        let metadata = serde_json::json!({
            "archived_mosek_result": {
                "objective": 2.9,
                "reproduction_tolerance": 1e-4,
                "source_path": "source.json"
            }
        });
        let report = source_reproduction(&metadata, 2.900_001).unwrap();
        assert_eq!(report["matches"], true);
        assert!((report["absolute_difference"].as_f64().unwrap() - 1e-6).abs() < 1e-12);
    }

    #[test]
    fn separates_lifted_normalization_from_liouville_multipliers() {
        let metadata = serde_json::json!({
            "liouville_equality_count": 2,
            "terminal_moment_count": 5,
        });
        assert_eq!(
            positional_dual_scalars(&[1.0, 2.0, 3.0], &metadata).unwrap(),
            (vec![1.0, 2.0], Some(3.0))
        );
        assert!(positional_dual_scalars(&[1.0, 2.0], &metadata).is_err());
    }

    #[test]
    fn preserves_direct_realified_liouville_order() {
        let metadata = serde_json::json!({"liouville_equality_count": 2});
        assert_eq!(
            positional_dual_scalars(&[1.0, 9.0, 2.0, 8.0], &metadata).unwrap(),
            (vec![1.0, 2.0], None)
        );
    }

    #[test]
    fn two_cell_order_three_clarabel_is_not_weaker_than_monolithic() {
        let grid = "0,1/2,1".parse::<SplitGrid>().unwrap();
        let split = stationary_hausdorff_split::assemble(3, &grid).unwrap();
        let monolithic = stationary_hausdorff::assemble(3).unwrap();
        let split_result = solve_clarabel(
            &split.conic,
            serde_json::to_value(split.structure).unwrap(),
            false,
        )
        .unwrap();
        let monolithic_result = solve_clarabel(
            &monolithic.conic,
            serde_json::to_value(monolithic.structure).unwrap(),
            false,
        )
        .unwrap();
        let diagnostic = stationary_hausdorff_split::split_monotonicity_diagnostic(
            split_result["objective"].as_f64().unwrap(),
            monolithic_result["objective"].as_f64().unwrap(),
            1e-6,
        )
        .unwrap();
        assert!(diagnostic.valid, "{diagnostic:?}");
    }

    #[test]
    fn permutes_clarabel_upper_svec_to_mosek_lower_svec() {
        assert_eq!(
            mosek_psd_permutation(3, 10).unwrap(),
            vec![10, 11, 13, 12, 14, 15]
        );
    }

    #[test]
    fn exact_psd_failure_retains_complete_split_candidate_and_reason() {
        let mut candidate = split_candidate_with_negative_gram();
        let original_multipliers = candidate.liouville_multipliers_by_cell.clone();
        let original_occupation_grams = candidate.occupation_grams_by_cell.clone();
        let original_interface_grams = candidate.interface_grams_by_knot.clone();
        let original_terminal_grams = candidate.terminal_grams_by_cell.clone();
        let directory = std::env::temp_dir().join(format!(
            "minexposure-split-retention-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let output = directory.join("candidate.json");

        let error = audit_split_candidate_with_retention(&output, &mut candidate).unwrap_err();
        assert!(error.to_string().contains("failed native exact audit"));
        let retained: SplitExactDualCertificate =
            serde_json::from_slice(&fs::read(&output).unwrap()).unwrap();
        assert_eq!(retained.schema, SPLIT_EXACT_SCHEMA_V1);
        assert_eq!(retained.liouville_multipliers_by_cell, original_multipliers);
        assert_eq!(retained.occupation_grams_by_cell, original_occupation_grams);
        assert_eq!(retained.interface_grams_by_knot, original_interface_grams);
        assert_eq!(retained.terminal_grams_by_cell, original_terminal_grams);
        assert_eq!(retained.normalization, "0");
        assert_eq!(
            retained.provenance.as_ref().unwrap()["retention_test_marker"],
            37
        );
        let reason = retained.provenance.as_ref().unwrap()["exact_audit_failure"]
            .as_str()
            .unwrap();
        assert!(reason.contains("Gram block 0 LDL pivot 0"), "{reason}");
        assert!(reason.contains("-1"), "{reason}");
        assert_eq!(
            retained.provenance.as_ref().unwrap()["failure"],
            retained.provenance.as_ref().unwrap()["exact_audit_failure"]
        );
        assert_eq!(
            retained.provenance.as_ref().unwrap()["exactification_status"],
            "failed_native_exact_audit"
        );
        let shifted_path = adjacent_split_shifted_path(&output).unwrap();
        let shifted: serde_json::Value =
            serde_json::from_slice(&fs::read(&shifted_path).unwrap()).unwrap();
        assert_eq!(shifted["schema"], SPLIT_SHIFTED_SALVAGE_ERROR_SCHEMA_V1);
        assert_eq!(shifted["status"], "salvage_error");
        assert_eq!(shifted["failure_stage"], "raw_identity_validation");
        assert_eq!(shifted["original_identity_exact"], false);
        assert!(
            shifted["failure"]
                .as_str()
                .unwrap()
                .contains("raw split exact identity")
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn post_identity_salvage_error_reports_exact_identity_stage() {
        let mut candidate = split_candidate_with_negative_gram();
        for matrix in candidate
            .occupation_grams_by_cell
            .iter_mut()
            .flatten()
            .chain(candidate.interface_grams_by_knot.iter_mut().flatten())
            .chain(candidate.terminal_grams_by_cell.iter_mut().flatten())
        {
            for (index, row) in matrix.iter_mut().enumerate() {
                row[index] = "1".into();
            }
        }
        minexposure_core::stationary_certificate::repair_split_exact_identity(&mut candidate)
            .unwrap();
        assert!(split_shifted_original_identity_is_exact(&candidate).unwrap());
        let record = split_shifted_salvage_error_record(
            std::path::Path::new("identity-closed-candidate.json"),
            &candidate,
            "injected post-identity shift-search failure".into(),
        );
        let payload = serde_json::to_value(record).unwrap();
        assert_eq!(payload["schema"], SPLIT_SHIFTED_SALVAGE_ERROR_SCHEMA_V1);
        assert_eq!(payload["status"], "salvage_error");
        assert_eq!(
            payload["failure_stage"],
            "post_identity_split_shifted_salvage"
        );
        assert_eq!(payload["original_identity_exact"], true);
        assert!(payload.get("original_identity_check_failure").is_none());
    }
}
