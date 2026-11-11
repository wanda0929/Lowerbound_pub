# Appendix E — partial Lean formalization

The `AppendixE` modules formalize selected parts of Appendix E of `main.tex`
(`app:sos-convergence`, "Asymptotic completeness of the real-coefficient SOS
hierarchy", lines 1796–2301), whose stated conclusion is
`0 ≤ L_d ≤ L_{d+1} ≤ C_*` and `L_d → C_*` for the stationary and fixed finite
split SOS hierarchies.

**STATUS: explicitly PARTIAL and CONDITIONAL.** No unconditional statement of
physical completeness is claimed. Every analytic or SOS input appears as a
named hypothesis of a theorem or is listed as an obligation below. A compiled
conditional theorem is not a verification of Appendix E.

Build: `lake build LowerBoundCZ.AppendixE`
Kernel audit: `lake env lean AppendixEAudit.lean` (expected: only
`propext`, `Classical.choice`, `Quot.sound`).

## What is proved (paper → theorem map)

| Paper statement | Lean | Caveat |
|---|---|---|
| Model: measurable disk controls, `x(t) = x₀ + ∫ f_u`, exposure `∫ c(x) ds` | `DiskTrajectory`, `physicalCosts`, `relaxedCosts`, `physicalInfimum` in `Model.lean` | Integral-equation model; admits measurable `u`, piecewise-smooth pulses |
| `c(x) ≥ 0` ⇒ `C ≥ 0` | `DiskTrajectory.exposure_nonneg`, `physicalCosts_bddBelow`, `relaxedCosts_bddBelow` | — |
| `lem:disk_equivalence` (disk ↔ unimodular infima equal) | `disk_infimum_eq_of_compression` | CONDITIONAL: assumes nonemptiness and the compression step; time reparametrization not proved |
| Patching ⇒ `C_* ≤ T` (end of `lem:patching` argument) | `physicalInfimum_le_of_patching`, `physicalInfimum_le_of_threshold_family` | CONDITIONAL: assumes existence of the patched pulse family |
| Occupation-measure zero gap | `zero_gap_of_patching` | CONDITIONAL: assumes physical ⊆ measure costs and `ε`-approximation; no measures constructed |
| `0 ≤ L_d ≤ L_{d+1} ≤ C_*`, `L_d → C_*` | `ValueHierarchy.value_nonneg/_mono/_le`, `tendsto_of_finite_certificates`, `stationary_and_split_complete_of_common_certificates`, `physicalInfimum_stationary_and_split_complete_of_common_certificates` | `ValueHierarchy` is an abstract value-set structure; feasibility of the actual cones is hypothesis, not theorem |
| `b^(−3/2) (b⁵)^(3/8) = b^(3/8)`; error `→ 0`; `b⁵ < b/2` eventually | `coupled_threshold_power`, `patching_error_tendsto_zero`, `threshold_eventually_valid` in `Patching.lean` | Exact `Real.rpow` arithmetic only |
| Augmentation `‖r‖²I − rrᵀ`, kills `r`, PSD, invariance `rᵀ(A + Λ·aug)r = rᵀAr` | `augmentation_mulVec`, `augmentation_mulVec_self`, `quadratic_augmentation`, `quadratic_augmentation_nonneg`, `quadratic_add_smul_augmentation` | No compactness/norm-spectrum claims |
| Scalar Schur step `ax² + 2bxy + (d+t)y² > 0` | `schur_quadratic_pos` (completion of square) | Not the full uniform matrix positivity lemma |
| Gram contraction `∑ᵢⱼ (r-coordᵢ)(HᵀH)ᵢⱼ(r-coordⱼ) = ∑ₖ (rowfactorₖ)²`, vanishes on `F`, evaluated ≥ 0 | `gram_contraction`, `gram_contraction_poly`, `gram_contraction_eval_nonneg`, `rowFactor_eval_zero_on_face`, `gram_contraction_eval_zero_on_face` | Existence of `H` (matrix Putinar) not asserted |
| Stationary→split gluing, constant cells give zero interface | `stationary_interface_zero`, `stationary_interface_zero_cells` | Pure algebra; not cone feasibility |

## Outstanding obligations (NOT formalized)

1. A.e. ODE/integral-equation equivalence and the disk compression step of
   `lem:disk_equivalence` (time reparametrization to `|u| = 1`).
2. Lie-bracket growth bound and the ball-box local controllability estimate.
3. Properties of the compactification map `J` and the exposure-velocity field
   `B`, and the phase-preserving patch construction (the audit's phase-error
   and concatenation facts are recorded under Mathematical review notes).
4. Current decomposition, weighted-time reparametrization, disintegration,
   and the actual zero-duality-gap construction for occupation measures.
5. Closedness of the cone and the separation argument.
6. `C¹` polynomial approximation of the separating smooth function `φ` on a
   compact box, its pullback through `J`, and cubic ideal factorization.
7. Global matrix positivity (compactness + norm bounds), the face-restricted
   matrix Putinar Positivstellensatz providing the factor `H` used in
   `gram_contraction_poly`, and quotient/SOS degree bookkeeping.
8. Haar averaging and feasibility embedding for the actual stationary/split
   cones, plus weak duality. Note: the paper's `W` is constructed so that `J`
   is constant on the initial `G`-orbit, which is why averaging preserves the
   objective value; this is not true for arbitrary `W`.

## Mathematical review notes

- The manuscript's stated Schur threshold is supported by an informal
  spectral argument: if `‖A₀‖ ≤ M` and `a = eᵀA₀e ≥ m > 0`, each
  two-dimensional orthonormal compression has determinant at least `−M²`.
  Hence its Schur complement is bounded below by `−M²/m`, and `Λδ² > M²/m`
  suffices. The Lean scalar Schur lemma does not yet formalize this norm
  estimate or the uniform compactness argument.
- The unresolved items above are formalization obligations; they are not
  presented as counterexamples to the manuscript.
- For the phase/gluing review facts — the projection `P` with
  `z(P) = z/|z|` giving zero endpoint phase error (audit lines 506–579), and
  independent sector rotations permitting cost-preserving concatenation
  (audit lines 581–721) — see the supporting audit
  [`sos-convergence-theory-audit-2026-09-16-expanded.md`](../proof/sos-convergence/sos-convergence-theory-audit-2026-09-16-expanded.md).

## Scope notes

- `physicalInfimum` (Model.lean) ranges over exact-CZ trajectories with
  *unimodular* drive (`IsPhase`) in the integral-equation model;
  `relaxedCosts` is the corresponding disk-control version. Both are
  deliberately distinct from `Dynamics.Cstar`, the infimum over the
  everywhere-differentiable `ActiveTrajectory` class — continuous
  differentiability is not required there — and it is not the measurable
  class of Appendix E; no equality between them is claimed.
- `ValueHierarchy.feasible` sets are abstract sets of reals; nothing here
  manufactures feasible sets and calls them polynomial programs.
- No file in `AppendixE/` imports the certificate-axiom modules
  (`Upper`, `Results`, `Reductions`).
