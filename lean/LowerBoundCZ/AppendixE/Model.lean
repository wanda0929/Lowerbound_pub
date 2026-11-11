/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Dynamics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Appendix E — physical model with measurable disk controls

Formal counterpart of the "Mathematical formulation" subsection of Appendix E
(`app:sos-convergence`) in `main.tex`.

Unlike `Dynamics.ActiveTrajectory`, which assumes an everywhere-differentiable
trajectory class (`HasDerivAt` at every point) and unimodular controls, the
trajectories here are given by an *integral equation*, so measurable disk
controls `|u| ≤ 1` and piecewise-smooth pulses are admitted. This
integral-equation class is intended to model the measurable-control
trajectories used in Appendix E; equivalence with the a.e. ODE formulation is
not proved here.

Everything below is PARTIAL and CONDITIONAL by design: the disk-compression
(`lem:disk_equivalence`), the occupation-measure zero-gap step, and the pulse
patching construction appear only as explicit hypotheses of the theorems, never
as proved facts. The new `physicalInfimum` is deliberately distinct from the
old `Dynamics.Cstar` (a different, everywhere-differentiable trajectory class).
-/

noncomputable section

namespace LowerBoundCZ.AppendixE

open MeasureTheory

/-- State vector `(g₁, r₁, g₂, r₂) ∈ ℂ⁴`, coordinate order as in the paper. -/
abbrev State := Fin 4 → ℂ

/-- Initial state `x₀ = (1, 0, 1, 0)`. -/
def initialState : State := ![1, 0, 1, 0]

/-- Schrödinger vector field `f_u(x)` of Eq. (app_fu):
`(-iκ₁ u r₁, -iκ₁ ū g₁, -iκ₂ u r₂, -iκ₂ ū g₂)`. -/
def velocity (u : ℂ) (x : State) : State :=
  ![groundVel 1 u (x 1), rydbergVel 1 u (x 0),
    groundVel 2 u (x 3), rydbergVel 2 u (x 2)]

/-- Sector-wise normalization `|g₁|² + |r₁|² = |g₂|² + |r₂|² = 1`. -/
def Normalized (x : State) : Prop :=
  Complex.normSq (x 0) + Complex.normSq (x 1) = 1 ∧
  Complex.normSq (x 2) + Complex.normSq (x 3) = 1

/-- A finite-duration trajectory driven by a measurable disk control,
formulated through the integral equation `x(t) = x₀ + ∫₀ᵗ f_u(x) ds`. -/
structure DiskTrajectory where
  /-- Active duration `S`. -/
  S : ℝ
  duration_pos : 0 < S
  x : ℝ → State
  u : ℝ → ℂ
  state_continuous : ContinuousOn x (Set.Icc 0 S)
  control_measurable : Measurable u
  /-- Disk control bound `|u(s)| ≤ 1` a.e. on `[0, S]`. -/
  control_bound : ∀ᵐ s ∂volume.restrict (Set.Icc 0 S), Complex.normSq (u s) ≤ 1
  /-- The trajectory stays on the product sphere `S³ × S³`. -/
  normalized : ∀ s ∈ Set.Icc 0 S, Normalized (x s)
  velocity_integrable :
    IntervalIntegrable (fun s => velocity (u s) (x s)) volume 0 S
  /-- Integral form of the Schrödinger equation. -/
  evolves : ∀ t ∈ Set.Icc 0 S,
    x t = initialState + ∫ s in (0 : ℝ)..t, velocity (u s) (x s)

/-- Unimodular (physical) drive: `|u(s)| = 1` a.e. on `[0, S]`. -/
def DiskTrajectory.IsPhase (tr : DiskTrajectory) : Prop :=
  ∀ᵐ s ∂volume.restrict (Set.Icc 0 tr.S), Complex.normSq (tr.u s) = 1

/-- Exact CZ terminal conditions on the ground manifold. -/
def DiskTrajectory.IsCZ (tr : DiskTrajectory) : Prop :=
  tr.x tr.S 1 = 0 ∧ tr.x tr.S 3 = 0 ∧ tr.x tr.S 2 = -(tr.x tr.S 0) ^ 2

/-- Cumulative exposure `C[u] = ∫₀ˢ c(x(s)) ds`. -/
def DiskTrajectory.exposure (tr : DiskTrajectory) : ℝ :=
  ∫ s in (0 : ℝ)..tr.S, pointCost (tr.x s 1) (tr.x s 3)

/-- Exposures realized by exact-CZ trajectories with unimodular drive. -/
def physicalCosts : Set ℝ :=
  {C | ∃ tr : DiskTrajectory, tr.IsPhase ∧ tr.IsCZ ∧ tr.exposure = C}

/-- Exposures realized by exact-CZ trajectories with disk controls. -/
def relaxedCosts : Set ℝ :=
  {C | ∃ tr : DiskTrajectory, tr.IsCZ ∧ tr.exposure = C}

/-- The physical exposure infimum of Appendix E: the infimum over exact-CZ
trajectories with unimodular drive in the integral-equation model. Distinct
from `Dynamics.Cstar`, which quantifies over the everywhere-differentiable
`ActiveTrajectory` class; no equality between them is claimed here. -/
def physicalInfimum : ℝ := sInf physicalCosts

theorem DiskTrajectory.exposure_nonneg (tr : DiskTrajectory) :
    0 ≤ tr.exposure :=
  intervalIntegral.integral_nonneg tr.duration_pos.le
    fun _s _hs => pointCost_nonneg _ _

theorem physicalCosts_subset_relaxedCosts : physicalCosts ⊆ relaxedCosts := by
  rintro C ⟨tr, _hphase, hcz, hC⟩
  exact ⟨tr, hcz, hC⟩

theorem physicalCosts_bddBelow : BddBelow physicalCosts := by
  refine ⟨0, fun C hC => ?_⟩
  obtain ⟨tr, _, _, rfl⟩ := hC
  exact tr.exposure_nonneg

theorem relaxedCosts_bddBelow : BddBelow relaxedCosts := by
  refine ⟨0, fun C hC => ?_⟩
  obtain ⟨tr, _, rfl⟩ := hC
  exact tr.exposure_nonneg

/-- CONDITIONAL form of `lem:disk_equivalence`: *if* every disk-control CZ
exposure can be compressed to a unimodular CZ exposure of no greater value
(the time-reparametrization claim of the paper, assumed here), and *if* a
physical CZ trajectory exists at all, then the relaxed and physical infima
coincide. The compression itself is not proved here. -/
theorem disk_infimum_eq_of_compression
    (hne : physicalCosts.Nonempty)
    (hcompress : ∀ a ∈ relaxedCosts, ∃ b ∈ physicalCosts, b ≤ a) :
    sInf relaxedCosts = physicalInfimum :=
  sInf_eq_of_compression (hne.mono physicalCosts_subset_relaxedCosts) hne
    physicalCosts_bddBelow relaxedCosts_bddBelow
    physicalCosts_subset_relaxedCosts hcompress

/-- If arbitrarily good physical CZ exposures exist below `T + ε` for every
`ε > 0` (the conclusion of the paper's patching argument, assumed here), then
the physical infimum is at most `T`. -/
theorem physicalInfimum_le_of_patching (_hne : physicalCosts.Nonempty)
    {T : ℝ} (hpatch : ∀ ε : ℝ, 0 < ε → ∃ C ∈ physicalCosts, C ≤ T + ε) :
    physicalInfimum ≤ T := by
  apply le_of_forall_sub_le
  intro ε hε
  obtain ⟨C, hC, hCT⟩ := hpatch ε hε
  have hle : physicalInfimum ≤ T + ε :=
    (csInf_le physicalCosts_bddBelow hC).trans hCT
  linarith

/-- Order-theoretic zero-gap statement: if a larger cost set (e.g. values of an
occupation-measure linear program) contains the physical costs and every
element `m` of it admits physical costs at most `m + ε` for all `ε > 0`, then
its infimum equals the physical infimum. No occupation measures or current
decompositions are constructed; they enter only through `hpatch`. -/
theorem zero_gap_of_patching (hne : physicalCosts.Nonempty)
    (measureCosts : Set ℝ) (hembed : physicalCosts ⊆ measureCosts)
    (hpatch : ∀ m ∈ measureCosts, ∀ ε : ℝ, 0 < ε →
      ∃ C ∈ physicalCosts, C ≤ m + ε) :
    sInf measureCosts = physicalInfimum := by
  have hPhys_le : ∀ m ∈ measureCosts, physicalInfimum ≤ m := by
    intro m hm
    apply le_of_forall_sub_le
    intro ε hε
    obtain ⟨C, hC, hCm⟩ := hpatch m hm ε hε
    have hle : physicalInfimum ≤ m + ε :=
      (csInf_le physicalCosts_bddBelow hC).trans hCm
    linarith
  have hMeasBdd : BddBelow measureCosts := ⟨physicalInfimum, hPhys_le⟩
  apply le_antisymm
  · exact le_csInf hne fun C hC => csInf_le hMeasBdd (hembed hC)
  · exact le_csInf (hne.mono hembed) hPhys_le

end LowerBoundCZ.AppendixE
