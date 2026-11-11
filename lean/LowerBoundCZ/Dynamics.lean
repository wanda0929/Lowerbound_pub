/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Active-time and laboratory CZ trajectories

Formal counterparts of Eqs. (schrod_lab)–(objective) in `main.tex`.
A trajectory is a pair of normalized spinors driven by a common control,
not an existence theorem for the ODE.
-/

noncomputable section

namespace LowerBoundCZ

open Complex InnerProductSpace intervalIntegral

/-- A finite-duration, maximum-amplitude, globally driven two-sector path. -/
structure ActiveTrajectory where
  /-- Active duration `S`. -/
  S : ℝ
  hS : 0 < S
  g1 : ℝ → ℂ
  r1 : ℝ → ℂ
  g2 : ℝ → ℂ
  r2 : ℝ → ℂ
  u : ℝ → ℂ
  /-- `|u| = 1` on the gate interval. -/
  hu : ∀ s ∈ Set.Icc 0 S, normSq (u s) = 1
  /-- Sector-1 Schrödinger equation. -/
  hg1 : ∀ s ∈ Set.Icc 0 S, HasDerivAt g1 (groundVel 1 (u s) (r1 s)) s
  hr1 : ∀ s ∈ Set.Icc 0 S, HasDerivAt r1 (rydbergVel 1 (u s) (g1 s)) s
  /-- Sector-2 Schrödinger equation. -/
  hg2 : ∀ s ∈ Set.Icc 0 S, HasDerivAt g2 (groundVel 2 (u s) (r2 s)) s
  hr2 : ∀ s ∈ Set.Icc 0 S, HasDerivAt r2 (rydbergVel 2 (u s) (g2 s)) s
  /-- Sphere constraints. -/
  n1 : ∀ s ∈ Set.Icc 0 S, normSq (g1 s) + normSq (r1 s) = 1
  n2 : ∀ s ∈ Set.Icc 0 S, normSq (g2 s) + normSq (r2 s) = 1
  /-- Computational ground initial data. -/
  g1_init : g1 0 = 1
  r1_init : r1 0 = 0
  g2_init : g2 0 = 1
  r2_init : r2 0 = 0

/-- Exact CZ terminal conditions, Eq. (CZ_cond). -/
def ActiveTrajectory.IsCZ (tr : ActiveTrajectory) : Prop :=
  tr.r1 tr.S = 0 ∧ tr.r2 tr.S = 0 ∧ tr.g2 tr.S = - (tr.g1 tr.S) ^ 2

/-- Active-time exposure `C[u] = ∫ c(x(s)) ds`, Eq. (objective). -/
def ActiveTrajectory.exposure (tr : ActiveTrajectory) : ℝ :=
  ∫ s in (0 : ℝ)..tr.S, pointCost (tr.r1 s) (tr.r2 s)

/-- Laboratory-time path with amplitude envelope `0 ≤ ρ ≤ 1`. -/
structure LabTrajectory where
  τf : ℝ
  hτ : 0 < τf
  ρ : ℝ → ℝ
  ω : ℝ → ℂ
  g1 : ℝ → ℂ
  r1 : ℝ → ℂ
  g2 : ℝ → ℂ
  r2 : ℝ → ℂ
  hρ : ∀ τ ∈ Set.Icc 0 τf, 0 ≤ ρ τ ∧ ρ τ ≤ 1
  hω : ∀ τ ∈ Set.Icc 0 τf, normSq (ω τ) = 1
  hg1 : ∀ τ ∈ Set.Icc 0 τf,
    HasDerivAt g1 (ρ τ * groundVel 1 (ω τ) (r1 τ)) τ
  hr1 : ∀ τ ∈ Set.Icc 0 τf,
    HasDerivAt r1 (ρ τ * rydbergVel 1 (ω τ) (g1 τ)) τ
  hg2 : ∀ τ ∈ Set.Icc 0 τf,
    HasDerivAt g2 (ρ τ * groundVel 2 (ω τ) (r2 τ)) τ
  hr2 : ∀ τ ∈ Set.Icc 0 τf,
    HasDerivAt r2 (ρ τ * rydbergVel 2 (ω τ) (g2 τ)) τ
  n1 : ∀ τ ∈ Set.Icc 0 τf, normSq (g1 τ) + normSq (r1 τ) = 1
  n2 : ∀ τ ∈ Set.Icc 0 τf, normSq (g2 τ) + normSq (r2 τ) = 1
  g1_init : g1 0 = 1
  r1_init : r1 0 = 0
  g2_init : g2 0 = 1
  r2_init : r2 0 = 0

def LabTrajectory.IsCZ (tr : LabTrajectory) : Prop :=
  tr.r1 tr.τf = 0 ∧ tr.r2 tr.τf = 0 ∧ tr.g2 tr.τf = - (tr.g1 tr.τf) ^ 2

def LabTrajectory.exposure (tr : LabTrajectory) : ℝ :=
  ∫ τ in (0 : ℝ)..tr.τf, pointCost (tr.r1 τ) (tr.r2 τ)

/-- Compressed (active-time) cost of a laboratory waveform. -/
def LabTrajectory.bangCost (tr : LabTrajectory) : ℝ :=
  ∫ τ in (0 : ℝ)..tr.τf, pointCost (tr.r1 τ) (tr.r2 τ) * tr.ρ τ

/-- Two-sector path with independent bounded drives (lock-free relaxation). -/
structure IndependentTrajectory where
  S : ℝ
  hS : 0 < S
  g1 : ℝ → ℂ
  r1 : ℝ → ℂ
  g2 : ℝ → ℂ
  r2 : ℝ → ℂ
  u1 : ℝ → ℂ
  u2 : ℝ → ℂ
  /-- Independent bounded drives, `|v_k| ≤ 1` (Theorem relax). -/
  hu1 : ∀ s ∈ Set.Icc 0 S, normSq (u1 s) ≤ 1
  hu2 : ∀ s ∈ Set.Icc 0 S, normSq (u2 s) ≤ 1
  hg1 : ∀ s ∈ Set.Icc 0 S, HasDerivAt g1 (groundVel 1 (u1 s) (r1 s)) s
  hr1 : ∀ s ∈ Set.Icc 0 S, HasDerivAt r1 (rydbergVel 1 (u1 s) (g1 s)) s
  hg2 : ∀ s ∈ Set.Icc 0 S, HasDerivAt g2 (groundVel 2 (u2 s) (r2 s)) s
  hr2 : ∀ s ∈ Set.Icc 0 S, HasDerivAt r2 (rydbergVel 2 (u2 s) (g2 s)) s
  n1 : ∀ s ∈ Set.Icc 0 S, normSq (g1 s) + normSq (r1 s) = 1
  n2 : ∀ s ∈ Set.Icc 0 S, normSq (g2 s) + normSq (r2 s) = 1
  g1_init : g1 0 = 1
  r1_init : r1 0 = 0
  g2_init : g2 0 = 1
  r2_init : r2 0 = 0

def IndependentTrajectory.IsCZ (tr : IndependentTrajectory) : Prop :=
  tr.r1 tr.S = 0 ∧ tr.r2 tr.S = 0 ∧ tr.g2 tr.S = - (tr.g1 tr.S) ^ 2

def IndependentTrajectory.exposure (tr : IndependentTrajectory) : ℝ :=
  ∫ s in (0 : ℝ)..tr.S, pointCost (tr.r1 s) (tr.r2 s)

/-- A single-sector closed loop used by the free-phase construction. -/
structure ClosedLoop (k : ℕ) where
  S : ℝ
  hS : 0 < S
  g : ℝ → ℂ
  r : ℝ → ℂ
  u : ℝ → ℂ
  /-- Bounded drive (`|u| ≤ 1`); the chirp family uses `|u| = 1`. -/
  hu : ∀ s ∈ Set.Icc 0 S, normSq (u s) ≤ 1
  hg : ∀ s ∈ Set.Icc 0 S, HasDerivAt g (groundVel k (u s) (r s)) s
  hr : ∀ s ∈ Set.Icc 0 S, HasDerivAt r (rydbergVel k (u s) (g s)) s
  nrm : ∀ s ∈ Set.Icc 0 S, normSq (g s) + normSq (r s) = 1
  g_init : g 0 = 1
  r_init : r 0 = 0
  r_final : r S = 0

def ClosedLoop.phase (L : ClosedLoop k) : ℝ := Complex.arg (L.g L.S)

def ClosedLoop.exposure (L : ClosedLoop k) : ℝ :=
  ∫ s in (0 : ℝ)..L.S, normSq (L.r s)

/-- Admissible globally driven CZ exposures. -/
def AdmissibleExposures : Set ℝ :=
  { C | ∃ tr : ActiveTrajectory, tr.IsCZ ∧ tr.exposure = C }

/-- Physical exposure infimum `C_*`. -/
def Cstar : ℝ := sInf AdmissibleExposures

lemma pointCost_mul_rho_le (r1 r2 : ℂ) {ρ : ℝ} (_hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    pointCost r1 r2 * ρ ≤ pointCost r1 r2 := by
  have hc : 0 ≤ pointCost r1 r2 := pointCost_nonneg _ _
  nlinarith [_hρ0, hρ1, hc]

/-- Order-theoretic content of Lemma bang: compression cannot raise the infimum,
and restricting to a subset cannot lower it. -/
lemma sInf_eq_of_compression {A B : Set ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hBd : BddBelow B) (hAd : BddBelow A)
    (hsubset : B ⊆ A)
    (hcompress : ∀ a ∈ A, ∃ b ∈ B, b ≤ a) :
    sInf A = sInf B := by
  apply le_antisymm
  · apply le_csInf hB
    intro b hb
    exact csInf_le hAd (hsubset hb)
  · apply le_csInf hA
    intro a ha
    obtain ⟨b, hb, hba⟩ := hcompress a ha
    exact (csInf_le hBd hb).trans hba

end LowerBoundCZ
