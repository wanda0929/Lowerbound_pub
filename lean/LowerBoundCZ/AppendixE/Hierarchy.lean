/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.AppendixE.Model
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Appendix E — order-theoretic completeness of the dual hierarchies

The final step of Appendix E is order-theoretic: if a nested sequence of
feasible value sets is sound (`v ≤ C`) and admits certificates arbitrarily
close to `C`, then `sSup` of the level-`d` values converges up to `C` from
below.

`ValueHierarchy` abstracts both the stationary and the fixed finite split
hierarchies. The feasible sets here are *abstract value sets*: the module
does not construct the actual polynomial/SOS programs, and soundness,
nesting, and near-optimality are explicit hypotheses. In particular this
file does not prove that the real hierarchies of the paper satisfy them —
that requires the Haar-averaging and feasibility-embedding arguments that
remain open (see `AppendixE.md`).

Each level value is the real supremum `sSup`; nonemptiness and an upper bound
are proved before using its order properties. Natural-number indices may be
reindexed from the first valid SOS order; no polynomial degree-zero
feasibility is claimed. `C` is instantiated to `physicalInfimum` only in the
explicit corollary at the end — independent of the old `Dynamics.Cstar`.
-/

noncomputable section

namespace LowerBoundCZ.AppendixE

open Filter

/-- A nested, `0`-containing, `C`-sound sequence of abstract feasible value
sets. This models the value side `L_d` of either SOS hierarchy; it is not
itself a polynomial program. -/
structure ValueHierarchy (C : ℝ) where
  feasible : ℕ → Set ℝ
  /-- `0` is always feasible (the zero subsolution). -/
  zero_mem : ∀ d, 0 ∈ feasible d
  /-- The hierarchy is nested. -/
  nested : ∀ {d e}, d ≤ e → feasible d ⊆ feasible e
  /-- Soundness: every feasible value is at most `C`. -/
  sound : ∀ d v, v ∈ feasible d → v ≤ C

namespace ValueHierarchy

/-- Level-`d` value `L_d = sSup (feasible d)`. -/
noncomputable def value {C : ℝ} (H : ValueHierarchy C) (d : ℕ) : ℝ :=
  sSup (H.feasible d)

theorem nonempty {C : ℝ} (H : ValueHierarchy C) (d : ℕ) : (H.feasible d).Nonempty :=
  ⟨0, H.zero_mem d⟩

theorem bddAbove {C : ℝ} (H : ValueHierarchy C) (d : ℕ) : BddAbove (H.feasible d) :=
  ⟨C, fun _v hv => H.sound d _ hv⟩

theorem value_nonneg {C : ℝ} (H : ValueHierarchy C) (d : ℕ) : 0 ≤ H.value d :=
  le_csSup (H.bddAbove d) (H.zero_mem d)

theorem value_le {C : ℝ} (H : ValueHierarchy C) (d : ℕ) : H.value d ≤ C :=
  csSup_le (H.nonempty d) fun _v hv => H.sound d _ hv

theorem value_mono {C : ℝ} (H : ValueHierarchy C) {d e : ℕ} (hde : d ≤ e) :
    H.value d ≤ H.value e :=
  csSup_le_csSup (H.bddAbove e) (H.nonempty d) (H.nested hde)

/-- If near-optimal feasible values exist at every scale `ε`, the value
sequence converges to `C`. Combined with `value_nonneg`, `value_mono`, and
`value_le` this is exactly `0 ≤ L_d ≤ L_{d+1} ≤ C`, `L_d → C`. -/
theorem tendsto_of_finite_certificates {C : ℝ} (H : ValueHierarchy C)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ d v, v ∈ H.feasible d ∧ C - ε < v) :
    Tendsto H.value atTop (nhds C) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d₀, v, hv, hCv⟩ := happrox ε hε
  refine ⟨d₀, fun d hd => ?_⟩
  have hle : H.value d ≤ C := H.value_le d
  have hlt : C - ε < H.value d :=
    hCv.trans_le (le_csSup (H.bddAbove d) (H.nested hd hv))
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end ValueHierarchy

/-- The complete order-theoretic final step for both hierarchies at once:
from a common certificate family whose objective values embed into both
level-`degree w` feasible sets and approach `C`, conclude monotonicity,
soundness, and convergence `L_d ↑ C` for each hierarchy. All analytic input
(certificates exist) sits in `near_optimal`; all algebraic input (they are
feasible) sits in `in_stationary`/`in_split`. -/
theorem stationary_and_split_complete_of_common_certificates
    {C : ℝ} (stationary split : ValueHierarchy C)
    {Certificate : Type*} (degree : Certificate → ℕ) (objective : Certificate → ℝ)
    (in_stationary : ∀ w, objective w ∈ stationary.feasible (degree w))
    (in_split : ∀ w, objective w ∈ split.feasible (degree w))
    (near_optimal : ∀ ε : ℝ, 0 < ε → ∃ w, C - ε < objective w) :
    (∀ d, 0 ≤ stationary.value d ∧ stationary.value d ≤ stationary.value (d + 1) ∧
        stationary.value (d + 1) ≤ C) ∧
    (∀ d, 0 ≤ split.value d ∧ split.value d ≤ split.value (d + 1) ∧
        split.value (d + 1) ≤ C) ∧
    Tendsto stationary.value atTop (nhds C) ∧
    Tendsto split.value atTop (nhds C) := by
  have happrox (H : ValueHierarchy C)
      (hin : ∀ w, objective w ∈ H.feasible (degree w)) :
      ∀ ε : ℝ, 0 < ε → ∃ d v, v ∈ H.feasible d ∧ C - ε < v := by
    intro ε hε
    obtain ⟨w, hw⟩ := near_optimal ε hε
    exact ⟨degree w, objective w, hin w, hw⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    exact ⟨stationary.value_nonneg d,
      stationary.value_mono (Nat.le_succ d), stationary.value_le (d + 1)⟩
  · intro d
    exact ⟨split.value_nonneg d,
      split.value_mono (Nat.le_succ d), split.value_le (d + 1)⟩
  · exact stationary.tendsto_of_finite_certificates (happrox stationary in_stationary)
  · exact split.tendsto_of_finite_certificates (happrox split in_split)

/-- The same statement instantiated at the new `physicalInfimum` of
Appendix E (`Model.lean`). The hypotheses are unchanged: the actual
stationary and split cone hierarchies still have to be shown to form
`ValueHierarchy physicalInfimum` structures with a common near-optimal
certificate family — that is the SOS-side content of the appendix and is
not formalized here. -/
theorem physicalInfimum_stationary_and_split_complete_of_common_certificates
    (stationary split : ValueHierarchy physicalInfimum)
    {Certificate : Type*} (degree : Certificate → ℕ) (objective : Certificate → ℝ)
    (in_stationary : ∀ w, objective w ∈ stationary.feasible (degree w))
    (in_split : ∀ w, objective w ∈ split.feasible (degree w))
    (near_optimal : ∀ ε : ℝ, 0 < ε → ∃ w, physicalInfimum - ε < objective w) :
    (∀ d, 0 ≤ stationary.value d ∧ stationary.value d ≤ stationary.value (d + 1) ∧
        stationary.value (d + 1) ≤ physicalInfimum) ∧
    (∀ d, 0 ≤ split.value d ∧ split.value d ≤ split.value (d + 1) ∧
        split.value (d + 1) ≤ physicalInfimum) ∧
    Tendsto stationary.value atTop (nhds physicalInfimum) ∧
    Tendsto split.value atTop (nhds physicalInfimum) :=
  stationary_and_split_complete_of_common_certificates stationary split
    degree objective in_stationary in_split near_optimal

/-- Algebra of the stationary-to-split gluing: a cell-independent weight `W`
contributes zero interface difference. Pure algebra — it says nothing about
feasibility of the constant extension in the actual cones. -/
theorem stationary_interface_zero {X : Type*} (W : X → ℝ) (x : X) :
    W x - W x = 0 := sub_self _

/-- The same zero interface for constant cell copies over any finite index
set: `(fun _ => W) j x − (fun _ => W) j' x = 0`, independent of the number
of cells. Again algebra only, not cone feasibility. -/
theorem stationary_interface_zero_cells {X : Type*} {n : ℕ}
    (W : X → ℝ) (j j' : Fin n) (x : X) :
    (fun _ : Fin n => W) j x - (fun _ : Fin n => W) j' x = 0 := sub_self _

end LowerBoundCZ.AppendixE
