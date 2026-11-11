/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Dynamics
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Interval / Krawczyk upper certificate
-/

noncomputable section

namespace LowerBoundCZ

open Function

/-- Newton/Krawczyk map `g(x) = x - R(F x)`. A fixed point is a root of `F`
whenever `R` kills only zero. -/
lemma newton_fixed_is_root {E : Type*} [AddCommGroup E]
    (F : E → E) (R : E → E)
    (hR0 : ∀ y, R y = 0 → y = 0) (hRzero : R 0 = 0) (x : E) :
    x - R (F x) = x ↔ F x = 0 := by
  constructor
  · intro h
    exact hR0 (F x) (sub_eq_self.mp h)
  · intro h
    simp [h, hRzero]

/-- Banach uniqueness for a global contraction: the Newton map has a unique
fixed point, hence `F` has a unique root. -/
lemma unique_root_of_contraction
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [Nonempty E]
    (F : E → E) (R : E → E)
    (hR0 : ∀ y, R y = 0 → y = 0) (hRzero : R 0 = 0)
    {K : NNReal} (hf : ContractingWith K fun x => x - R (F x)) :
    ∃! x, F x = 0 := by
  set g : E → E := fun x => x - R (F x)
  refine ⟨hf.fixedPoint, ?_, ?_⟩
  · have hx : IsFixedPt g (hf.fixedPoint) := hf.fixedPoint_isFixedPt
    exact (newton_fixed_is_root F R hR0 hRzero _).mp hx
  · intro y hy
    have hy' : IsFixedPt g y := (newton_fixed_is_root F R hR0 hRzero y).mpr hy
    exact (hf.fixedPoint_unique' hf.fixedPoint_isFixedPt hy').symm

/-- Computer-checked Krawczyk contraction for the 12,672-segment witness.

Verified by `certificates/cz-upper-bound-2.935875225844105-v1/verify.sh`
in 500-bit Arb arithmetic. -/
axiom intervalKrawczykCertificate :
  ∃ tr : ActiveTrajectory, tr.IsCZ ∧ tr.exposure < upperEndpoint

lemma AdmissibleExposures_nonempty : AdmissibleExposures.Nonempty := by
  obtain ⟨tr, hCZ, _⟩ := intervalKrawczykCertificate
  exact ⟨tr.exposure, tr, hCZ, rfl⟩

lemma AdmissibleExposures_bddBelow : BddBelow AdmissibleExposures :=
  ⟨0, fun C hC => by
    obtain ⟨t, _, rfl⟩ := hC
    exact intervalIntegral.integral_nonneg t.hS.le fun _ _ => pointCost_nonneg _ _⟩

theorem Cstar_lt_upperEndpoint : Cstar < upperEndpoint := by
  obtain ⟨tr, hCZ, hup⟩ := intervalKrawczykCertificate
  have hmem : tr.exposure ∈ AdmissibleExposures := ⟨tr, hCZ, rfl⟩
  have hle : Cstar ≤ tr.exposure := csInf_le AdmissibleExposures_bddBelow hmem
  linarith

end LowerBoundCZ
