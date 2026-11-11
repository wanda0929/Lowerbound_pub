import RequestProject.AppendixE.RotationAverage

/-!
Continuous symmetry audit. All printed dependencies must be standard Lean
axioms only. The candidate theorem retains only the superposition input;
it does not prove matrix/SOS feasibility or completeness.
-/

noncomputable section

namespace CZExposure

open MvPolynomial MeasureTheory PolynomialApproximation PolynomialSymmetry
open PolynomialIntegration RotationAction RotationAverage

local instance : MeasurableSpace Rotations := borel Rotations
local instance : BorelSpace Rotations := ⟨rfl⟩

#print axioms polynomialIntegral_degree
#print axioms linearMap_polynomialIntegral
#print axioms continuous_coeff_aeval
#print axioms rotate_mul
#print axioms rotate_vf
#print axioms rotate_exp
#print axioms rotatePoly_degree
#print axioms rotatePoly_drift
#print axioms continuous_coeff_rotatePoly
#print axioms rotationAverage_degree
#print axioms rotationAverage_invariant
#print axioms rotationAverage_initial
#print axioms rotationAverage_target_zero
#print axioms rotationAverage_residual
#print axioms Jmap_rotate
#print axioms exposureRotate_yPi
#print axioms rotationAverage_strictPolynomial
#print axioms symmetryAverage_degree
#print axioms symmetryAverage_isGInvariant
#print axioms symmetryAverage_initial
#print axioms symmetryAverage_target_zero
#print axioms symmetryAverage_residual
#print axioms symmetryAverage_strictPolynomial
#print axioms exists_G_invariant_candidate_below_Cstar

#check @symmetryAverage_initial
#check @symmetryAverage_strictPolynomial
#check @exists_G_invariant_candidate_below_Cstar

-- Probability normalization: constants survive with their original value.
example (c : ℝ) : rotationAverage (C c) = C c := by
  apply MvPolynomial.funext
  intro x
  simp [eval_rotationAverage]

-- The nonconstant invariant cost survives exactly, including its zero face.
example : rotationAverage costPoly = costPoly := by
  apply MvPolynomial.funext
  intro x
  simp [eval_rotationAverage, cost_rotate]

-- Averaging is not the identity: the real first-amplitude coordinate vanishes.
example : rotationAverage (X 0) = (0 : StatePoly) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_rotationAverage, map_zero]
  have h := integral_mul_left_eq_self
    (μ := rotationMeasure) (fun g : Rotations => eval (rotate g x) (X 0 : StatePoly))
    ((1, Circle.exp Real.pi) : Rotations)
  have hn : ∀ g : Rotations,
      eval (rotate (((1, Circle.exp Real.pi) : Rotations)*g) x) (X 0 : StatePoly) =
        -eval (rotate g x) (X 0 : StatePoly) := by
    intro g
    simp [rotate, phases, mkState, Circle.coe_exp, Complex.exp_pi_mul_I]
  simp_rw [hn] at h
  rw [integral_neg] at h
  linarith

-- No division by cost was used: the residual theorem includes x0, where cost=0.
example {W : StatePoly} {α : ℝ}
    (hW : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv W))
    {u : ℂ} (hu : ‖u‖ ≤ 1) (ξ : ℝ) :
    0 ≤ eval (pt ξ x0 u) (cpoly + lieDeriv (symmetryAverage W)) := by
  have hx : x0 ∈ Xset := FaceBlock.x0_mem_Fface.1
  have hc : cost x0 = 0 := ((Jmap_eq_y0_iff x0).mp Jmap_x0).1
  simpa only [hc, mul_zero] using symmetryAverage_residual hW hx hu ξ

end CZExposure
