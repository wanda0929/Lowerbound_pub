import RequestProject.AppendixE.PolynomialApproximation
import RequestProject.AppendixE.Completeness

/-!
# Polynomial approximation audit

Combined-import check: `PolynomialApproximation` and `Completeness`
load together. Axiom audit of every new public declaration added in
this milestone: the two generic calculus lemmas in `Calculus.lean`
and all public definitions, abbreviations, and theorems in
`PolynomialApproximation.lean`.

Expected: every audited declaration uses only standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound` where needed) — no
`sorryAx` and no project `External` axioms — with the integrated
conditional `Completeness` module also imported. This audit
does not assert that a `C¹` approximating polynomial exists; the
transfer theorems are conditional on supplied approximation data.
-/

noncomputable section

namespace CZExposure

/-! ## Generic calculus additions -/

#check @CZExposure.contDiff_eval
#print axioms CZExposure.contDiff_eval

#check @CZExposure.fderiv_eval_apply
#print axioms CZExposure.fderiv_eval_apply

end CZExposure

namespace CZExposure.PolynomialApproximation

open MvPolynomial CZExposure

/-! ## Polynomial definitions and approximation data -/

#check @ExposurePoly
#print axioms ExposurePoly

#check @costPoly
#print axioms costPoly

#check @zRealPoly
#print axioms zRealPoly

#check @zImagPoly
#print axioms zImagPoly

#check @Jpoly
#print axioms Jpoly

#check @pullbackPoly
#print axioms pullbackPoly

#check @normalizedPolynomial
#print axioms normalizedPolynomial

#check @strictPolynomial
#print axioms strictPolynomial

#check @centeredPullback
#print axioms centeredPullback

/- The approximation data, printed so the operator-norm and `Yset`
domain premises are visible. -/
#print C1ApproxOnY
#print axioms C1ApproxOnY

/-! ## Evaluation lemmas -/

#check @eval_costPoly
#print axioms eval_costPoly

#check @eval_zRealPoly
#print axioms eval_zRealPoly

#check @eval_zImagPoly
#print axioms eval_zImagPoly

#check @eval_Jpoly
#print axioms eval_Jpoly

#check @eval_pullbackPoly
#print axioms eval_pullbackPoly

#check @eval_normalizedPolynomial
#print axioms eval_normalizedPolynomial

#check @eval_strictPolynomial
#print axioms eval_strictPolynomial

/-! ## Geometric and analytic helpers -/

#check @y0_mem_Yset
#print axioms y0_mem_Yset

#check @yPi_mem_Yset
#print axioms yPi_mem_Yset

#check @Bfield_le_32
#print axioms Bfield_le_32

#check @centeredPullback_fderiv
#print axioms centeredPullback_fderiv

#check @centeredPullback_drift_eq
#print axioms centeredPullback_drift_eq

#check @centeredPullback_drift_error
#print axioms centeredPullback_drift_error

#check @eval_lieDeriv_eq_fderiv
#print axioms eval_lieDeriv_eq_fderiv

#check @normalization_denominator_pos
#print axioms normalization_denominator_pos

#check @normalized_fderiv_apply
#print axioms normalized_fderiv_apply

/- Strong zero-cost statement: no approximation input is needed;
the `DJ·vf = c·B` geometry alone kills the drift at `cost = 0`. -/
#check @normalized_drift_zero_of_cost_zero
#print axioms normalized_drift_zero_of_cost_zero

/-! ## Core transfer theorems -/

#check @normalized_drift_bound
#print axioms normalized_drift_bound

#check @normalized_target_zero
#print axioms normalized_target_zero

#check @normalized_initial_error
#print axioms normalized_initial_error

#check @strict_drift_bound
#print axioms strict_drift_bound

#check @strict_residual_bound
#print axioms strict_residual_bound

#check @strict_target_zero
#print axioms strict_target_zero

#check @strict_initial_error
#print axioms strict_initial_error

#check @exists_small_parameters
#print axioms exists_small_parameters

/- Final tolerance theorem: positive `α, η` are chosen first; every
supplied polynomial satisfying `C1ApproxOnY` then yields the strict
candidate. No existence of `P` is asserted. -/
#check @exists_tolerance_for_strict_candidate
#print axioms exists_tolerance_for_strict_candidate

/-! ## Concrete evaluation examples -/

/-- Centering cancels constants: `Q` built from a constant
approximant is the zero polynomial. -/
example (b η : ℝ) : normalizedPolynomial (C b) η = 0 := by
  simp [normalizedPolynomial, pullbackPoly]

/-- Evaluation identity only: this does not assert the base-function
rate hypothesis required by the transfer theorems. Uses `yPi 0 = -1`. -/
example (x : State) :
    eval x (normalizedPolynomial (X (0 : Fin 11)) 0) =
      (zObs x).re + 1 := by
  simp [eval_normalizedPolynomial, Jmap, yPi]

end CZExposure.PolynomialApproximation
