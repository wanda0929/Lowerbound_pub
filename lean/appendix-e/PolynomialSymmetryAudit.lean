import RequestProject.AppendixE.PolynomialSymmetry
import RequestProject.AppendixE.Completeness

/-!
# Reflection averaging and initial-fibre audit

Every new declaration is audited below. Expected dependencies: only standard
Lean axioms, never `sorryAx` or project `External` axioms. The final candidate
theorem takes only superposition explicitly. No continuous rotation
average or SOS feasibility follows from these results.

The examples discriminate reflection-even and reflection-odd monomials, the
sign of the reflected control, and preservation of the objective for polynomials
in `J` versus arbitrary state polynomials.
-/

noncomputable section

namespace CZExposure.PolynomialSymmetry

open MvPolynomial ComplexConjugate PolynomialApproximation

#print axioms totalDegree_aeval_le
#print axioms reflectionSign
#print axioms reflection_apply
#print axioms reflectionCLM
#print axioms reflectionCLM_apply
#print axioms reflection_reflection
#print axioms reflection_x0
#print axioms cost_reflection
#print axioms reflection_mem_Xset
#print axioms reflection_mem_XCZ
#print axioms reflection_vf
#print axioms reflectPoly
#print axioms eval_reflectPoly
#print axioms reflectPoly_degree
#print axioms reflectionAverage
#print axioms eval_reflectionAverage
#print axioms reflectionAverage_degree
#print axioms reflectionAverage_invariant
#print axioms reflectionAverage_initial
#print axioms reflectionAverage_target_zero
#print axioms reflectPoly_drift
#print axioms reflectionAverage_drift
#print axioms reflectionAverage_residual
#print axioms cost_opticalGauge
#print axioms cost_qubitGauge
#print axioms zObs_opticalGauge
#print axioms zObs_qubitGauge
#print axioms Jmap_eq_y0_iff
#print axioms generators_preserve_initial_fibre
#print axioms strictPolynomial_initial_fibre
#print axioms reflection_opticalGauge
#print axioms reflection_qubitGauge
#print axioms reflectionAverage_isGInvariant
#print axioms exposureReflectionSign
#print axioms exposureReflection
#print axioms zObs_reflection
#print axioms Jmap_reflection
#print axioms exposureReflection_yPi
#print axioms exposureReflectionAverage
#print axioms eval_exposureReflectionAverage
#print axioms reflectionAverage_strictPolynomial
#print axioms exists_reflection_candidate_below_Cstar

#check @reflectionAverage_isGInvariant
#check @reflectionAverage_strictPolynomial
#check @exists_reflection_candidate_below_Cstar

-- An odd imaginary coordinate and a mixed odd term disappear; the even
-- imaginary square survives. This distinguishes averaging from substitution.
example : reflectionAverage (X 0 + C 3 * X 1 + C 2 * X 1 ^ 2 + X 0 * X 3) =
    (X 0 + C 2 * X 1 ^ 2 : StatePoly) := by
  apply MvPolynomial.funext
  intro x
  simp [reflection_apply, reflectionSign]
  ring

example : reflectionAverage (0 : StatePoly) = 0 := by
  simp [reflectionAverage, reflectPoly]

example (W : StatePoly) : reflectionAverage (reflectionAverage W) = reflectionAverage W := by
  apply MvPolynomial.funext
  intro x
  rw [eval_reflectionAverage, reflectionAverage_invariant]
  ring

-- Conjugating the control without its minus sign is wrong even at x0.
example : reflection (vf x0 1) ≠ vf (reflection x0) (conj 1) := by
  intro h
  have hh := congrFun h 3
  simp only [reflection_x0, map_one] at hh
  norm_num [reflection, vf, fC, mkState, g1, r1, g2, r2, x0,
    Complex.mul_re, Complex.mul_im, Matrix.cons_val_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hh

-- The initial fibre is preserved by rotations, but arbitrary polynomials
-- need not preserve their initial value along that fibre.
example : Jmap (qubitGauge Real.pi x0) = y0 :=
  (generators_preserve_initial_fibre Jmap_x0 0 Real.pi).2.1

example : eval (qubitGauge Real.pi x0) (X 0 : StatePoly) ≠ eval x0 (X 0 : StatePoly) := by
  norm_num [qubitGauge, mkState, g1, r1, g2, r2, x0, Complex.exp_pi_mul_I]

end CZExposure.PolynomialSymmetry
