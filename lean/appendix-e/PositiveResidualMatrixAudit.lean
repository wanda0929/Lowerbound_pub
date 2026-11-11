import RequestProject.AppendixE.PositiveResidualMatrix

/-! Audit of the physical positive-matrix construction. The nearly optimal
candidate keeps only superposition explicit. No SOS input is used yet. -/

noncomputable section
namespace CZExposure
open MvPolynomial Matrix PolynomialApproximation ResidualFactors PositiveResidualMatrix

#print axioms freeze
#print axioms eval_freeze
#print axioms freeze_amplitudes
#print axioms freeze_residual
#print axioms freeze_quadratic
#print axioms eval_amplitudes
#print axioms eval_quadratic
#print axioms cost_pos_of_amplitudes_ne_zero
#print axioms continuous_pt_zero
#print axioms continuous_realAmplitudes
#print axioms eval_corrected
#print axioms exists_positive_residual_matrix
#print axioms exists_positive_matrix_candidate_below_Cstar
#check @exists_positive_residual_matrix
#check @exists_positive_matrix_candidate_below_Cstar

-- Specialization removes only the cell coordinate, including mixed terms;
-- state and control coordinates and a nonzero constant must survive.
example : freeze (X Var.xi * xs 2 + X Var.xi^2 * ua + xs 3 * ub + C 7) = xs 3 * ub + C 7 := by
  simp [freeze]

-- Positivity checked at ξ=0 alone would be insufficient without specialization.
example : eval (pt (-2) x0 0) (C 1 + X Var.xi) = -1 ∧
    eval (pt (-2) x0 0) (freeze (C 1 + X Var.xi)) = 1 := by
  norm_num [freeze, pt]

-- A concrete admissible candidate demonstrates that the construction's margin
-- hypotheses are satisfiable. The resulting matrix is strictly positive even
-- at x0 (zero cost), for a zero disk control and a unit boundary control,
-- and at distinct nonzero values of the unused coordinate.
example : ∃ A : Matrix (Fin 4) (Fin 4) Poly,
    amplitudes ⬝ᵥ (A *ᵥ amplitudes) = cpoly ∧
    (A.map (eval (pt 17 x0 0))).PosDef ∧
    (A.map (eval (pt (-3) x0 1))).PosDef := by
  have hz : strictPolynomial (0 : ExposurePoly) 0 (1/2) = 0 := by
    simp [strictPolynomial, normalizedPolynomial, pullbackPoly]
  have hm : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      (1/2) * cost x ≤ eval (pt ξ x u)
        (cpoly + lieDeriv (strictPolynomial (0 : ExposurePoly) 0 (1/2))) := by
    intro x _ u _ ξ
    simp only [hz, lieDeriv_zero, add_zero, eval_pt_cpoly]
    linarith [cost_nonneg x]
  obtain ⟨A, _, hq, hp, _⟩ := exists_positive_residual_matrix 0 0 (1/2) (by norm_num) hm
  refine ⟨A, ?_, hp x0 FaceBlock.x0_mem_Fface.1 0 (by norm_num) 17,
    hp x0 FaceBlock.x0_mem_Fface.1 1 (by norm_num) (-3)⟩
  simpa only [hz, lieDeriv_zero, add_zero] using hq

end CZExposure
