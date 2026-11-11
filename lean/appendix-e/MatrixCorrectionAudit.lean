import RequestProject.AppendixE.MatrixCorrection

/-! Audit of the uniform matrix correction, not of the still-missing
extraction of a polynomial matrix from the physical residual. -/

noncomputable section
open Matrix
open CZExposure.MatrixCorrection

#print axioms correction_mulVec
#print axioms correction_annihilates
#print axioms corrected_radial
#print axioms corrected_residual
#print axioms correction_quadratic
#print axioms correction_perpendicular
#print axioms correction_symmetric
#print axioms correction_nonneg
#print axioms correction_posSemidef
#print axioms corrected_posDef_of_posDef
#print axioms correction_zero_iff
#print axioms exists_uniform_penalty
#print axioms exists_corrected_posDef
#check @exists_corrected_posDef

-- The zero face must remain unchanged, even for a nonzero coefficient.
example (A : Matrix (Fin 4) (Fin 4) ℝ) (Λ : ℝ) : corrected A 0 Λ = A := by
  ext i j
  simp [corrected, correction, vecMulVec]

-- An indefinite matrix with positive radial value needs a sufficiently large
-- correction. Cross terms matter: repairing only its negative diagonal is
-- insufficient. At Λ=8 the quadratic form is (v0+2*v1)^2+v1^2.
example : (corrected (!![1, 2; 2, -3] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] 8).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.IsHermitian, conjTranspose, corrected, correction, vecMulVec,
        dotProduct, Fin.sum_univ_two]
  · intro v hv
    have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      ext i
      fin_cases i <;> simp [h]
    simp [corrected, correction, vecMulVec, dotProduct, mulVec, Fin.sum_univ_two]
    rcases hn with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0 + 2*v 1), sq_nonneg (v 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0 + 2*v 1)]

-- At Λ=7 it is still singular: the vector (-2,1) has zero quadratic form.
example : ¬ (corrected (!![1, 2; 2, -3] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] 7).PosDef := by
  intro h
  have hv : (![(-2 : ℝ), 1] : Fin 2 → ℝ) ≠ 0 := by
    intro he
    have := congrFun he 1
    norm_num at this
  have hp := h.dotProduct_mulVec_pos hv
  norm_num [corrected, correction, vecMulVec, dotProduct, mulVec, Fin.sum_univ_two] at hp
