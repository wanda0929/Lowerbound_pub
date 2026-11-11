import RequestProject.AppendixE.ResidualFactors

/-! Audit of exact residual extraction. No normalization equations or
new external theorem inputs enter the polynomial identities. -/

noncomputable section
namespace CZExposure
open MvPolynomial Matrix PolynomialApproximation MatrixExtraction ResidualFactors

#print axioms amplitudeIdeal_cube
#print axioms exists_matrix_of_mem_cube
#print axioms symmetrize_symmetric
#print axioms symmetrize_quadratic
#print axioms symmetrize_mem
#print axioms exists_symmetric_matrix_of_mem_cube
#print axioms lieDeriv_add
#print axioms lieDeriv_sub
#print axioms lieDeriv_C
#print axioms lieDeriv_mul
#print axioms lieDeriv_X
#print axioms lieDeriv_zReal
#print axioms lieDeriv_zImag
#print axioms progress_drift_mem_cube
#print axioms cost_mem_square
#print axioms cost_drift_mem
#print axioms cost_square_drift_mem_cube
#print axioms Jpoly_drift_mem_cube
#print axioms pullback_drift_mem_cube
#print axioms strictPolynomial_drift_mem_cube
#print axioms costDiagonal_posDef
#print axioms costMatrix_quadratic
#print axioms eval_faceIdeal_zero
#print axioms exists_residual_matrix
#check @exists_residual_matrix

-- Asymmetric amplitudes and complex control detect conjugation/sign mistakes:
-- (3-4i)(5+6i)(1+2i)^2 = -109+162i.
private def probe : Var → ℝ
  | .st i => if i = 2 then 1 else if i = 3 then 2 else
      if i = 6 then 3 else if i = 7 then 4 else 7
  | .ctl i => ![5, 6] i
  | .xi => 11

example : eval probe (lieDeriv zRealPoly) = 81 * Real.sqrt 2 := by
  rw [lieDeriv_zReal]
  norm_num [probe, Fin.ext_iff]
  ring

example : eval probe (lieDeriv zImagPoly) = (109 / 2) * Real.sqrt 2 := by
  rw [lieDeriv_zImag]
  norm_num [probe, Fin.ext_iff]
  ring

example : eval probe (amplitudes ⬝ᵥ (costMatrix *ᵥ amplitudes)) = 35 / 4 := by
  rw [costMatrix_quadratic]
  norm_num [cpoly, probe, Fin.ext_iff]

-- Symmetrization preserves cross terms rather than discarding them.
example : symmetrize (!![1, 6; 2, 3] : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 4; 4, 3] := by
  ext i j
  simp only [symmetrize, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num

end CZExposure
