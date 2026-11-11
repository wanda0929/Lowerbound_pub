module

public import RequestProject.AppendixE.MatrixExtraction

/-! Cubic amplitude factors in the drift of exposure-coordinate polynomials. -/

@[expose] public section
noncomputable section

namespace CZExposure.ResidualFactors

open MvPolynomial PolynomialApproximation MatrixExtraction

def amplitudes : Fin 4 → Poly := ![xs 2, xs 3, xs 6, xs 7]
def faceIdeal : Ideal Poly := amplitudeIdeal amplitudes

theorem lieDeriv_add (P Q : StatePoly) : lieDeriv (P + Q) = lieDeriv P + lieDeriv Q := by
  simp [lieDeriv, ofState, add_mul, Finset.sum_add_distrib]

theorem lieDeriv_sub (P Q : StatePoly) : lieDeriv (P - Q) = lieDeriv P - lieDeriv Q := by
  simp [lieDeriv, ofState, sub_mul, Finset.sum_sub_distrib]

theorem lieDeriv_C (c : ℝ) : lieDeriv (C c) = 0 := by
  simp [lieDeriv, ofState]

@[simp] theorem lieDeriv_two : lieDeriv 2 = 0 := by
  exact lieDeriv_C 2

@[simp] theorem ofState_two : ofState 2 = 2 := by
  exact map_ofNat (rename Var.st) 2

theorem lieDeriv_mul (P Q : StatePoly) :
    lieDeriv (P * Q) = ofState P * lieDeriv Q + ofState Q * lieDeriv P := by
  simp only [lieDeriv, pderiv_mul, ofState, map_add, map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lieDeriv_X (i : Fin 8) : lieDeriv (X i) = fpoly i := by
  simp [lieDeriv, ofState, pderiv_X, Pi.single_apply, apply_ite]

theorem lieDeriv_zReal : lieDeriv zRealPoly =
    C (Real.sqrt 2 / 2) *
      ((xs 6 * ub - xs 7 * ua) * (xs 2^2 - xs 3^2) +
        (xs 6 * ua + xs 7 * ub) * (2 * xs 2 * xs 3)) := by
  simp only [zRealPoly, pow_two, lieDeriv_add, lieDeriv_sub, lieDeriv_mul,
    lieDeriv_C, lieDeriv_X]
  apply MvPolynomial.funext
  intro y
  simp [fpoly, ofState, show (rename Var.st) (2 : StatePoly) = 2 from ofState_two]
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem lieDeriv_zImag : lieDeriv zImagPoly =
    -C (Real.sqrt 2 / 2) *
      ((xs 6 * ua + xs 7 * ub) * (xs 2^2 - xs 3^2) -
        (xs 6 * ub - xs 7 * ua) * (2 * xs 2 * xs 3)) := by
  simp only [zImagPoly, pow_two, lieDeriv_add, lieDeriv_sub, lieDeriv_mul,
    lieDeriv_C, lieDeriv_X]
  apply MvPolynomial.funext
  intro y
  simp [fpoly, ofState, show (rename Var.st) (2 : StatePoly) = 2 from ofState_two]
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem amplitude_members : xs 2 ∈ faceIdeal ∧ xs 3 ∈ faceIdeal ∧
    xs 6 ∈ faceIdeal ∧ xs 7 ∈ faceIdeal :=
  ⟨amplitude_mem amplitudes 0, amplitude_mem amplitudes 1,
    amplitude_mem amplitudes 2, amplitude_mem amplitudes 3⟩

theorem mul_mem_cube {a b : Poly} (ha : a ∈ faceIdeal) (hb : b ∈ faceIdeal^2) :
    a*b ∈ faceIdeal^3 := by
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha hb

theorem progress_drift_mem_cube : lieDeriv zRealPoly ∈ faceIdeal^3 ∧
    lieDeriv zImagPoly ∈ faceIdeal^3 := by
  obtain ⟨h2, h3, h6, h7⟩ := amplitude_members
  have ha : xs 6 * ub - xs 7 * ua ∈ faceIdeal :=
    faceIdeal.sub_mem (faceIdeal.mul_mem_right _ h6) (faceIdeal.mul_mem_right _ h7)
  have hb : xs 6 * ua + xs 7 * ub ∈ faceIdeal :=
    faceIdeal.add_mem (faceIdeal.mul_mem_right _ h6) (faceIdeal.mul_mem_right _ h7)
  have hc : xs 2^2 - xs 3^2 ∈ faceIdeal^2 :=
    (faceIdeal^2).sub_mem (Ideal.pow_mem_pow h2 2) (Ideal.pow_mem_pow h3 2)
  have hd : 2 * xs 2 * xs 3 ∈ faceIdeal^2 := by
    rw [mul_assoc, pow_two]
    exact (faceIdeal*faceIdeal).mul_mem_left _ (Ideal.mul_mem_mul h2 h3)
  rw [lieDeriv_zReal, lieDeriv_zImag]
  exact ⟨(faceIdeal^3).mul_mem_left _
    ((faceIdeal^3).add_mem (mul_mem_cube ha hc) (mul_mem_cube hb hd)),
    (faceIdeal^3).mul_mem_left _
    ((faceIdeal^3).sub_mem (mul_mem_cube hb hc) (mul_mem_cube ha hd))⟩

theorem lieDeriv_mul_mem (I : Ideal Poly) {P Q : StatePoly}
    (hP : lieDeriv P ∈ I) (hQ : lieDeriv Q ∈ I) : lieDeriv (P*Q) ∈ I := by
  rw [lieDeriv_mul]
  exact I.add_mem (I.mul_mem_left _ hQ) (I.mul_mem_left _ hP)

theorem cost_mem_square : ofState costPoly ∈ faceIdeal^2 := by
  obtain ⟨h2, h3, h6, h7⟩ := amplitude_members
  simp only [ofState, costPoly, map_mul, map_add, map_pow, map_ofNat, rename_X, rename_C]
  exact (faceIdeal^2).mul_mem_left _ ((faceIdeal^2).add_mem
    ((faceIdeal^2).mul_mem_left _ ((faceIdeal^2).add_mem
      (Ideal.pow_mem_pow h2 2) (Ideal.pow_mem_pow h3 2)))
    ((faceIdeal^2).add_mem (Ideal.pow_mem_pow h6 2) (Ideal.pow_mem_pow h7 2)))

theorem cost_drift_mem : lieDeriv costPoly ∈ faceIdeal := by
  have hs (i : Fin 8) (hi : xs i ∈ faceIdeal) : lieDeriv (X i ^ 2) ∈ faceIdeal := by
    rw [pow_two, lieDeriv_mul]
    simp only [ofState, rename_X]
    exact faceIdeal.add_mem (faceIdeal.mul_mem_right _ hi) (faceIdeal.mul_mem_right _ hi)
  obtain ⟨h2, h3, h6, h7⟩ := amplitude_members
  unfold costPoly
  apply lieDeriv_mul_mem
  · simp [lieDeriv_C]
  · rw [lieDeriv_add]
    apply faceIdeal.add_mem
    · apply lieDeriv_mul_mem
      · simp
      · rw [lieDeriv_add]
        exact faceIdeal.add_mem (hs 2 h2) (hs 3 h3)
    · rw [lieDeriv_add]
      exact faceIdeal.add_mem (hs 6 h6) (hs 7 h7)

theorem cost_square_drift_mem_cube : lieDeriv (costPoly^2) ∈ faceIdeal^3 := by
  rw [pow_two, lieDeriv_mul]
  apply (faceIdeal^3).add_mem <;>
    simpa [mul_comm] using mul_mem_cube cost_drift_mem cost_mem_square

theorem Jpoly_drift_mem_cube (i : Fin 11) : lieDeriv (Jpoly i) ∈ faceIdeal^3 := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  · exact progress_drift_mem_cube.1
  · exact progress_drift_mem_cube.2
  · exact cost_square_drift_mem_cube
  · change lieDeriv (costPoly^2 * X i) ∈ faceIdeal^3
    rw [lieDeriv_mul]
    apply (faceIdeal^3).add_mem
    · have h4 : ofState (costPoly^2) ∈ faceIdeal^4 := by
        simpa [ofState, ← pow_mul] using Ideal.pow_mem_pow cost_mem_square 2
      exact (faceIdeal^3).mul_mem_right _ (Ideal.pow_le_pow_right (by omega) h4)
    · exact (faceIdeal^3).mul_mem_left _ cost_square_drift_mem_cube

theorem pullback_drift_mem_cube (P : ExposurePoly) :
    lieDeriv (pullbackPoly P) ∈ faceIdeal^3 := by
  unfold pullbackPoly
  induction P using MvPolynomial.induction_on with
  | C c => simp [lieDeriv_C]
  | add P Q hP hQ =>
      rw [map_add, lieDeriv_add]
      exact (faceIdeal^3).add_mem hP hQ
  | mul_X P i hP =>
      rw [map_mul, aeval_X]
      exact lieDeriv_mul_mem _ hP (Jpoly_drift_mem_cube i)

theorem strictPolynomial_drift_mem_cube (P : ExposurePoly) (η α : ℝ) :
    lieDeriv (strictPolynomial P η α) ∈ faceIdeal^3 := by
  unfold strictPolynomial normalizedPolynomial
  apply lieDeriv_mul_mem
  · rw [lieDeriv_C]
    exact (faceIdeal^3).zero_mem
  · apply lieDeriv_mul_mem
    · simp [lieDeriv_C]
    · rw [lieDeriv_sub, lieDeriv_C, sub_zero]
      exact pullback_drift_mem_cube P

open Matrix

def costWeights : Fin 4 → ℝ := ![1/2, 1/2, 1/4, 1/4]
def costMatrix : Matrix (Fin 4) (Fin 4) Poly := diagonal (fun i => C (costWeights i))

theorem costDiagonal_posDef : (diagonal costWeights).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [costWeights]

theorem costMatrix_symmetric : costMatrix.IsSymm := by
  exact Matrix.isSymm_diagonal _

theorem costMatrix_quadratic : amplitudes ⬝ᵥ (costMatrix *ᵥ amplitudes) = cpoly := by
  apply MvPolynomial.funext
  intro y
  norm_num [amplitudes, costMatrix, costWeights, dotProduct, mulVec, diagonal,
    Fin.sum_univ_four, cpoly, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem eval_faceIdeal_zero {p : Poly} (hp : p ∈ faceIdeal) (y : Var → ℝ)
    (hy : ∀ i, eval y (amplitudes i) = 0) : eval y p = 0 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  rw [← hc]
  simp [hy]

/-- The actual candidate residual admits an exact symmetric polynomial
matrix representation, equal on the zero-amplitude face to the positive
cost diagonal. No factorization hypothesis is supplied by the caller. -/
theorem exists_residual_matrix (P : ExposurePoly) (η α : ℝ) :
    ∃ A : Matrix (Fin 4) (Fin 4) Poly, A.IsSymm ∧
      amplitudes ⬝ᵥ (A *ᵥ amplitudes) = cpoly + lieDeriv (strictPolynomial P η α) ∧
      ∀ y : Var → ℝ, (∀ i, eval y (amplitudes i) = 0) →
        ∀ i j, eval y (A i j) = diagonal costWeights i j := by
  obtain ⟨B, hsym, hB, hq⟩ := exists_symmetric_matrix_of_mem_cube amplitudes
    (strictPolynomial_drift_mem_cube P η α)
  refine ⟨costMatrix + B, costMatrix_symmetric.add hsym, ?_, ?_⟩
  · rw [add_mulVec, dotProduct_add, costMatrix_quadratic, hq]
  · intro y hy i j
    have hb := eval_faceIdeal_zero (hB i j) y hy
    simp only [Matrix.add_apply, map_add, hb, add_zero]
    by_cases hij : i = j <;> simp [costMatrix, diagonal, hij]

end CZExposure.ResidualFactors
