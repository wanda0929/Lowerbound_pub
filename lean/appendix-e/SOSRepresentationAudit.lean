import RequestProject.AppendixE.SOSRepresentation
import RequestProject.AppendixE.SOSOrderBounds
import RequestProject.AppendixE.ScalarSOSRepresentation
import RequestProject.AppendixE.MatrixSOSApproximation
import RequestProject.AppendixE.MatrixSOSRemainder

/-! The generic matrix theorem is proved. Finite feasibility retains only
superposition and must have neither sorryAx nor a project axiom. -/

noncomputable section
namespace CZExposure
open MvPolynomial Matrix PolynomialGeometry PositiveResidualMatrix SOSRepresentation

#print axioms sum_variables
#print axioms norm_generators
#print axioms slice_archimedean
#print axioms freeze_norm_generator
#print axioms freeze_slice_mem
#print axioms physical_point_of_zeros
#print axioms gram_contraction
#print axioms residual_squares
#print axioms finite_order
#print axioms exists_stationary_feasible_below_Cstar
#check @MatrixPositivstellensatz
#check @exists_stationary_feasible_below_Cstar

-- Empty square families are legal, even for nonconstant W.
example : ∃ d, (X (2 : Fin 8) ^ 7 : StatePoly).totalDegree ≤ 2 * d - 1 ∧
    IsSOS d (0 : Poly) := by
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using
    finite_order (X (2 : Fin 8) ^ 7) (fun i : Fin 0 => Fin.elim0 i)

-- Unequal degrees, nonconstant W, and ξ-dependent square factors are allowed.
example : ∃ d, (X (1 : Fin 8)^9 : StatePoly).totalDegree ≤ 2 * d - 1 ∧
    IsSOS d ((xs 2 + 3 * ub)^2 + (X Var.xi^5 + xs 7)^2) := by
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using finite_order (X (1 : Fin 8)^9)
    ![xs 2 + 3 * ub, X Var.xi^5 + xs 7]

-- Removing the temporary equation preserves a nonzero normalization multiple.
example : freeze ((X Var.xi) * (xs 2 + ua) +
    ub * (ua^2 + ub^2 - 1)) ∈ normIdeal := by
  apply freeze_slice_mem
  apply sliceIdeal.add_mem
  · exact sliceIdeal.mul_mem_right _ ((le_sup_right :
      Ideal.span {X Var.xi} ≤ sliceIdeal) (Ideal.subset_span (by simp)))
  · exact (le_sup_left : normIdeal ≤ sliceIdeal)
      (normIdeal.mul_mem_left _ norm_generators.2.2)

-- M1 applies to the actual slice ideal without a matrix Positivstellensatz input.
example (p : Poly) : ∃ (N dp dm : ℕ) (sp sm : Poly),
    IsSOS dp sp ∧ IsSOS dm sm ∧
    C (N : ℝ)+p-sp ∈ sliceIdeal ∧ C (N : ℝ)-p-sm ∈ sliceIdeal := by
  letI : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm
  exact slice_archimedean.polynomial_order_certificates sliceIdeal p

-- Empty coordinate sets still include arbitrary real constants, including negative ones.
example : ∃ N : ℕ,
    IsSumSq ((N : (MvPolynomial (Fin 0) ℝ) ⧸ (⊥ : Ideal _)) +
      Ideal.Quotient.mk ⊥ (C (-7/3 : ℝ))) ∧
    IsSumSq ((N : (MvPolynomial (Fin 0) ℝ) ⧸ (⊥ : Ideal _)) -
      Ideal.Quotient.mk ⊥ (C (-7/3 : ℝ))) := by
  have hI : IdealArchimedean (⊥ : Ideal (MvPolynomial (Fin 0) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  exact hI.quotient_order_bounds _ _

-- No proper-ideal or pointed-cone assumption is smuggled into the theorem.
example (p : MvPolynomial (Fin 1) ℝ) :
    ∃ (N dp dm : ℕ) (sp sm : MvPolynomial (Fin 1) ℝ),
      IsSOS dp sp ∧ IsSOS dm sm ∧
      C (N : ℝ)+p-sp ∈ (⊤ : Ideal _) ∧ C (N : ℝ)-p-sm ∈ (⊤ : Ideal _) := by
  have hI : IdealArchimedean (⊤ : Ideal (MvPolynomial (Fin 1) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  exact hI.polynomial_order_certificates _ p

-- M2 on the physical slice, with no matrix or scalar representation hypothesis.
example (p : Poly)
    (hp : ∀ y : Var → ℝ, (∀ q ∈ sliceIdeal, eval y q = 0) → 0 < eval y p) :
    ∃ d s, IsSOS d s ∧ p-s ∈ sliceIdeal := by
  letI : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm
  exact slice_archimedean.scalar_representation sliceIdeal p hp

-- A polynomial positive only on the constrained variety, not on all of ℝ.
example : ∃ (d : ℕ) (s : MvPolynomial (Fin 1) ℝ),
    IsSOS d s ∧
      2 + X 0 - s ∈ Ideal.span ({X 0^2-1} : Set (MvPolynomial (Fin 1) ℝ)) := by
  let I : Ideal (MvPolynomial (Fin 1) ℝ) := Ideal.span {X 0^2-1}
  have hg : X (0:Fin 1)^2-1 ∈ I := Ideal.subset_span (by simp)
  have hI : IdealArchimedean I := by
    refine ⟨1, 0, 0, IsSOS.zero 0, ?_⟩
    simpa [Fin.sum_univ_one] using I.neg_mem hg
  obtain ⟨d, s, hs, hi⟩ := hI.scalar_representation I (2+X 0) (by
    intro y hy
    have he := hy _ hg
    simp only [eval_sub, eval_pow, eval_X, map_one] at he
    simp only [eval_add, eval_ofNat, eval_X]
    nlinarith [sq_nonneg (y 0 + 1)])
  exact ⟨d, s, hs, hi⟩

-- Constants and an empty coordinate type do not need a nonempty-variable assumption.
example : ∃ (d : ℕ) (s : MvPolynomial (Fin 0) ℝ),
    IsSOS d s ∧ C (2/7 : ℝ)-s ∈ (⊥ : Ideal _) := by
  have hI : IdealArchimedean (⊥ : Ideal (MvPolynomial (Fin 0) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  obtain ⟨d, s, hs, hi⟩ := hI.scalar_representation _ (C (2/7:ℝ)) (by
    intro y _; norm_num)
  exact ⟨d, s, hs, hi⟩

-- Empty real zero sets are allowed; this does not assume a proper ideal.
example (p : MvPolynomial (Fin 1) ℝ) : ∃ d s, IsSOS d s ∧ p-s ∈ (⊤ : Ideal _) := by
  have hI : IdealArchimedean (⊤ : Ideal (MvPolynomial (Fin 1) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  apply hI.scalar_representation _ p
  intro y hy
  have h := hy 1 (by trivial)
  simp at h

-- Negative control: an unconstrained negative constant has no such certificate.
example : ¬ ∃ (d : ℕ) (s : MvPolynomial (Fin 0) ℝ),
    IsSOS d s ∧ C (-1:ℝ)-s ∈ (⊥ : Ideal _) := by
  rintro ⟨d, s, hs, hi⟩
  have he : C (-1:ℝ) = s := sub_eq_zero.mp (by simpa using hi)
  have hp := hs.eval_nonneg (fun i : Fin 0 => Fin.elim0 i)
  rw [← he] at hp
  norm_num at hp

-- M3 supplies polynomial Gram approximation on the actual physical slice,
-- without a separate compactness, square-root, or approximation assumption.
example (A : Matrix (Fin 3) (Fin 3) Poly)
    (hp : ∀ x : Var → ℝ, (∀ p ∈ sliceIdeal, eval x p = 0) → (A.map (eval x)).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Matrix (Fin 3) (Fin 3) Poly,
      ∀ x : Var → ℝ, (∀ p ∈ sliceIdeal, eval x p = 0) → ∀ i j,
        |eval x (A i j - ∑ l, H l i * H l j)| < ε := by
  letI : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm
  obtain ⟨H, hH⟩ := slice_archimedean.polynomial_matrix_gram_approximation sliceIdeal A hp hε
  exact ⟨H, fun x hx i j => (hH x hx i j).2⟩

-- A nonscalar family with changing rank: B(t)=[[t,1],[0,t]], A(t)=B(t)ᵀB(t).
-- A(0) is singular, so a positive-definite-only continuity argument would not apply.
open scoped MatrixOrder in
example {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℝ),
      ∀ x : Set.Icc (fun _ : Fin 1 => (-1:ℝ)) (fun _ => (1:ℝ)), ∀ i j,
        let B : Matrix (Fin 2) (Fin 2) ℝ := !![x.val 0, 1; 0, x.val 0]
        |eval x.val (H i j) - CFC.sqrt (B.transpose * B) i j| < ε := by
  let K := Set.Icc (fun _ : Fin 1 => (-1:ℝ)) (fun _ => (1:ℝ))
  let B (x : K) : Matrix (Fin 2) (Fin 2) ℝ := !![x.val 0, 1; 0, x.val 0]
  have ht : Continuous (fun x : K => x.val 0) :=
    (continuous_apply (0:Fin 1)).comp continuous_subtype_val
  have hc : Continuous (fun x : K => (B x).transpose * B x) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two]
    · exact ht.mul ht
    · exact ht
    · exact ht
    · exact continuous_const.add (ht.mul ht)
  have hp (x : K) : ((B x).transpose * B x).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self (B x)
  obtain ⟨H, hH⟩ := exists_polynomial_sqrt_gram_approximation K isCompact_Icc
    (fun x => (B x).transpose * B x) hc hp hε
  exact ⟨H, fun x i j => (hH x i j).1⟩

-- Zero-dimensional matrices and coordinate spaces are allowed by M3.
example (A : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin 0) ℝ)) :
    ∃ H : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin 0) ℝ),
      ∀ x : Fin 0 → ℝ, ∀ i j, |eval x (A i j - ∑ l, H l i * H l j)| < 1 := by
  have hI : IdealArchimedean (⊥ : Ideal (MvPolynomial (Fin 0) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  have hp (x : Fin 0 → ℝ) : (A.map (eval x)).PosSemidef := by
    have he : A.map (eval x) = 0 := Subsingleton.elim _ _
    rw [he]; exact PosSemidef.zero
  obtain ⟨H, hH⟩ := hI.polynomial_matrix_gram_approximation _ A (fun x _ => hp x)
    (by norm_num : (0:ℝ) < 1)
  refine ⟨H, fun x i j => ?_⟩
  exact (hH x (by
    intro p hp
    have hz : p = 0 := by simpa using hp
    rw [hz, map_zero]) i j).2

-- M4 yields exact ideal membership on the actual physical slice, not merely
-- positivity on that slice or an arbitrarily accurate Gram approximation.
example (R : Matrix (Fin 3) (Fin 3) Poly) (hR : R.IsSymm)
    (hdd : ∀ x : Var → ℝ, (∀ p ∈ sliceIdeal, eval x p = 0) → ∀ i,
      (∑ j, if i=j then 0 else |eval x (R i j)|) < eval x (R i i)) :
    ∃ m, ∃ H : Matrix (Fin m) (Fin 3) Poly,
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ sliceIdeal := by
  letI : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm
  exact slice_archimedean.diagonally_dominant_gram sliceIdeal R hR hdd

-- Nonconstant off-diagonal entries change sign on the variety; the two
-- diagonal margins differ. A globally-positive or fixed-sign shortcut fails.
example : ∃ m, ∃ H : Matrix (Fin m) (Fin 2) (MvPolynomial (Fin 1) ℝ),
    ∀ i j, (!![2, X 0; X 0, 3] : Matrix (Fin 2) (Fin 2) _) i j -
      ∑ l, H l i * H l j ∈ Ideal.span ({X 0^2-1} : Set (MvPolynomial (Fin 1) ℝ)) := by
  let I : Ideal (MvPolynomial (Fin 1) ℝ) := Ideal.span {X 0^2-1}
  let R : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℝ) := !![2, X 0; X 0, 3]
  have hg : X (0:Fin 1)^2-1 ∈ I := Ideal.subset_span (by simp)
  have hI : IdealArchimedean I := by
    refine ⟨1, 0, 0, IsSOS.zero 0, ?_⟩
    simpa [Fin.sum_univ_one] using I.neg_mem hg
  apply hI.diagonally_dominant_gram I R
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x hx i
    have he := hx _ hg
    simp only [eval_sub, eval_pow, eval_X, map_one] at he
    have ha : |x 0| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    fin_cases i <;> simp [R, Fin.sum_univ_two] <;> linarith

-- M3-to-M4 error-budget interface, with a non-unit scalar shift.
example (R : Matrix (Fin 3) (Fin 3) Poly) (hR : R.IsSymm)
    (hclose : ∀ x : Var → ℝ, (∀ p ∈ sliceIdeal, eval x p = 0) → ∀ i j,
      |eval x (R i j) - (if i=j then (2/3:ℝ) else 0)| < 1/12) :
    ∃ m, ∃ H : Matrix (Fin m) (Fin 3) Poly,
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ sliceIdeal := by
  letI : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm
  apply slice_archimedean.near_scalar_gram sliceIdeal R hR (by norm_num : (0:ℝ)<2/3)
  norm_num
  exact hclose

-- Empty zero sets do not require a fabricated positive margin or proper ideal.
example (R : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℝ)) (hR : R.IsSymm) :
    ∃ m, ∃ H : Matrix (Fin m) (Fin 2) (MvPolynomial (Fin 1) ℝ),
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ (⊤ : Ideal _) := by
  have hI : IdealArchimedean (⊤ : Ideal (MvPolynomial (Fin 1) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  apply hI.diagonally_dominant_gram _ R hR
  intro x hx
  have h := hx 1 (by trivial)
  simp at h

-- No hidden positive matrix-dimension assumption in the compact-gap step.
example (R : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin 0) ℝ)) :
    ∃ m, ∃ H : Matrix (Fin m) (Fin 0) (MvPolynomial (Fin 0) ℝ),
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ (⊥ : Ideal _) := by
  have hI : IdealArchimedean (⊥ : Ideal (MvPolynomial (Fin 0) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  exact hI.diagonally_dominant_gram _ R (Subsingleton.elim _ _)
    (fun _ _ i => Fin.elim0 i)

-- Negative control: absolute diagonal dominance is insufficient. A negative
-- scalar matrix cannot have an exact unconstrained Gram representation.
example : ¬ ∃ m, ∃ H : Matrix (Fin m) (Fin 1) (MvPolynomial (Fin 0) ℝ),
    C (-1:ℝ) - ∑ l, H l 0 * H l 0 ∈ (⊥ : Ideal _) := by
  rintro ⟨m, H, hH⟩
  have he : C (-1:ℝ) = ∑ l, H l 0 * H l 0 := sub_eq_zero.mp (by simpa using hH)
  have hv := congrArg (eval (fun i : Fin 0 => Fin.elim0 i)) he
  simp only [eval_C, map_sum, map_mul] at hv
  have hn := Finset.sum_nonneg (fun (l : Fin m) (_ : l ∈ Finset.univ) =>
    mul_self_nonneg (eval (fun i : Fin 0 => Fin.elim0 i) (H l 0)))
  linarith

-- M5 applies on the actual slice with strict positivity, not diagonal dominance.
example (A : Matrix (Fin 4) (Fin 4) Poly) (hA : A.IsSymm)
    (hp : ∀ x : Var → ℝ, (∀ p ∈ sliceIdeal, eval x p = 0) → (A.map (eval x)).PosDef) :
    ∃ m, ∃ H : Matrix (Fin m) (Fin 4) Poly,
      ∀ i j, A i j - ∑ l, H l i * H l j ∈ sliceIdeal := by
  letI : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm
  exact matrixPositivstellensatz Var 4 (by norm_num) sliceIdeal slice_archimedean A hA hp

-- A positive definite family outside M4's input: on x²=1 its first row has
-- diagonal 1 and off-diagonal absolute value 2. Its quadratic form is
-- (v₀+2xv₁)²+v₁², so no diagonal-dominance hypothesis can replace positivity.
example : ∃ m, ∃ H : Matrix (Fin m) (Fin 2) (MvPolynomial (Fin 1) ℝ),
    ∀ i j, (!![1, 2*X 0; 2*X 0, 1+4*X 0^2] : Matrix (Fin 2) (Fin 2) _) i j -
      ∑ l, H l i * H l j ∈ Ideal.span ({X 0^2-1} : Set (MvPolynomial (Fin 1) ℝ)) := by
  let I : Ideal (MvPolynomial (Fin 1) ℝ) := Ideal.span {X 0^2-1}
  let A : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℝ) :=
    !![1, 2*X 0; 2*X 0, 1+4*X 0^2]
  have hg : X (0:Fin 1)^2-1 ∈ I := Ideal.subset_span (by simp)
  have hI : IdealArchimedean I := by
    refine ⟨1, 0, 0, IsSOS.zero 0, ?_⟩
    simpa [Fin.sum_univ_one] using I.neg_mem hg
  apply matrixPositivstellensatz (Fin 1) 2 (by norm_num) I hI A
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x _
    apply PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [A, conjTranspose_apply]
    · intro v hv
      simp [A, dotProduct, mulVec, Fin.sum_univ_two]
      by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv
          ext i
          fin_cases i <;> simp [h0, h1]
        simpa [h1, pow_two] using sq_pos_of_ne_zero h0
      · nlinarith [sq_nonneg (v 0 + 2*x 0*v 1), sq_pos_of_ne_zero h1]

-- An empty real variety is covered by M5, with no nonemptiness premise.
example (A : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℝ)) (hA : A.IsSymm) :
    ∃ m, ∃ H : Matrix (Fin m) (Fin 2) (MvPolynomial (Fin 1) ℝ),
      ∀ i j, A i j - ∑ l, H l i * H l j ∈ (⊤ : Ideal _) := by
  have hI : IdealArchimedean (⊤ : Ideal (MvPolynomial (Fin 1) ℝ)) :=
    ⟨0, 0, 0, IsSOS.zero 0, by simp⟩
  apply matrixPositivstellensatz (Fin 1) 2 (by norm_num) _ hI A hA
  intro x hx
  have h := hx 1 (by trivial)
  simp at h

run_cmd do
  for name in [``isSumSq_algebraMap_of_nonneg, ``SOSSquareBounded.scalar,
      ``SOSSquareBounded.add, ``SOSSquareBounded.mul, ``SOSSquareBounded.order_bounds,
      ``PolynomialGeometry.IsSOS.quotient_sumSq,
      ``IdealArchimedean.variable_square_bounded,
      ``IdealArchimedean.polynomial_square_bounded, ``IdealArchimedean.quotient_order_bounds,
      ``isSumSq_quotient_iff, ``IdealArchimedean.polynomial_order_certificates,
      ``neg_one_notMem_sosSeparatingCone, ``exists_sos_separating_state,
      ``isCompact_sosStates, ``extreme_sosState_mul,
      ``exists_nonpos_character_of_not_sumSq, ``isSumSq_of_pos_characters,
      ``quotient_character_evaluation, ``IdealArchimedean.scalar_representation,
      ``exists_polynomial_near_continuous, ``continuous_matrix_sqrt,
      ``matrix_sqrt_gram, ``exists_polynomial_matrix_near,
      ``gram_entry_error_le, ``exists_polynomial_sqrt_gram_approximation,
      ``IdealArchimedean.isCompact_realZeroSet,
      ``IdealArchimedean.polynomial_matrix_gram_approximation,
      ``finite_rankOne_gram, ``dd_decomposition,
      ``IdealArchimedean.matrix_gram_of_majorants, ``exists_dd_polynomial_majorants,
      ``IdealArchimedean.diagonally_dominant_gram, ``IdealArchimedean.near_scalar_gram,
      ``exists_uniform_matrix_shift, ``matrixPositivstellensatz,
      ``residual_squares, ``exists_stationary_feasible_below_Cstar] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

end CZExposure
