module

public import RequestProject.AppendixE.ConjugateGram

/-! Exact mixed-coordinate certificate identities. These proofs operate in
the polynomial ring and its normalization quotient, not by inferring ideal
membership from equality on physical states. -/

@[expose] public section
noncomputable section
namespace CZExposure.QuotientCertificate
open MvPolynomial QuotientNormalForm ComplexConjugate
open scoped Matrix ComplexOrder

def embed : Poly →+* MixedPoly :=
  toMixed.toRingHom.comp (MvPolynomial.map Complex.ofRealHom)

@[simp] theorem embed_C (c : ℝ) : embed (C c) = C (c : ℂ) := by
  change toMixed (MvPolynomial.map Complex.ofRealHom (C c)) = _
  simp [toMixed]

@[simp] theorem embed_X (v : Var) : embed (X v) = encodeCoordinate v := by
  change toMixed (MvPolynomial.map Complex.ofRealHom (X v)) = _
  simp [toMixed]

theorem real_imag_square (i j : Fin 11) :
    realPart i j ^ 2 + imagPart i j ^ 2 = X i * X j := by
  apply MvPolynomial.funext
  intro z
  simp only [QuotientNormalForm.realPart, imagPart, map_add, map_mul, map_pow,
    map_sub, eval_C, eval_X]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem embed_state_norm₁ :
    embed (xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2 - 1) =
      X 3 * X 4 - (1 - X 5 * X 6) := by
  simp only [map_sub, map_add, map_pow, map_one, embed_X]
  change realPart 3 4 ^ 2 + imagPart 3 4 ^ 2 + realPart 5 6 ^ 2 + imagPart 5 6 ^ 2 - 1 = _
  rw [real_imag_square]
  have h := real_imag_square 5 6
  linear_combination h

theorem embed_state_norm₂ :
    embed (xs 4 ^ 2 + xs 5 ^ 2 + xs 6 ^ 2 + xs 7 ^ 2 - 1) =
      X 7 * X 8 - (1 - X 9 * X 10) := by
  simp only [map_sub, map_add, map_pow, map_one, embed_X]
  change realPart 7 8 ^ 2 + imagPart 7 8 ^ 2 + realPart 9 10 ^ 2 + imagPart 9 10 ^ 2 - 1 = _
  rw [real_imag_square]
  have h := real_imag_square 9 10
  linear_combination h

theorem embed_control_norm : embed (ua ^ 2 + ub ^ 2 - 1) = X 1 * X 2 - 1 := by
  simp only [map_sub, map_add, map_pow, map_one, embed_X]
  change realPart 1 2 ^ 2 + imagPart 1 2 ^ 2 - 1 = _
  rw [real_imag_square]

theorem embed_normIdeal {p : Poly} (hp : p ∈ normIdeal) : embed p ∈ relations := by
  have h : normIdeal ≤ Ideal.comap embed relations := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · change embed _ ∈ relations
      rw [embed_state_norm₁]
      exact Ideal.subset_span (by simp)
    · change embed _ ∈ relations
      rw [embed_state_norm₂]
      exact Ideal.subset_span (by simp)
    · change embed _ ∈ relations
      rw [embed_control_norm]
      exact Ideal.subset_span (by simp)
  exact h hp

theorem normalization_ideal_eq : Ideal.map embed normIdeal = relations := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (fun _ hp => embed_normIdeal hp)
  · apply Ideal.span_le.mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · rw [← embed_control_norm]
      exact Ideal.mem_map_of_mem embed (Ideal.subset_span (by simp))
    · rw [← embed_state_norm₁]
      exact Ideal.mem_map_of_mem embed (Ideal.subset_span (by simp))
    · rw [← embed_state_norm₂]
      exact Ideal.mem_map_of_mem embed (Ideal.subset_span (by simp))

theorem factor_congr (p : Poly) : embed p - factorExpansion p ∈ relations :=
  normalize_congr _

/-- The original stationary square identity survives coordinate conversion
and factor normalization exactly modulo the three normalization relations. -/
theorem normalized_squares {W : StatePoly} {N : ℕ} (h : Fin N → Poly)
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) :
    embed (cpoly + lieDeriv W) - ∑ l, factorExpansion (h l) ^ 2 ∈ relations := by
  apply Ideal.Quotient.eq.mp
  let π := Ideal.Quotient.mk relations
  have hf (l : Fin N) : π (embed (h l)) = π (factorExpansion (h l)) :=
    Ideal.Quotient.eq.mpr (factor_congr _)
  have hi := embed_normIdeal hdrift
  simp only [map_sub, map_sum, map_pow] at hi
  have he := Ideal.Quotient.eq.mpr hi
  change π (embed (cpoly + lieDeriv W)) = π (∑ l, factorExpansion (h l) ^ 2)
  change π (embed (cpoly + lieDeriv W)) = π (∑ l, embed (h l) ^ 2) at he
  simpa only [map_sum, map_pow, hf] using he

def conjugate : MixedPoly →+* MixedPoly :=
  (rename ConjugateGram.swap).toRingHom.comp (MvPolynomial.map (starRingEnd ℂ))

@[simp] theorem conjugate_C (c : ℂ) : conjugate (C c) = C (conj c) := by
  change rename ConjugateGram.swap (MvPolynomial.map (starRingEnd ℂ) (C c)) = _
  simp

@[simp] theorem conjugate_X (i : Fin 11) : conjugate (X i) = X (ConjugateGram.swap i) := by
  change rename ConjugateGram.swap (MvPolynomial.map (starRingEnd ℂ) (X i)) = _
  simp

theorem conjugate_coordinate (v : Var) : conjugate (encodeCoordinate v) = encodeCoordinate v := by
  cases v with
  | xi => simp [encodeCoordinate, ConjugateGram.swap]
  | ctl i =>
    fin_cases i <;> dsimp [encodeCoordinate]
    all_goals simp only [QuotientNormalForm.realPart, imagPart,
      map_mul, map_add, map_sub, conjugate_C, conjugate_X]
    all_goals simp only [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_I,
      mul_neg, div_neg, map_neg]
    all_goals dsimp [ConjugateGram.swap]
    all_goals ring
  | st i =>
    fin_cases i <;> dsimp [encodeCoordinate]
    all_goals simp only [QuotientNormalForm.realPart, imagPart,
      map_mul, map_add, map_sub, conjugate_C, conjugate_X]
    all_goals simp only [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_I,
      mul_neg, div_neg, map_neg]
    all_goals dsimp [ConjugateGram.swap]
    all_goals ring

theorem conjugate_embed (p : Poly) : conjugate (embed p) = embed p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp_all
  | mul_X p v hp => simp_all [conjugate_coordinate]

theorem conjugate_relations {p : MixedPoly} (hp : p ∈ relations) : conjugate p ∈ relations := by
  have h : relations ≤ Ideal.comap conjugate relations := by
    apply Ideal.span_le.mpr
    intro f hf
    have he : conjugate f = f := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl <;>
        simp [map_sub, map_mul, ConjugateGram.swap] <;> ring
    change conjugate f ∈ relations
    rw [he]
    exact Ideal.subset_span hf
  exact h hp

theorem factor_conjugate_congr (p : Poly) :
    conjugate (factorExpansion p) - factorExpansion p ∈ relations := by
  have h := conjugate_relations (factor_congr p)
  rw [map_sub, conjugate_embed] at h
  have hs := relations.sub_mem (factor_congr p) h
  convert hs using 1
  ring

def gram {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) (z : ι → MixedPoly) : MixedPoly :=
  ∑ i, ∑ j, conjugate (z i) * C (Q i j) * z j

theorem gram_factors {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (z : ι → MixedPoly) :
    gram (Aᴴ * A) z = ∑ k, conjugate (∑ i, C (A k i) * z i) * (∑ i, C (A k i) * z i) := by
  symm
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply,
    map_sum, map_mul, conjugate_C, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem factor_expansion_polynomial {N : ℕ} (h : Fin N → Poly) (l : Fin N) :
    (∑ i : StationaryGram.columns h, C (StationaryGram.coefficients h l i) * term i.val 1) =
      factorExpansion (h l) := by
  apply MvPolynomial.funext
  intro z
  simpa using StationaryGram.expansion_sum h l z

/-- Exact Gram certificate before charge separation and reflection averaging.
No physical-domain vanishing-to-ideal implication is used. -/
theorem normalized_gram {W : StatePoly} {N : ℕ} (h : Fin N → Poly)
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) :
    embed (cpoly + lieDeriv W) -
      gram ((StationaryGram.coefficients h)ᴴ * StationaryGram.coefficients h)
        (fun i => term i.val 1) ∈ relations := by
  rw [gram_factors]
  simp_rw [factor_expansion_polynomial]
  apply Ideal.Quotient.eq.mp
  let π := Ideal.Quotient.mk relations
  have hf (l : Fin N) : π (conjugate (factorExpansion (h l))) = π (factorExpansion (h l)) :=
    Ideal.Quotient.eq.mpr (factor_conjugate_congr _)
  have he := Ideal.Quotient.eq.mpr (normalized_squares h hdrift)
  change π (embed (cpoly + lieDeriv W)) = π (∑ l, _)
  change π (embed (cpoly + lieDeriv W)) = π (∑ l, factorExpansion (h l) ^ 2) at he
  simpa only [map_sum, map_mul, hf, map_pow, pow_two] using he

/-- Exact complex Gram data on degree-d normal face columns, before the
symmetry reductions. In particular the quotient identity is not inferred
from the previously constructed compressed matrix's physical values. -/
theorem stationary_exact_gram {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ (s : Finset (Fin 11 →₀ ℕ)) (Q : Matrix s s ℂ),
      s ⊆ NormalFaceBasis.basis d ∧ Q.PosSemidef ∧
      embed (cpoly + lieDeriv W) - gram Q (fun i => term i.val 1) ∈ relations := by
  obtain ⟨_, _, _, σ, ⟨N, h, hd, heq⟩, hdrift⟩ := hW
  rw [heq] at hdrift
  refine ⟨StationaryGram.columns h,
    (StationaryGram.coefficients h)ᴴ * StationaryGram.coefficients h, ?_,
    Matrix.posSemidef_conjTranspose_mul_self _, normalized_gram h hdrift⟩
  intro a ha
  have hc := StationaryGram.column_properties h hd ⟨a, ha⟩
  obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp ha
  exact NormalFaceBasis.mem_basis.mpr
    ⟨hc.1, NormalFaceBasis.stationary_factor_support hdrift l hl, hc.2⟩

theorem eval_conjugate (p : MixedPoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) (conjugate p) = conj (eval (mixedPoint ξ x u) p) := by
  have hc (i : Fin 11) : mixedPoint ξ x u (ConjugateGram.swap i) =
      conj (mixedPoint ξ x u i) := by
    fin_cases i <;> simp [mixedPoint, ConjugateGram.swap]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp_all
  | mul_X p i hp => simp_all

theorem eval_gram {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) (z : ι → MixedPoly)
    (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) (gram Q z) =
      SymmetryGram.value Q (fun i => eval (mixedPoint ξ x u) (z i)) := by
  simp [gram, SymmetryGram.value, eval_conjugate]

end CZExposure.QuotientCertificate
