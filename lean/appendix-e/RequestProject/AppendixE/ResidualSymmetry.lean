module

public import RequestProject.AppendixE.QuotientSymmetry

/-! Exact symmetry of the stationary residual, before taking a quotient. -/

@[expose] public section
noncomputable section
namespace CZExposure.ResidualSymmetry
open MvPolynomial QuotientNormalForm QuotientCertificate QuotientSymmetry SymmetryGram
open ComplexConjugate

private def cartesian : MixedPoly →ₐ[ℂ] MixedPoly := aeval
  ![X 0, X 1 + C Complex.I * X 2, X 1 - C Complex.I * X 2,
    X 3 + C Complex.I * X 4, X 3 - C Complex.I * X 4,
    X 5 + C Complex.I * X 6, X 5 - C Complex.I * X 6,
    X 7 + C Complex.I * X 8, X 7 - C Complex.I * X 8,
    X 9 + C Complex.I * X 10, X 9 - C Complex.I * X 10]

private theorem cartesian_injective : Function.Injective cartesian := by
  let back : MixedPoly →ₐ[ℂ] MixedPoly := aeval
    ![X 0, realPart 1 2, imagPart 1 2, realPart 3 4, imagPart 3 4,
      realPart 5 6, imagPart 5 6, realPart 7 8, imagPart 7 8,
      realPart 9 10, imagPart 9 10]
  have h : back.comp cartesian = AlgHom.id ℂ MixedPoly := by
    ext i : 1
    fin_cases i <;> simp [back, cartesian, QuotientNormalForm.realPart, imagPart]
      <;> ring_nf <;> simp [← map_pow]
      <;> rw [← add_mul, ← map_add] <;> norm_num
  intro p q hpq
  have := congrArg back hpq
  simpa only [← AlgHom.comp_apply, h, AlgHom.id_apply] using this

/-- Unrestricted real Cartesian coordinates determine a mixed polynomial.
No normalization or unit-control hypothesis is used. -/
theorem mixedPoint_ext {p q : MixedPoly}
    (h : ∀ (ξ : ℝ) (x : State) (u : ℂ),
      eval (mixedPoint ξ x u) p = eval (mixedPoint ξ x u) q) : p = q := by
  apply cartesian_injective
  apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  choose y hy using fun i => hz i (Set.mem_univ i)
  have hz' : z = fun i => (y i : ℂ) := funext (fun i => (hy i).symm)
  subst z
  let x : State := ![y 3, y 4, y 5, y 6, y 7, y 8, y 9, y 10]
  have he (p : MixedPoly) :
      eval (fun i => (y i : ℂ)) (cartesian p) =
        eval (mixedPoint (y 0) x ((y 1 : ℂ) + Complex.I * y 2)) p := by
    have hh (i : Fin 11) : eval (fun i => (y i : ℂ)) (cartesian (X i)) =
        mixedPoint (y 0) x ((y 1 : ℂ) + Complex.I * y 2) i := by
      fin_cases i <;> simp [cartesian, mixedPoint, x, g1, r1, g2, r2,
        Complex.mk_eq_add_mul_I, mul_comm, sub_eq_add_neg]
    induction p using MvPolynomial.induction_on with
    | C c => simp [cartesian]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, hh, eval_X]
  rw [he, he]
  exact h _ _ _

theorem eval_embed (p : Poly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) (embed p) = (eval (pt ξ x u) p : ℂ) := by
  change eval _ (toMixed (MvPolynomial.map Complex.ofRealHom p)) = _
  rw [eval_toMixed]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp_all
  | mul_X p i hp => simp_all

theorem eval_reflect (p : MixedPoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) (reflect p) =
      eval (mixedPoint ξ (reflection x) (-conj u)) p := by
  have hh (i : Fin 11) : eval (mixedPoint ξ x u) (reflect (X i)) =
      mixedPoint ξ (reflection x) (-conj u) i := by
    fin_cases i <;> simp [reflectCoordinate, ConjugateGram.swap, mixedPoint,
      reflection, mkState, g1, r1, g2, r2]
      <;> apply Complex.ext <;> simp
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, hh, eval_X]

theorem residual_reflect {W : StatePoly} (hW : IsGInvariant (fun x => eval x W)) :
    reflect (embed (cpoly + lieDeriv W)) = embed (cpoly + lieDeriv W) := by
  apply mixedPoint_ext
  intro ξ x u
  rw [eval_reflect, eval_embed, eval_embed, StationaryGram.residual_reflection hW]

theorem residual_reflectionAverage {W : StatePoly}
    (hW : IsGInvariant (fun x => eval x W)) :
    reflectionAverage (embed (cpoly + lieDeriv W)) = embed (cpoly + lieDeriv W) := by
  rw [reflectionAverage_apply, residual_reflect hW]
  have h : (C (1/2 : ℂ) : MixedPoly) + C (1/2 : ℂ) = 1 := by
    rw [← map_add]; norm_num
  linear_combination h * embed (cpoly + lieDeriv W)

/-- A finite character expansion extracts the zero-charge component of an
invariant evaluation. This does not assume projection is multiplicative. -/
theorem eval_chargePart_of_invariant (p : MixedPoly) (z : Fin 11 → ℂ)
    (h : ∀ t, eval (rotatePoint t z) p = eval z p) :
    eval z (chargePart 0 p) = eval z p := by
  classical
  let spectrum : FaceRestriction.FaceAlgebra := ∑ a ∈ p.support,
    AddMonoidAlgebra.single (chargeIndex (monomialCharge a)) (eval z (term a (coeff a p)))
  have he : spectrum = AddMonoidAlgebra.single 0 (eval z p) := by
    apply sub_eq_zero.mp
    apply FaceRestriction.eq_zero_of_evaluate
    intro t
    have hh : FaceRestriction.evaluate t spectrum = eval (rotatePoint t z) p := by
      conv_rhs => rw [← support_sum_monomial_coeff p]
      simp only [spectrum, map_sum, evaluate_charge_single]
      apply Finset.sum_congr rfl
      intro a _
      rw [← term_eq_monomial, monomial_response]
      ring
    rw [map_sub, hh, h]
    simp [FaceRestriction.evaluate]
  have hc := congrArg (fun f : FaceRestriction.FaceAlgebra => f 0) he
  have hz (q : Charge) : chargeIndex q = 0 ↔ q = 0 := by
    simpa [eq_comm] using (chargeIndex_sub_eq_zero 0 q)
  change (∑ a ∈ p.support, Finsupp.single (chargeIndex (monomialCharge a))
    (eval z (term a (coeff a p)))) 0 = (Finsupp.single 0 (eval z p) :
      FaceRestriction.Index →₀ ℂ) 0 at hc
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, hz, ite_true] at hc
  rw [← hc]
  conv_lhs => rw [← support_sum_monomial_coeff p]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← term_eq_monomial]
  change eval z (weightedHomogeneousComponent variableCharge 0 _) = _
  rw [weightedHomogeneousComponent_of_mem (term_homogeneous a (coeff a p))]
  by_cases ha : monomialCharge a = 0
  · simp [ha]
  · simp [ha, Ne.symm ha]

theorem residual_chargePart {W : StatePoly} (hW : IsGInvariant (fun x => eval x W)) :
    chargePart 0 (embed (cpoly + lieDeriv W)) = embed (cpoly + lieDeriv W) := by
  apply mixedPoint_ext
  intro ξ x u
  apply eval_chargePart_of_invariant
  intro t
  rw [rotatePoint_physical, eval_embed, eval_embed, StationaryGram.residual_rotate hW]

/-- Both projections fix the target literally, not merely modulo relations. -/
theorem residual_projections {W : StatePoly} (hW : IsGInvariant (fun x => eval x W)) :
    reflectionAverage (chargePart 0 (embed (cpoly + lieDeriv W))) =
      embed (cpoly + lieDeriv W) := by
  rw [residual_chargePart hW, residual_reflectionAverage hW]

open scoped Matrix ComplexOrder in
/-- Remove the target projection from the previously proved quotient identity. -/
theorem stationary_identity {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ (s : Finset (Fin 11 →₀ ℕ)) (Q : Matrix s s ℂ),
      s ⊆ NormalFaceBasis.basis d ∧ Q.PosSemidef ∧
      (∀ i j, monomialCharge i.val ≠ monomialCharge j.val → Q i j = 0) ∧
      embed (cpoly + lieDeriv W) -
        reflectionAverage (gram Q (fun i => term i.val 1)) ∈ relations := by
  obtain ⟨s, Q, hs, hQ, hsep, he⟩ := stationary_projected_identity hW
  rw [residual_projections hW.2.1] at he
  exact ⟨s, Q, hs, hQ, hsep, he⟩

/-- The prescribed phase factor makes reflection equal polynomial
conjugation for every monomial, without normalization or degree assumptions. -/
theorem reflect_rephased_term (a : Powers) :
    reflect (C (rephaser (decide (Odd (a 1 + a 2)))) * term a 1) =
      conjugate (C (rephaser (decide (Odd (a 1 + a 2)))) * term a 1) := by
  apply mixedPoint_ext
  intro ξ x u
  rw [eval_reflect, eval_conjugate]
  simp only [map_mul, eval_C]
  simpa only [map_mul] using rephased_monomial_reflection a ξ x u

/-- The reflection condition in the real-part Gram theorem is now proved
for any finite family of the prescribed rephased monomial columns. -/
theorem reflectionAverage_rephased_gram {ι : Type*} [Fintype ι]
    (a : ι → Powers) (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) :
    reflectionAverage (gram Q (fun i =>
      C (rephaser (decide (Odd (a i 1 + a i 2)))) * term (a i) 1)) =
    gram ((realMatrix Q).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (a i 1 + a i 2)))) * term (a i) 1) :=
  reflectionAverage_gram Q hQ _ (fun i => reflect_rephased_term (a i))

/-- Changing both the matrix and its columns preserves the entire Gram
polynomial, not only its values on the normalization variety. -/
theorem rephaseMatrix_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (odd : ι → Bool) (Q : Matrix ι ι ℂ) (z : ι → MixedPoly) :
    gram (rephaseMatrix odd Q) (fun i => C (rephaser (odd i)) * z i) = gram Q z := by
  apply mixedPoint_ext
  intro ξ x u
  simp only [eval_gram, map_mul, eval_C]
  exact rephaseMatrix_value odd Q _

open scoped Matrix ComplexOrder in
/-- Exact stationary certificate on rephased normal face columns with a
real positive matrix. Padding and conjugate-block compression are separate. -/
theorem stationary_real_identity {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ (s : Finset (Fin 11 →₀ ℕ)) (B : Matrix s s ℝ),
      s ⊆ NormalFaceBasis.basis d ∧ B.PosSemidef ∧
      (∀ i j, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
      embed (cpoly + lieDeriv W) - gram (B.map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) ∈ relations := by
  classical
  obtain ⟨s, Q, hs, hQ, hsep, he⟩ := stationary_identity hW
  let odd (i : s) := decide (Odd (i.val 1 + i.val 2))
  have hR := rephaseMatrix_posSemidef odd hQ
  refine ⟨s, realMatrix (rephaseMatrix odd Q), hs, realMatrix_posSemidef hR, ?_, ?_⟩
  · intro i j hij
    simp only [realMatrix, rephaseMatrix_blocks odd (fun i : s => monomialCharge i.val)
      Q hsep i j hij, Complex.zero_re]
  · rw [← rephaseMatrix_gram odd Q (fun i => term i.val 1)] at he
    rw [reflectionAverage_rephased_gram (fun i : s => (i.val : Powers)) _ hR.1] at he
    exact he

/-- Inclusion padding preserves the polynomial quadratic form for arbitrary
columns. The subset hypothesis prevents any source column from being lost. -/
theorem pad_gram {s t : Finset (Fin 11 →₀ ℕ)} (hs : s ⊆ t)
    (B : Matrix s s ℝ) (z : t → MixedPoly) :
    gram ((FaceGram.pad B).map Complex.ofReal) z =
      gram (B.map Complex.ofReal) (fun i => z ⟨i.val, hs i.property⟩) := by
  apply mixedPoint_ext
  intro ξ x u
  simp only [eval_gram]
  exact FaceGram.pad_value hs B _

open scoped Matrix ComplexOrder in
/-- A single matrix on the full prescribed degree-d face basis, with an
exact identity modulo normalization. Both conjugate charge blocks remain. -/
theorem stationary_fixed_identity {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ B : Matrix (NormalFaceBasis.basis d) (NormalFaceBasis.basis d) ℝ,
      B.PosSemidef ∧
      (∀ i j, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
      embed (cpoly + lieDeriv W) - gram (B.map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) ∈ relations := by
  obtain ⟨s, B, hs, hB, hb, he⟩ := stationary_real_identity hW
  refine ⟨FaceGram.pad B, FaceGram.pad_posSemidef hB, FaceGram.pad_blocks B hb, ?_⟩
  rw [pad_gram hs]
  exact he

open scoped Matrix ComplexOrder in
/-- Folding opposite charges preserves the polynomial, including the parity
signs on opposite columns. The zero-charge block contributes only once. -/
theorem compressed_gram {d : ℕ}
    {B : Matrix (NormalFaceBasis.basis d) (NormalFaceBasis.basis d) ℝ}
    (hB : B.PosSemidef)
    (hb : ∀ i j, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) :
    (∑ q ∈ ConjugateGram.retained d,
      gram ((ConjugateGram.compressedBlock B q).map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1)) =
    gram (B.map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) := by
  apply mixedPoint_ext
  intro ξ x u
  simp only [map_sum, eval_gram, map_mul, eval_C]
  change (∑ q ∈ ConjugateGram.retained d,
    value ((ConjugateGram.compressedBlock B q).map Complex.ofReal)
      (fun i => ConjugateGram.column i.val ξ x u)) =
    value (B.map Complex.ofReal) (fun i => ConjugateGram.column i.val ξ x u)
  simp_rw [ConjugateGram.compressedBlock_value hB]
  rw [ConjugateGram.sum_pairs, ConjugateGram.sum_blockValue B hb]

open scoped Matrix ComplexOrder in
/-- Exact stationary identity on one retained block per conjugate charge
pair, at the original degree and with real positive matrices. -/
theorem stationary_compressed_identity {d : ℕ} {W : StatePoly}
    (hW : StationaryFeasible d W) :
    ∃ Q : (q : Charge) → Matrix (ConjugateGram.sector d q) (ConjugateGram.sector d q) ℝ,
      (∀ q, (Q q).PosSemidef) ∧
      embed (cpoly + lieDeriv W) -
        (∑ q ∈ ConjugateGram.retained d, gram ((Q q).map Complex.ofReal) (fun i =>
          C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1)) ∈ relations := by
  obtain ⟨B, hB, hb, he⟩ := stationary_fixed_identity hW
  refine ⟨ConjugateGram.compressedBlock B, ConjugateGram.compressedBlock_posSemidef hB, ?_⟩
  rw [compressed_gram hB hb]
  exact he

end CZExposure.ResidualSymmetry
