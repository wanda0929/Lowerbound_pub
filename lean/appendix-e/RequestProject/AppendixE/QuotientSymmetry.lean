module

public import RequestProject.AppendixE.QuotientCertificate
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Symmetry projections preserve the normalization ideal algebraically. -/

@[expose] public section
noncomputable section
namespace CZExposure.QuotientSymmetry
open MvPolynomial QuotientNormalForm QuotientCertificate SymmetryGram
open scoped Matrix ComplexOrder

def chargePart (q : Charge) : MixedPoly →ₗ[ℂ] MixedPoly :=
  weightedHomogeneousComponent variableCharge q

private theorem generator_homogeneous {p : MixedPoly}
    (hp : p ∈ ({X 1 * X 2 - 1, X 3 * X 4 - (1 - X 5 * X 6),
      X 7 * X 8 - (1 - X 9 * X 10)} : Set MixedPoly)) :
    IsWeightedHomogeneous variableCharge p 0 := by
  have hx (i : Fin 11) := isWeightedHomogeneous_X (R := ℂ) variableCharge i
  have hpair (i j : Fin 11) (h : variableCharge i + variableCharge j = 0) :
      IsWeightedHomogeneous variableCharge (X i * X j : MixedPoly) 0 := by
    simpa only [h] using (hx i).mul (hx j)
  have h12 := hpair 1 2 (by dsimp [variableCharge]; norm_num)
  have h34 := hpair 3 4 (by dsimp [variableCharge]; norm_num)
  have h56 := hpair 5 6 (by dsimp [variableCharge]; norm_num)
  have h78 := hpair 7 8 (by dsimp [variableCharge]; norm_num)
  have h910 := hpair 9 10 (by dsimp [variableCharge]; norm_num)
  have h1 := isWeightedHomogeneous_one ℂ variableCharge
  have sub {f g : MixedPoly} (hf : IsWeightedHomogeneous variableCharge f 0)
      (hg : IsWeightedHomogeneous variableCharge g 0) :
      IsWeightedHomogeneous variableCharge (f - g) 0 :=
    (weightedHomogeneousSubmodule ℂ variableCharge 0).sub_mem hf hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact sub h12 h1
  · exact sub h34 (sub h1 h56)
  · exact sub h78 (sub h1 h910)

theorem chargePart_relations {p : MixedPoly} (hp : p ∈ relations) (q : Charge) :
    chargePart q p ∈ relations := by
  letI := weightedGradedAlgebra ℂ variableCharge
  have hI : relations.IsHomogeneous (weightedHomogeneousSubmodule ℂ variableCharge) := by
    apply Ideal.homogeneous_span
    intro p hp
    exact ⟨0, generator_homogeneous hp⟩
  have h := hI q hp
  change ((weightedDecomposition ℂ variableCharge).decompose' p q : MixedPoly) ∈ relations at h
  simpa only [weightedDecomposition.decompose'_apply] using h

theorem chargePart_congr {p r : MixedPoly} (h : p - r ∈ relations) (q : Charge) :
    chargePart q p - chargePart q r ∈ relations := by
  simpa only [map_sub] using chargePart_relations h q

theorem term_homogeneous (a : Fin 11 →₀ ℕ) (c : ℂ) :
    IsWeightedHomogeneous variableCharge (term a c) (monomialCharge a) := by
  rw [term_eq_monomial]
  apply isWeightedHomogeneous_monomial
  simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum_fintype, monomialCharge]

theorem conjugate_term (a : Fin 11 →₀ ℕ) (c : ℂ) :
    conjugate (term a c) = term (ConjugateGram.partner a) (starRingEnd ℂ c) := by
  simp only [term, map_mul, map_prod, map_pow, conjugate_C, conjugate_X]
  simp [ConjugateGram.partner, ConjugateGram.swap, Fin.prod_univ_succ]
  ring_nf
  simp

/-- Zero-charge projection deletes exactly the cross-charge Gram entries. -/
theorem chargePart_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Fin 11 →₀ ℕ) (Q : Matrix ι ι ℂ) :
    chargePart 0 (gram Q (fun i => term (a i) 1)) =
      gram (separate (fun i => monomialCharge (a i)) Q) (fun i => term (a i) 1) := by
  simp only [gram, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have ht := ((term_homogeneous (ConjugateGram.partner (a i)) 1).mul
    (isWeightedHomogeneous_C variableCharge (Q i j))).mul (term_homogeneous (a j) 1)
  rw [ConjugateGram.partner_charge] at ht
  simp only [add_zero] at ht
  rw [conjugate_term]
  simp only [map_one]
  change weightedHomogeneousComponent variableCharge 0 _ = _
  rw [weightedHomogeneousComponent_of_mem ht]
  by_cases h : monomialCharge (a i) = monomialCharge (a j)
  · simp [separate, h]
  · have hn : (0 : Charge) ≠ -monomialCharge (a i) + monomialCharge (a j) := by
      intro he
      apply h
      exact neg_add_eq_zero.mp he.symm
    simp [separate, h, hn]

def reflectCoordinate (i : Fin 11) : MixedPoly :=
  if i = 1 ∨ i = 2 then -X (ConjugateGram.swap i) else X (ConjugateGram.swap i)

def reflect : MixedPoly →ₐ[ℂ] MixedPoly := aeval reflectCoordinate

@[simp] theorem reflect_X (i : Fin 11) : reflect (X i) = reflectCoordinate i := by
  simp [reflect]

@[simp] theorem reflect_C (c : ℂ) : reflect (C c) = C c := by simp [reflect]

theorem reflect_relations {p : MixedPoly} (hp : p ∈ relations) : reflect p ∈ relations := by
  have h : relations ≤ Ideal.comap reflect.toRingHom relations := by
    apply Ideal.span_le.mpr
    intro f hf
    have he : reflect f = f := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl <;>
        simp [map_sub, map_mul, reflectCoordinate, ConjugateGram.swap] <;> ring
    change reflect f ∈ relations
    rw [he]
    exact Ideal.subset_span hf
  exact h hp

def reflectionAverage : MixedPoly →ₗ[ℂ] MixedPoly :=
  (1/2 : ℂ) • (LinearMap.id + reflect.toLinearMap)

theorem reflectionAverage_apply (p : MixedPoly) :
    reflectionAverage p = C (1/2) * (p + reflect p) := by
  simp [reflectionAverage, ← smul_eq_C_mul]

theorem reflectionAverage_relations {p : MixedPoly} (hp : p ∈ relations) :
    reflectionAverage p ∈ relations := by
  rw [reflectionAverage_apply]
  exact relations.mul_mem_left _ (relations.add_mem hp (reflect_relations hp))

theorem reflectionAverage_congr {p r : MixedPoly} (h : p - r ∈ relations) :
    reflectionAverage p - reflectionAverage r ∈ relations := by
  simpa only [map_sub] using reflectionAverage_relations h

theorem conjugate_involutive (p : MixedPoly) : conjugate (conjugate p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => simp_all
  | mul_X p i hp =>
    have hi : ConjugateGram.swap (ConjugateGram.swap i) = i := by fin_cases i <;> rfl
    simp_all

theorem reflect_conjugate (p : MixedPoly) : reflect (conjugate p) = conjugate (reflect p) := by
  have hx (i : Fin 11) : reflect (conjugate (X i)) = conjugate (reflect (X i)) := by
    fin_cases i <;> simp [reflectCoordinate, ConjugateGram.swap]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => simp_all
  | mul_X p i hp => simp_all

theorem reflect_gram {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) (z : ι → MixedPoly)
    (hz : ∀ i, reflect (z i) = conjugate (z i)) :
    reflect (gram Q z) = gram Q.transpose z := by
  simp only [gram, map_sum, map_mul, reflect_C, reflect_conjugate, hz, conjugate_involutive]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.transpose_apply]
  ring

/-- Once reflection acts as column conjugation, averaging replaces a
Hermitian Gram matrix by its entrywise real part, as a polynomial identity. -/
theorem reflectionAverage_gram {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) (z : ι → MixedPoly)
    (hz : ∀ i, reflect (z i) = conjugate (z i)) :
    reflectionAverage (gram Q z) = gram ((realMatrix Q).map Complex.ofReal) z := by
  rw [reflectionAverage_apply, reflect_gram Q z hz]
  simp only [gram, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hc : (C (1/2 : ℂ) : MixedPoly) * (C (Q i j) + C (Q j i)) = C ((Q i j).re : ℂ) := by
    have hh : Q j i = starRingEnd ℂ (Q i j) := by simpa using (hQ.apply j i).symm
    rw [hh, ← map_add, ← map_mul]
    congr 1
    rw [Complex.re_eq_add_conj]
    ring
  change C (1/2 : ℂ) * (conjugate (z i) * C (Q i j) * z j +
    conjugate (z i) * C (Q j i) * z j) = conjugate (z i) * C ((Q i j).re : ℂ) * z j
  calc
    _ = conjugate (z i) * (C (1/2 : ℂ) * (C (Q i j) + C (Q j i))) * z j := by ring
    _ = _ := by rw [hc]

theorem separated_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Fin 11 →₀ ℕ) (Q : Matrix ι ι ℂ) {p : MixedPoly}
    (h : p - gram Q (fun i => term (a i) 1) ∈ relations) :
    chargePart 0 p - gram (separate (fun i => monomialCharge (a i)) Q)
      (fun i => term (a i) 1) ∈ relations := by
  simpa only [chargePart_gram] using chargePart_congr h 0

theorem real_averaged_congr {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) (z : ι → MixedPoly)
    (hz : ∀ i, reflect (z i) = conjugate (z i)) {p : MixedPoly}
    (h : p - gram Q z ∈ relations) :
    reflectionAverage p - gram ((realMatrix Q).map Complex.ofReal) z ∈ relations := by
  simpa only [reflectionAverage_gram Q hQ z hz] using reflectionAverage_congr h

/-- Apply both quotient projections to an actual stationary identity.
The target is explicitly projected: identifying it with the original
residual still requires its polynomial symmetry identities. -/
theorem stationary_projected_identity {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ (s : Finset (Fin 11 →₀ ℕ)) (Q : Matrix s s ℂ),
      s ⊆ NormalFaceBasis.basis d ∧ Q.PosSemidef ∧
      (∀ i j, monomialCharge i.val ≠ monomialCharge j.val → Q i j = 0) ∧
      reflectionAverage (chargePart 0 (embed (cpoly + lieDeriv W))) -
        reflectionAverage (gram Q (fun i => term i.val 1)) ∈ relations := by
  obtain ⟨s, Q, hs, hQ, he⟩ := stationary_exact_gram hW
  refine ⟨s, separate (fun i => monomialCharge i.val) Q, hs,
    separate_posSemidef _ hQ, ?_, reflectionAverage_congr (separated_congr _ Q he)⟩
  intro i j hij
  simp [separate, hij]

end CZExposure.QuotientSymmetry
