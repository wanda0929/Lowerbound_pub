module

public import RequestProject.AppendixE.QuotientNormalForm

/-! Face restriction of fully quotient-normal monomials. Nonvanishing
normal monomials have distinct restriction characters, so their groups
are singletons. Face reduction retains exactly the excited monomials. -/

@[expose] public section
noncomputable section
namespace CZExposure.NormalFaceBasis
open MvPolynomial QuotientNormalForm

def Excited (a : Powers) : Prop := a 5 ≠ 0 ∨ a 6 ≠ 0 ∨ a 9 ≠ 0 ∨ a 10 ≠ 0

def key (a : Powers) : FaceRestriction.Index :=
  (a 0, ![(a 1 : ℤ) - a 2, (a 3 : ℤ) - a 4, (a 7 : ℤ) - a 8])

theorem key_injective {a b : Powers} (ha : Normal a) (hb : Normal b)
    (hea : ¬Excited a) (heb : ¬Excited b) (hk : key a = key b) : a = b := by
  have h0 := congrArg Prod.fst hk
  have h1 := congrArg (fun k : FaceRestriction.Index => k.2 0) hk
  have h2 := congrArg (fun k : FaceRestriction.Index => k.2 1) hk
  have h3 := congrArg (fun k : FaceRestriction.Index => k.2 2) hk
  dsimp [key] at h0 h1 h2 h3
  simp only [Excited, not_or, not_not] at hea heb
  dsimp [QuotientNormalForm.Normal] at ha hb
  funext i
  fin_cases i <;> dsimp <;> omega

theorem restriction_excited (a : Powers) (c : ℂ) (ha : Excited a) :
    mixedRestriction (term a c) = 0 := by
  simp only [term, map_mul, map_prod, map_pow]
  suffices (∏ i : Fin 11, mixedRestriction (X i) ^ a i) = 0 by rw [this, mul_zero]
  rcases ha with h | h | h | h
  · exact Finset.prod_eq_zero (Finset.mem_univ 5) (by simp [mixedRestriction, faceModes, h])
  · exact Finset.prod_eq_zero (Finset.mem_univ 6) (by simp [mixedRestriction, faceModes, h])
  · exact Finset.prod_eq_zero (Finset.mem_univ 9) (by simp [mixedRestriction, faceModes, h])
  · exact Finset.prod_eq_zero (Finset.mem_univ 10) (by simp [mixedRestriction, faceModes, h])

theorem restriction_unexcited (a : Powers) (c : ℂ) (ha : ¬Excited a) :
    mixedRestriction (term a c) = AddMonoidAlgebra.single (key a) c := by
  simp only [Excited, not_or, not_not] at ha
  simp only [term, map_mul, map_pow, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp only [mixedRestriction, aeval_C, aeval_X, map_one]
  dsimp [faceModes, FaceRestriction.coordinate, FaceRestriction.mode]
  simp only [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, pow_zero, mul_one,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.single_mul_single, one_mul]
  congr 1
  apply Prod.ext
  · simp [key]
  · funext i
    fin_cases i <;> simp [key] <;> omega

theorem support_excited {p : MixedPoly} (hn : ∀ a ∈ p.support, Normal a)
    (hz : mixedRestriction p = 0) {a : Fin 11 →₀ ℕ} (ha : a ∈ p.support) : Excited a := by
  classical
  by_contra he
  have hr : mixedRestriction p = ∑ b ∈ p.support, mixedRestriction (term b (coeff b p)) := by
    simp only [term_eq_monomial, ← map_sum, support_sum_monomial_coeff]
  have hc := congrArg (fun f : FaceRestriction.FaceAlgebra => f (key a)) hz
  rw [hr] at hc
  change (∑ b ∈ p.support, (mixedRestriction (term b (coeff b p)) :
    FaceRestriction.Index →₀ ℂ)) (key a) = 0 at hc
  rw [Finsupp.finset_sum_apply] at hc
  have hs : (∑ b ∈ p.support, mixedRestriction (term b (coeff b p)) (key a)) = coeff a p := by
    rw [Finset.sum_eq_single a]
    · rw [restriction_unexcited _ _ he]
      exact Finsupp.single_eq_same
    · intro b hb hba
      by_cases heb : Excited b
      · rw [restriction_excited _ _ heb]; rfl
      · rw [restriction_unexcited _ _ heb]
        apply Finsupp.single_eq_of_ne
        intro hk
        apply hba
        exact Finsupp.ext fun i => congrFun (key_injective (hn b hb) (hn a ha) heb he hk.symm) i
    · exact fun h => False.elim (h ha)
  rw [hs] at hc
  exact (mem_support_iff.mp ha) hc

theorem restriction_zero_iff {p : MixedPoly} (hn : ∀ a ∈ p.support, Normal a) :
    mixedRestriction p = 0 ↔ ∀ a ∈ p.support, Excited a := by
  constructor
  · exact fun hz _ ha => support_excited hn hz ha
  · intro he
    conv_lhs => rw [← support_sum_monomial_coeff p]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro a ha
    rw [← term_eq_monomial]
    exact restriction_excited _ _ (he a ha)

theorem stationary_factor_support {W : StatePoly} {N : ℕ} {h : Fin N → Poly}
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) (l : Fin N)
    {a : Fin 11 →₀ ℕ} (ha : a ∈ (factorExpansion (h l)).support) : Excited a :=
  support_excited (fun _ => factorExpansion_normal _) (stationary_expansion_restriction_zero hdrift l) ha

/-- The fixed degree-d face column, before conjugate-pair representative
selection. Charge blocks are obtained by filtering by monomial charge. -/
def basis (d : ℕ) : Finset (Fin 11 →₀ ℕ) := by
  classical
  exact (PolynomialIntegration.exponentBox 11 d).filter
    (fun a => Normal a ∧ Excited a ∧ (∑ i, a i) ≤ d)

theorem term_degree_exact (a : Fin 11 →₀ ℕ) :
    (term a (1 : ℂ)).totalDegree = ∑ i, a i := by
  rw [term_eq_monomial, totalDegree_monomial _ one_ne_zero]
  simp [Finsupp.sum_fintype]

theorem mem_basis {a : Fin 11 →₀ ℕ} {d : ℕ} : a ∈ basis d ↔
    Normal a ∧ Excited a ∧ (term a 1).totalDegree ≤ d := by
  classical
  rw [basis, Finset.mem_filter, term_degree_exact]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    simp only [PolynomialIntegration.exponentBox, Finset.mem_Iic]
    intro i
    change a i ≤ d
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans h.2.2

theorem basis_restriction_zero {d : ℕ} (a : basis d) : mixedRestriction (term a.val 1) = 0 :=
  restriction_excited _ _ (mem_basis.mp a.property).2.1

/-- Exact face-kernel span on the fully normal, degree-bounded space. Since
unexcited restriction groups are singletons, the manuscript's difference
columns contribute nothing in this presentation. -/
theorem face_span_iff {p : MixedPoly} {d : ℕ}
    (hn : ∀ a ∈ p.support, Normal a) (hd : p.totalDegree ≤ d) :
    mixedRestriction p = 0 ↔
      p ∈ Submodule.span ℂ (Set.range (fun a : basis d => term a.val 1)) := by
  classical
  constructor
  · intro hz
    rw [← support_sum_monomial_coeff p]
    apply Submodule.sum_mem
    intro a ha
    have hb : a ∈ basis d := mem_basis.mpr ⟨hn a ha, support_excited hn hz ha, by
      rw [term_degree_exact]
      simpa [Finsupp.sum_fintype] using (le_totalDegree ha).trans hd⟩
    have heq : monomial a (coeff a p) = coeff a p • term a 1 := by
      simp [term_eq_monomial, smul_monomial]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, hb⟩, rfl⟩)
  · intro hp
    have hs : Submodule.span ℂ (Set.range (fun a : basis d => term a.val 1)) ≤
        LinearMap.ker mixedRestriction.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact basis_restriction_zero a
    exact hs hp

end CZExposure.NormalFaceBasis
