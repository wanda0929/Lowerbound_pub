module

public import RequestProject.AppendixE.Hierarchy
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The finite-dimensional face-basis conversion in Appendix C.
Within one restriction-character group, the prescribed integer-coefficient
columns span exactly the coefficient combinations whose sum is zero.
This algebraic step does not identify the quotient-normal monomials or prove
independence of their distinct restriction characters on the physical face. -/

@[expose] public section
noncomputable section

namespace CZExposure.ReducedBasis

open MvPolynomial
open scoped Matrix

section Group

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- The manuscript's column indexed by ℓ > 0: Σ_{i<ℓ} mᵢ − ℓ mℓ. -/
def groupColumn (m : ℕ → V) (ℓ : ℕ) : V :=
  (∑ i ∈ Finset.range ℓ, m i) - (ℓ : K) • m ℓ

/-- No multiplication of monomials occurs in this change of coordinates. -/
theorem difference_mem_span (m : ℕ → V) (n k : ℕ) (hk : k ≤ n) :
    m k - m 0 ∈ Submodule.span K
      (Set.range fun l : Fin n => groupColumn (K := K) m (l.val + 1)) := by
  let S := Submodule.span K
    (Set.range fun l : Fin n => groupColumn (K := K) m (l.val + 1))
  change m k - m 0 ∈ S
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hzero : k = 0
    · subst k
      simp
    have hcol : groupColumn (K := K) m k ∈ S := by
      apply Submodule.subset_span
      refine ⟨⟨k - 1, by omega⟩, ?_⟩
      change groupColumn (K := K) m (k - 1 + 1) = groupColumn (K := K) m k
      rw [Nat.sub_add_cancel (by omega)]
    have hsum : (∑ i ∈ Finset.range k, (m i - m 0)) ∈ S :=
      S.sum_mem fun i hi => ih i (Finset.mem_range.mp hi)
        ((Finset.mem_range.mp hi).le.trans hk)
    have heq : (∑ i ∈ Finset.range k, (m i - m 0)) - groupColumn (K := K) m k =
        (k : K) • (m k - m 0) := by
      simp only [groupColumn, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, ← Nat.cast_smul_eq_nsmul K, smul_sub]
      abel
    have hmem := S.sub_mem hsum hcol
    rw [heq] at hmem
    exact (S.smul_mem_iff (by exact_mod_cast hzero)).mp hmem

/-- Every zero-sum coefficient vector has coordinates in the prescribed columns,
including the singleton group (n = 0), whose kernel is zero. -/
theorem group_conversion (m : ℕ → V) (n : ℕ) (a : Fin (n + 1) → K)
    (ha : ∑ i, a i = 0) :
    ∃ b : Fin n → K, (∑ i, a i • m i.val) =
      ∑ l, b l • groupColumn (K := K) m (l.val + 1) := by
  suffices h : (∑ i, a i • m i.val) ∈ Submodule.span K
      (Set.range fun l : Fin n => groupColumn (K := K) m (l.val + 1)) by
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h
    exact ⟨b, hb.symm⟩
  have heq : (∑ i, a i • m i.val) = ∑ i, a i • (m i.val - m 0) := by
    simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ha]
  rw [heq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (difference_mem_span m n i.val (by omega))

omit [CharZero K] in
/-- Equal restrictions make each group column vanish. This is an algebraic
restriction map, not an assumed physical-character independence theorem. -/
theorem groupColumn_restrict {U : Type*} [AddCommGroup U] [Module K U]
    (T : V →ₗ[K] U) (m : ℕ → V) (ℓ : ℕ)
    (hm : ∀ i ≤ ℓ, T (m i) = T (m 0)) :
    T (groupColumn (K := K) m ℓ) = 0 := by
  simp only [groupColumn, map_sub, map_sum, map_smul]
  rw [Finset.sum_congr rfl (fun i hi => hm i (by simpa using (Finset.mem_range.mp hi).le)),
    hm ℓ le_rfl]
  simp [← Nat.cast_smul_eq_nsmul K]

end Group

section Groups

variable {K V χ ι : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [Fintype χ] [DecidableEq χ] [Fintype ι]

omit [CharZero K] in
/-- A formal restriction records independent characters as finitely supported
coefficients. Its vanishing forces zero coefficient sum separately in each
group; cancellation between different characters is not allowed. -/
theorem restriction_group_sums (T : V →ₗ[K] (χ →₀ K))
    (z : ι → V) (m : χ → ℕ → V) (n : χ → ℕ)
    (hz : ∀ i, T (z i) = 0)
    (hm : ∀ c i, i ≤ n c → T (m c i) = Finsupp.single c 1)
    (a : ι → K) (b : (c : χ) → Fin (n c + 1) → K)
    (hzero : T ((∑ i, a i • z i) + ∑ c, ∑ j, b c j • m c j.val) = 0) :
    ∀ c, ∑ j, b c j = 0 := by
  intro c
  have h := congrArg (fun f : χ →₀ K => f c) hzero
  simp only [map_add, map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero,
    zero_add] at h
  have hm' (c : χ) (i : Fin (n c + 1)) : T (m c i.val) = Finsupp.single c 1 :=
    hm c i.val (by omega)
  simp only [hm', Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply] at h
  simpa [mul_ite, Finset.sum_ite_irrel] using h

/-- Conversion of all face-vanishing factors in an already grouped column.
The originally vanishing monomials z are retained unchanged. -/
theorem grouped_conversion (T : V →ₗ[K] (χ →₀ K))
    (z : ι → V) (m : χ → ℕ → V) (n : χ → ℕ)
    (hz : ∀ i, T (z i) = 0)
    (hm : ∀ c i, i ≤ n c → T (m c i) = Finsupp.single c 1)
    (a : ι → K) (b : (c : χ) → Fin (n c + 1) → K)
    (hzero : T ((∑ i, a i • z i) + ∑ c, ∑ j, b c j • m c j.val) = 0) :
    ∃ e : (c : χ) → Fin (n c) → K,
      (∑ i, a i • z i) + ∑ c, ∑ j, b c j • m c j.val =
        (∑ i, a i • z i) + ∑ c, ∑ l, e c l • groupColumn (K := K) (m c) (l.val + 1) := by
  have hs := restriction_group_sums T z m n hz hm a b hzero
  choose e he using fun c => group_conversion (m c) (n c) (b c) (hs c)
  exact ⟨e, congrArg (_ + ·) (Finset.sum_congr rfl fun c _ => he c)⟩

/-- The unreduced column, separating already vanishing monomials from groups. -/
def originalColumn (z : ι → V) (m : χ → ℕ → V) (n : χ → ℕ) :
    ι ⊕ ((c : χ) × Fin (n c + 1)) → V :=
  Sum.elim z (fun j => m j.1 j.2.val)

/-- Exactly the face column prescribed in Appendix C, without rescaling. -/
def reducedColumn (z : ι → V) (m : χ → ℕ → V) (n : χ → ℕ) :
    ι ⊕ ((c : χ) × Fin (n c)) → V :=
  Sum.elim z (fun j => groupColumn (K := K) (m j.1) (j.2.val + 1))

/-- The prescribed reduced column spans precisely the kernel of formal face
restriction in the original span. No independence of the original column is
needed, so the assertion also covers redundant columns. -/
theorem face_span_eq (T : V →ₗ[K] (χ →₀ K))
    (z : ι → V) (m : χ → ℕ → V) (n : χ → ℕ)
    (hz : ∀ i, T (z i) = 0)
    (hm : ∀ c i, i ≤ n c → T (m c i) = Finsupp.single c 1) :
    Submodule.span K (Set.range (originalColumn z m n)) ⊓ LinearMap.ker T =
      Submodule.span K (Set.range (reducedColumn (K := K) z m n)) := by
  classical
  apply le_antisymm
  · rintro p ⟨hp, hTp⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hp
    simp only [Fintype.sum_sum_type, originalColumn,
      Sum.elim_inl, Sum.elim_inr, Fintype.sum_sigma] at hTp ⊢
    obtain ⟨e, he⟩ := grouped_conversion T z m n hz hm
      (fun i => a (.inl i)) (fun c j => a (.inr ⟨c, j⟩)) hTp
    rw [he]
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨Sum.elim (fun i => a (.inl i)) (fun j => e j.1 j.2), ?_⟩
    simp [reducedColumn, Fintype.sum_sum_type, Fintype.sum_sigma]
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    cases j with
    | inl i =>
      exact ⟨Submodule.subset_span ⟨.inl i, rfl⟩, hz i⟩
    | inr j =>
      obtain ⟨c, l⟩ := j
      change groupColumn (K := K) (m c) (l.val + 1) ∈ _ ⊓ _
      constructor
      · apply Submodule.sub_mem
        · exact Submodule.sum_mem _ fun i hi =>
            Submodule.subset_span ⟨.inr ⟨c, ⟨i, by have := Finset.mem_range.mp hi; omega⟩⟩, rfl⟩
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨.inr ⟨c, ⟨l.val + 1, by omega⟩⟩, rfl⟩)
      · apply groupColumn_restrict
        intro i hi
        rw [hm c i (by omega), hm c 0 (Nat.zero_le _)]

end Groups

section Degree

variable {σ K : Type*} [Field K]

theorem groupColumn_degree (m : ℕ → MvPolynomial σ K) (ℓ d : ℕ)
    (hm : ∀ i ≤ ℓ, (m i).totalDegree ≤ d) :
    (groupColumn (K := K) m ℓ).totalDegree ≤ d := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact totalDegree_finsetSum_le fun i hi => hm i (Finset.mem_range.mp hi).le
  · exact (totalDegree_smul_le _ _).trans (hm ℓ le_rfl)

theorem reducedColumn_degree {χ ι : Type*}
    (z : ι → MvPolynomial σ K) (m : χ → ℕ → MvPolynomial σ K) (n : χ → ℕ)
    (d : ℕ) (hz : ∀ i, (z i).totalDegree ≤ d)
    (hm : ∀ c i, i ≤ n c → (m c i).totalDegree ≤ d)
    (j : ι ⊕ ((c : χ) × Fin (n c))) :
    (reducedColumn (K := K) z m n j).totalDegree ≤ d := by
  cases j with
  | inl i => exact hz i
  | inr j =>
    exact groupColumn_degree (m j.1) (j.2.val + 1) d
      (fun i hi => hm j.1 i (by omega))

end Degree

section Gram

variable {σ ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Real Gram representation after any coefficient-only factor conversion.
Q = AᵀA is positive semidefinite even when the columns are redundant. -/
theorem gram_conversion (h : κ → MvPolynomial σ ℝ) (A : Matrix ι κ ℝ) :
    ∃ Q : Matrix κ κ ℝ, Q.PosSemidef ∧
      (∑ i, (∑ j, A i j • h j)^2) =
        ∑ j, ∑ k, h j * C (Q j k) * h k := by
  refine ⟨Aᴴ * A, Matrix.posSemidef_conjTranspose_mul_self A, ?_⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    map_sum, map_mul, smul_eq_C_mul, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Gram

/-- Same-degree Gram conversion once the formal restriction of each factor
is zero. The identification of that restriction with physical face vanishing,
charge decomposition, and reflection rephasing are separate obligations. -/
theorem face_sos_gram {σ χ ι κ : Type*} [Fintype χ] [DecidableEq χ]
    [Fintype ι] [Fintype κ]
    (T : MvPolynomial σ ℝ →ₗ[ℝ] (χ →₀ ℝ))
    (z : ι → MvPolynomial σ ℝ) (m : χ → ℕ → MvPolynomial σ ℝ) (n : χ → ℕ)
    (hz : ∀ i, T (z i) = 0)
    (hm : ∀ c i, i ≤ n c → T (m c i) = Finsupp.single c 1)
    (d : ℕ) (hzd : ∀ i, (z i).totalDegree ≤ d)
    (hmd : ∀ c i, i ≤ n c → (m c i).totalDegree ≤ d)
    (f : κ → MvPolynomial σ ℝ)
    (hf : ∀ k, f k ∈ Submodule.span ℝ (Set.range (originalColumn z m n)))
    (hTf : ∀ k, T (f k) = 0) :
    let h := reducedColumn (K := ℝ) z m n
    (∀ j, (h j).totalDegree ≤ d) ∧
    ∃ Q : Matrix (ι ⊕ ((c : χ) × Fin (n c))) (ι ⊕ ((c : χ) × Fin (n c))) ℝ,
      Q.PosSemidef ∧ (∑ k, f k ^ 2) = ∑ i, ∑ j, h i * C (Q i j) * h j := by
  classical
  dsimp only
  refine ⟨reducedColumn_degree z m n d hzd hmd, ?_⟩
  have hs (k : κ) : f k ∈ Submodule.span ℝ
      (Set.range (reducedColumn (K := ℝ) z m n)) := by
    rw [← face_span_eq T z m n hz hm]
    exact ⟨hf k, hTf k⟩
  choose A hA using fun k => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hs k)
  obtain ⟨Q, hQ, heq⟩ := gram_conversion (reducedColumn (K := ℝ) z m n) A
  exact ⟨Q, hQ, by simpa only [hA] using heq⟩

end CZExposure.ReducedBasis
