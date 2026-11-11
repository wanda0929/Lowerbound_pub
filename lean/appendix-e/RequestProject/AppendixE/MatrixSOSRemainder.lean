module
public import RequestProject.AppendixE.ScalarSOSRepresentation
public import RequestProject.AppendixE.MatrixSOSApproximation
public import Mathlib.Algebra.MvPolynomial.Funext

/-! M4: exact finite matrix SOS certificates for diagonally dominant remainders. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry
open MvPolynomial Matrix Set

variable {σ : Type} {k : ℕ}

/-- Stack finite scalar SOS families multiplied by polynomial row vectors.
The result has a single finite row count and exact entrywise ideal membership. -/
theorem finite_rankOne_gram {ι : Type*} [Fintype ι]
    (I : Ideal (MvPolynomial σ ℝ)) (c : ι → MvPolynomial σ ℝ)
    (v : ι → Fin k → MvPolynomial σ ℝ)
    (hc : ∀ a, ∃ d s, CZExposure.IsSOS d s ∧ c a-s ∈ I) :
    ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin k) (MvPolynomial σ ℝ),
      ∀ i j, (∑ a, c a*v a i*v a j) - ∑ l, H l i*H l j ∈ I := by
  classical
  choose d s hs hi using hc
  choose n f hf he using hs
  let J := Σ a : ι, Fin (n a)
  let G (t : J) (i : Fin k) := f t.1 t.2 * v t.1 i
  let e := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun l i => G (e l) i, fun i j => ?_⟩
  rw [e.sum_comp (fun t => G t i * G t j)]
  have hsum : ∑ t : J, G t i * G t j = ∑ a, s a * v a i * v a j := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    rw [he a, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [G]
    ring
  rw [hsum, ← Finset.sum_sub_distrib]
  apply I.sum_mem
  intro a _
  convert I.mul_mem_right (v a j) (I.mul_mem_right (v a i) (hi a)) using 1; ring

/-- Directions used for diagonal terms and the two signs of every ordered
pair. Ordering pairs twice is compensated by the coefficient 1/4. -/
def ddDirection (a : Fin k ⊕ (Fin k × Fin k × Bool)) (i : Fin k) : ℝ :=
  match a with
  | .inl j => if i = j then 1 else 0
  | .inr (j, l, b) => (if i = j then 1 else 0) +
      (if b then 1 else -1) * (if i = l then 1 else 0)

def ddCoefficient (R B : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ)) :
    (Fin k ⊕ (Fin k × Fin k × Bool)) → MvPolynomial σ ℝ
  | .inl i => R i i - ∑ j, if i = j then 0 else B i j
  | .inr (i, j, b) => if i = j then 0 else
      (1/4:ℝ) • (B i j + (if b then R i j else -R i j))

private theorem pair_sum_real (F : Matrix (Fin k) (Fin k) ℝ) (hs : F.IsSymm)
    (s : ℝ) (i j : Fin k) :
    (∑ a, ∑ b, F a b * ((if i=a then 1 else 0)+s*(if i=b then 1 else 0)) *
      ((if j=a then 1 else 0)+s*(if j=b then 1 else 0))) =
      (if i=j then (1+s^2)*∑ b, F i b else 0) + 2*s*F i j := by
  classical
  have he (a b : Fin k) :
      F a b * ((if i=a then 1 else 0)+s*(if i=b then 1 else 0)) *
        ((if j=a then 1 else 0)+s*(if j=b then 1 else 0)) =
      F a b*(if i=a then 1 else 0)*(if j=a then 1 else 0) +
      s*F a b*(if i=a then 1 else 0)*(if j=b then 1 else 0) +
      s*F a b*(if i=b then 1 else 0)*(if j=a then 1 else 0) +
      s^2*F a b*(if i=b then 1 else 0)*(if j=b then 1 else 0) := by ring
  simp_rw [he, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  by_cases hij : i=j
  · subst j
    simp [hs.apply]
    simp only [← Finset.mul_sum]
    ring
  · simp [hij, hs.apply]
    ring

/-- Exact polynomial identity behind the diagonal-dominance certificate.
No positivity or ideal assumptions enter this algebraic step. -/
theorem dd_decomposition (R B : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ))
    (hR : R.IsSymm) (hB : B.IsSymm) (i j : Fin k) :
    R i j = ∑ a, ddCoefficient R B a * C (ddDirection a i) * C (ddDirection a j) := by
  classical
  apply MvPolynomial.funext
  intro x
  let W (t : Bool) : Matrix (Fin k) (Fin k) ℝ :=
    fun a b => eval x (ddCoefficient R B (.inr (a,b,t)))
  have hW (t : Bool) : (W t).IsSymm := by
    ext a b
    change W t b a = W t a b
    by_cases hab : a=b
    · subst b; rfl
    · simp [W, ddCoefficient, hab, Ne.symm hab, hR.apply a b, hB.apply a b]
  have hpair (t : Bool) :
      (∑ a, ∑ b, W t a b * ddDirection (.inr (a,b,t)) i * ddDirection (.inr (a,b,t)) j) =
      (if i=j then (1+(if t then (1:ℝ) else -1)^2)*∑ b, W t i b else 0) +
        2*(if t then (1:ℝ) else -1)*W t i j :=
    pair_sum_real (W t) (hW t) _ i j
  have hrows : (∑ b, W true i b) + (∑ b, W false i b) =
      (∑ b, if i=b then 0 else eval x (B i b))/2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hib : i=b
    · simp [W, ddCoefficient, hib]
    · simp [W, ddCoefficient, hib]
      ring
  simp only [map_sum, map_add, map_mul, eval_C, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
  change eval x (R i j) =
    (∑ a, eval x (ddCoefficient R B (.inl a)) * ddDirection (.inl a) i * ddDirection (.inl a) j) +
    ((∑ a, ∑ b, W true a b * ddDirection (.inr (a,b,true)) i * ddDirection (.inr (a,b,true)) j) +
     (∑ a, ∑ b, W false a b * ddDirection (.inr (a,b,false)) i * ddDirection (.inr (a,b,false)) j))
  rw [hpair true, hpair false]
  by_cases hij : i=j
  · subst j
    simp [ddDirection, W, ddCoefficient, mul_ite]
    simp [W, ddCoefficient] at hrows
    simp only [apply_ite (eval x), map_zero] at hrows ⊢
    linarith
  · simp [ddDirection, hij, W, ddCoefficient]
    ring

/-- Polynomial upper bounds for the off-diagonal absolute values turn the
rank-one decomposition into an exact finite Gram certificate modulo I. -/
theorem IdealArchimedean.matrix_gram_of_majorants [Fintype σ]
    (I : Ideal (MvPolynomial σ ℝ)) (hI : IdealArchimedean I)
    (R B : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ)) (hR : R.IsSymm) (hB : B.IsSymm)
    (hoff : ∀ x : σ → ℝ, (∀ p ∈ I, eval x p = 0) → ∀ i j, i ≠ j →
      |eval x (R i j)| < eval x (B i j))
    (hdiag : ∀ x : σ → ℝ, (∀ p ∈ I, eval x p = 0) → ∀ i,
      (∑ j, if i=j then 0 else eval x (B i j)) < eval x (R i i)) :
    ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin k) (MvPolynomial σ ℝ),
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ I := by
  classical
  have hc (a : Fin k ⊕ (Fin k × Fin k × Bool)) :
      ∃ d s, CZExposure.IsSOS d s ∧ ddCoefficient R B a-s ∈ I := by
    rcases a with i | ⟨i,j,b⟩
    · apply hI.scalar_representation
      intro x hx
      simpa [ddCoefficient, apply_ite] using sub_pos.mpr (hdiag x hx i)
    · by_cases hij : i=j
      · exact ⟨0, 0, IsSOS.zero 0, by simp [ddCoefficient, hij]⟩
      · apply hI.scalar_representation
        intro x hx
        have hab := abs_lt.mp (hoff x hx i j hij)
        cases b <;> simp [ddCoefficient, hij] <;> linarith
  obtain ⟨m, H, hH⟩ := finite_rankOne_gram I (ddCoefficient R B)
    (fun a i => C (ddDirection a i)) hc
  refine ⟨m, H, fun i j => ?_⟩
  rw [dd_decomposition R B hR hB i j]
  exact hH i j

/-- Strict row diagonal dominance on a compact set admits symmetric
polynomial majorants with enough room left on every diagonal. Absolute
values themselves are not falsely treated as polynomials. -/
theorem exists_dd_polynomial_majorants (K : Set (σ → ℝ)) (hK : IsCompact K)
    (R : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ)) (hR : R.IsSymm)
    (hdd : ∀ x : K, ∀ i,
      (∑ j, if i=j then 0 else |eval x.val (R i j)|) < eval x.val (R i i)) :
    ∃ B : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ), B.IsSymm ∧
      (∀ x : K, ∀ i j, i ≠ j → |eval x.val (R i j)| < eval x.val (B i j)) ∧
      ∀ x : K, ∀ i, (∑ j, if i=j then 0 else eval x.val (B i j)) < eval x.val (R i i) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let gap (z : K × Fin k) := eval z.1.val (R z.2 z.2) -
    ∑ j, if z.2=j then 0 else |eval z.1.val (R z.2 j)|
  have hgpos (z : K × Fin k) : 0 < gap z := sub_pos.mpr (hdd z.1 z.2)
  have hgcont : Continuous gap := by
    apply continuous_prod_of_discrete_right.mpr
    intro i
    apply Continuous.sub ((R i i).continuous_eval.comp continuous_subtype_val)
    apply continuous_finset_sum
    intro j _
    by_cases hij : i=j
    · simp [hij]; exact continuous_const
    · simpa [hij] using ((R i j).continuous_eval.comp continuous_subtype_val).abs
  obtain ⟨η, hη, hgap⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z, η ≤ gap z := by
    by_cases hn : Nonempty (K × Fin k)
    · letI := hn
      obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hgcont.continuousOn
      exact ⟨gap z, hgpos z, fun w => hz (Set.mem_univ w)⟩
    · exact ⟨1, zero_lt_one, fun z => False.elim (hn ⟨z⟩)⟩
  let δ : ℝ := η / (4*((k:ℝ)+1))
  have hden : 0 < 4*((k:ℝ)+1) := by positivity
  have hd : 0 < δ := div_pos hη hden
  have hδ : 4*((k:ℝ)+1)*δ = η := by dsimp [δ]; field_simp
  have hex (i j : Fin k) := exists_polynomial_near_continuous K hK
    ⟨fun x => |eval x.val (R i j)|,
      ((R i j).continuous_eval.comp continuous_subtype_val).abs⟩ hd
  choose P hP using hex
  let B : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ) :=
    fun i j => (1/2:ℝ) • (P i j+P j i) + C (2*δ)
  have hb (x : K) (i j : Fin k) :
      |eval x.val (R i j)| < eval x.val (B i j) ∧
        eval x.val (B i j) < |eval x.val (R i j)|+3*δ := by
    have hp := abs_lt.mp (hP i j x)
    have hq := abs_lt.mp (hP j i x)
    rw [hR.apply i j] at hq
    dsimp at hp hq
    simp [B]
    constructor <;> linarith
  refine ⟨B, ?_, fun x i j _ => (hb x i j).1, ?_⟩
  · apply Matrix.ext
    intro i j
    change (1/2:ℝ) • (P j i+P i j) + C (2*δ) = (1/2:ℝ) • (P i j+P j i) + C (2*δ)
    rw [add_comm (P j i) (P i j)]
  · intro x i
    have hsum : (∑ j, if i=j then 0 else eval x.val (B i j)) ≤
        (∑ j, if i=j then 0 else |eval x.val (R i j)|) + (k:ℝ)*(3*δ) := by
      calc
        _ ≤ ∑ j, ((if i=j then 0 else |eval x.val (R i j)|)+3*δ) := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs <;> linarith [(hb x i j).2]
        _ = _ := by simp [Finset.sum_add_distrib]
    have hg := hgap (x,i)
    dsimp [gap] at hg
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

/-- M4: every symmetric polynomial matrix strictly row diagonally dominant
on the real zero set has an exact finite rectangular Gram representation
modulo the ideal. This is not an approximation statement. -/
theorem IdealArchimedean.diagonally_dominant_gram [Fintype σ]
    (I : Ideal (MvPolynomial σ ℝ)) (hI : IdealArchimedean I)
    (R : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ)) (hR : R.IsSymm)
    (hdd : ∀ x : σ → ℝ, (∀ p ∈ I, eval x p = 0) → ∀ i,
      (∑ j, if i=j then 0 else |eval x (R i j)|) < eval x (R i i)) :
    ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin k) (MvPolynomial σ ℝ),
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ I := by
  let K := {x : σ → ℝ | ∀ p ∈ I, eval x p = 0}
  obtain ⟨B, hB, hoff, hdiag⟩ := exists_dd_polynomial_majorants K
    (hI.isCompact_realZeroSet I) R hR (fun x => hdd x.val x.property)
  exact hI.matrix_gram_of_majorants I R B hR hB
    (fun x hx => hoff ⟨x,hx⟩) (fun x hx => hdiag ⟨x,hx⟩)

/-- A uniform entrywise error around a positive scalar matrix is sufficient
for M4. This is the tolerance interface for the shifted M3 approximation. -/
theorem IdealArchimedean.near_scalar_gram [Fintype σ]
    (I : Ideal (MvPolynomial σ ℝ)) (hI : IdealArchimedean I)
    (R : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ)) (hR : R.IsSymm)
    {μ : ℝ} (hμ : 0 < μ)
    (hclose : ∀ x : σ → ℝ, (∀ p ∈ I, eval x p = 0) → ∀ i j,
      |eval x (R i j) - (if i=j then μ else 0)| < μ/(2*((k:ℝ)+1))) :
    ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin k) (MvPolynomial σ ℝ),
      ∀ i j, R i j - ∑ l, H l i * H l j ∈ I := by
  classical
  apply hI.diagonally_dominant_gram I R hR
  intro x hx i
  let ε := μ/(2*((k:ℝ)+1))
  have he : 0 < ε := by dsimp [ε]; positivity
  have hε : 2*((k:ℝ)+1)*ε = μ := by dsimp [ε]; field_simp
  have hd : -ε < eval x (R i i)-μ := by
    simpa [ε] using (abs_lt.mp (hclose x hx i i)).1
  have hs : (∑ j, if i=j then 0 else |eval x (R i j)|) ≤ (k:ℝ)*ε := by
    calc
      _ ≤ ∑ _j : Fin k, ε := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i=j
        · simp [hij, he.le]
        · exact (by simpa [hij, ε] using (hclose x hx i j).le)
      _ = _ := by simp
  nlinarith

end CZExposure.PolynomialGeometry
