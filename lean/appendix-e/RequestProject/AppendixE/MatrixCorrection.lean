module

public import RequestProject.AppendixE.RotationAverage

/-!
# The residual-preserving matrix correction

The correction `|r|² I - r rᵀ` is polynomial, annihilates `r`, and is
positive semidefinite over the reals. These facts hold even at `r = 0`.
This module does not assume that a positive scalar quadratic form makes
its representing matrix positive definite.
-/

@[expose] public section
noncomputable section

namespace CZExposure.MatrixCorrection

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Algebra

variable {R : Type*} [CommRing R]

def correction (r : n → R) : Matrix n n R :=
  (r ⬝ᵥ r) • (1 : Matrix n n R) - vecMulVec r r

def corrected (A : Matrix n n R) (r : n → R) (Λ : R) : Matrix n n R :=
  A + Λ • correction r

theorem correction_mulVec (r v : n → R) :
    correction r *ᵥ v = (r ⬝ᵥ r) • v - (r ⬝ᵥ v) • r := by
  simp [correction, sub_mulVec, smul_mulVec, vecMulVec_mulVec]

theorem correction_annihilates (r : n → R) : correction r *ᵥ r = 0 := by
  simp [correction_mulVec]

theorem corrected_radial (A : Matrix n n R) (r : n → R) (Λ : R) :
    corrected A r Λ *ᵥ r = A *ᵥ r := by
  simp [corrected, add_mulVec, smul_mulVec, correction_annihilates]

theorem corrected_residual (A : Matrix n n R) (r : n → R) (Λ : R) :
    r ⬝ᵥ (corrected A r Λ *ᵥ r) = r ⬝ᵥ (A *ᵥ r) := by
  rw [corrected_radial]

theorem correction_quadratic (r v : n → R) :
    v ⬝ᵥ (correction r *ᵥ v) = (r ⬝ᵥ r) * (v ⬝ᵥ v) - (r ⬝ᵥ v)^2 := by
  rw [correction_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_smul,
    dotProduct_comm v r]
  simp [smul_eq_mul, pow_two]

theorem correction_perpendicular (r v : n → R) (h : r ⬝ᵥ v = 0) :
    correction r *ᵥ v = (r ⬝ᵥ r) • v := by
  simp [correction_mulVec, h]

theorem correction_symmetric (r : n → R) : (correction r).IsSymm := by
  ext i j
  simp [correction, Matrix.transpose_apply, Matrix.one_apply, vecMulVec, eq_comm, mul_comm]

end Algebra

theorem correction_nonneg (r v : n → ℝ) : 0 ≤ v ⬝ᵥ (correction r *ᵥ v) := by
  rw [correction_quadratic]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r v
  simpa [dotProduct, pow_two] using sub_nonneg.mpr h

theorem correction_posSemidef (r : n → ℝ) : (correction r).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa [Matrix.IsHermitian, conjTranspose] using correction_symmetric r
  · intro v
    simpa using correction_nonneg r v

/-- Adding the correction cannot destroy positivity near the zero-cost face. -/
theorem corrected_posDef_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    (r : n → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : (corrected A r Λ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact hA.1.add ((correction_posSemidef r).smul hΛ).1
  · intro v hv
    have ha := hA.dotProduct_mulVec_pos hv
    have hc := mul_nonneg hΛ (correction_nonneg r v)
    simpa [corrected, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul] using add_pos_of_pos_of_nonneg ha hc

/-- Away from `r = 0`, the only unpenalized vectors are radial. -/
theorem correction_zero_iff {r v : n → ℝ} (hr : r ≠ 0) :
    v ⬝ᵥ (correction r *ᵥ v) = 0 ↔ ∃ t : ℝ, v = t • r := by
  constructor
  · intro h
    rw [correction_quadratic] at h
    have hrr : r ⬝ᵥ r ≠ 0 := by simpa using hr
    have hw : ((r ⬝ᵥ r) • v - (r ⬝ᵥ v) • r) ⬝ᵥ
        ((r ⬝ᵥ r) • v - (r ⬝ᵥ v) • r) = 0 := by
      calc _ = (r ⬝ᵥ r) * ((r ⬝ᵥ r) * (v ⬝ᵥ v) - (r ⬝ᵥ v)^2) := by
             simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul,
               smul_dotProduct, smul_eq_mul, dotProduct_comm v r]
             ring
           _ = 0 := by rw [h, mul_zero]
    have he := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hw)
    refine ⟨(r ⬝ᵥ v) / (r ⬝ᵥ r), ?_⟩
    ext i
    have hi := congrFun he i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    apply (mul_left_cancel₀ hrr)
    rw [hi]
    field_simp
  · rintro ⟨t, rfl⟩
    simp [mulVec_smul, correction_annihilates]

/-- Compactness turns pointwise positivity on the zero set of a nonnegative
penalty into one uniform nonnegative coefficient. No matrix positivity theorem
is used here. -/
theorem exists_uniform_penalty {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ x ∈ K, 0 ≤ g x)
    (hzero : ∀ x ∈ K, g x = 0 → 0 < f x) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, 0 < f x + Λ * g x := by
  classical
  let U : ℕ → Set X := fun m => {x | 0 < f x + (m : ℝ) * g x}
  have ho : ∀ m, IsOpen (U m) := fun m =>
    isOpen_lt continuous_const (hf.add (continuous_const.mul hg))
  have hc : K ⊆ ⋃ m, U m := by
    intro x hx
    by_cases hz : g x = 0
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [U] using hzero x hx hz⟩
    · have hp := lt_of_le_of_ne (hg0 x hx) (Ne.symm hz)
      obtain ⟨m, hm⟩ := exists_nat_gt (-f x / g x)
      have hm' := (div_lt_iff₀ hp).mp hm
      exact Set.mem_iUnion.mpr ⟨m, by dsimp [U]; linarith⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U ho hc
  refine ⟨(s.sup id : ℕ), Nat.cast_nonneg _, ?_⟩
  intro x hx
  obtain ⟨m, hm, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
  have hm' : (m : ℝ) ≤ (s.sup id : ℕ) := by
    exact_mod_cast (Finset.le_sup (f := id) hm)
  have hmono := mul_le_mul_of_nonneg_right hm' (hg0 x hx)
  change 0 < f x + (m : ℝ) * g x at hxU
  linarith

/-- One coefficient works throughout a compact domain. Positivity on the
zero-amplitude face and in the radial direction off that face suffice;
no positivity of the other directions of `A` is assumed. -/
theorem exists_corrected_posDef {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {A : X → Matrix n n ℝ} {r : X → n → ℝ}
    (hA : Continuous A) (hr : Continuous r)
    (hsym : ∀ x ∈ K, (A x).IsHermitian)
    (hface : ∀ x ∈ K, r x = 0 → (A x).PosDef)
    (hrad : ∀ x ∈ K, r x ≠ 0 → 0 < r x ⬝ᵥ (A x *ᵥ r x)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, (corrected (A x) (r x) Λ).PosDef := by
  let f : X × (n → ℝ) → ℝ := fun p => p.2 ⬝ᵥ (A p.1 *ᵥ p.2)
  let g : X × (n → ℝ) → ℝ := fun p => p.2 ⬝ᵥ (correction (r p.1) *ᵥ p.2)
  have hf : Continuous f := by
    dsimp [f, dotProduct, mulVec]
    fun_prop
  have hg : Continuous g := by
    dsimp [g, correction, dotProduct, mulVec, vecMulVec]
    fun_prop
  have hz : ∀ p ∈ K ×ˢ Metric.sphere (0 : n → ℝ) 1, g p = 0 → 0 < f p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ hg0
    have hv0 : v ≠ 0 := by
      intro he
      simp [he] at hv
    by_cases hr0 : r x = 0
    · simpa [f] using (hface x hx hr0).dotProduct_mulVec_pos hv0
    · obtain ⟨t, ht⟩ := (correction_zero_iff hr0).mp hg0
      change v = t • r x at ht
      have ht0 : t ≠ 0 := by
        intro he
        apply hv0
        simpa [he] using ht
      have hpos := mul_pos (sq_pos_of_ne_zero ht0) (hrad x hx hr0)
      dsimp [f]
      rw [ht]
      simpa [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        pow_two, mul_assoc] using hpos
  obtain ⟨Λ, hΛ, hpos⟩ := exists_uniform_penalty
    (hK.prod (isCompact_sphere (0 : n → ℝ) 1)) hf hg
    (fun p _ => correction_nonneg (r p.1) p.2) hz
  refine ⟨Λ, hΛ, fun x hx => ?_⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (hsym x hx).add ((correction_posSemidef (r x)).smul hΛ).1
  · intro v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : n → ℝ) 1 := by
      simp [norm_smul, ne_of_gt hn]
    have hp := hpos (x, ‖v‖⁻¹ • v) ⟨hx, hu⟩
    have he : f (x, ‖v‖⁻¹ • v) + Λ * g (x, ‖v‖⁻¹ • v) =
        ‖v‖⁻¹ ^ 2 * (v ⬝ᵥ (corrected (A x) (r x) Λ *ᵥ v)) := by
      simp only [f, g, corrected, mulVec_smul, smul_dotProduct, dotProduct_smul,
        add_mulVec, smul_mulVec, dotProduct_add, smul_eq_mul]
      ring
    rw [he] at hp
    simpa using (pos_of_mul_pos_right hp (sq_nonneg _))

end CZExposure.MatrixCorrection
