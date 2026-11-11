module
public import RequestProject.AppendixE.SOSOrderBounds
public import Mathlib.Analysis.Convex.Cone.Extension

/-! Algebraic separation of the Archimedean SOS cone. No closedness of the
cone is assumed: the separating functional is obtained by Riesz extension. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry

variable {A : Type*} [CommRing A] [Algebra ℝ A]

theorem sumSq_smul {a : A} (ha : IsSumSq a) {r : ℝ} (hr : 0 ≤ r) :
    IsSumSq (r • a) := by
  rw [Algebra.smul_def]
  exact (isSumSq_algebraMap_of_nonneg hr).mul ha

/-- Adjoin the negative of the element to be separated, as a convex cone,
not as a multiplicatively closed preordering. -/
def sosSeparatingCone (a : A) : ConvexCone ℝ A where
  carrier := {x | ∃ s : A, ∃ t : ℝ, IsSumSq s ∧ 0 ≤ t ∧ x = s - t • a}
  smul_mem' r hr x hx := by
    obtain ⟨s, t, hs, ht, rfl⟩ := hx
    exact ⟨r • s, r*t, sumSq_smul hs hr.le, mul_nonneg hr.le ht,
      by rw [smul_sub, smul_smul]⟩
  add_mem' x hx y hy := by
    obtain ⟨s, t, hs, ht, rfl⟩ := hx
    obtain ⟨u, v, hu, hv, rfl⟩ := hy
    exact ⟨s+u, t+v, hs.add hu, add_nonneg ht hv, by rw [add_smul]; abel⟩

theorem mem_sosSeparatingCone {a x : A} (hx : IsSumSq x) :
    x ∈ sosSeparatingCone a := ⟨x, 0, hx, le_rfl, by simp⟩

theorem neg_one_notMem_sosSeparatingCone
    (hb : ∀ x : A, ∃ N : ℕ, IsSumSq ((N:A)+x) ∧ IsSumSq ((N:A)-x))
    {a : A} (ha : ¬ IsSumSq a) : (-1:A) ∉ sosSeparatingCone a := by
  have hn : ¬ IsSumSq (-1:A) := by
    intro h
    obtain ⟨N, hp, _⟩ := hb a
    have hneg : IsSumSq (-(N:A)) := by simpa using (IsSumSq.natCast N).mul h
    exact ha (by convert hp.add hneg using 1; ring)
  rintro ⟨s, t, hs, ht, he⟩
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp only [zero_smul, sub_zero] at he
    exact hn (he ▸ hs)
  · have he' : t • a = s+1 := by linear_combination he
    have h := sumSq_smul (hs.add (IsSumSq.natCast 1)) (inv_nonneg.mpr ht.le)
    have he'' : t⁻¹ • (s+1) = a := by
      rw [← he', smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    exact ha (he'' ▸ (by simpa only [Nat.cast_one] using h))

/-- A normalized real linear functional separates every nonmember of an
Archimedean SOS cone. Its positivity holds on finite sums of squares. -/
theorem exists_sos_separating_state
    (hb : ∀ x : A, ∃ N : ℕ, IsSumSq ((N:A)+x) ∧ IsSumSq ((N:A)-x))
    {a : A} (ha : ¬ IsSumSq a) :
    ∃ L : A →ₗ[ℝ] ℝ, L 1 = 1 ∧ (∀ x, IsSumSq x → 0 ≤ L x) ∧ L a ≤ 0 := by
  have h10 : (1:A) ≠ 0 := by
    intro h
    have hz : a = 0 := by calc
      a = a*1 := (mul_one a).symm
      _ = 0 := by rw [h, mul_zero]
    exact ha (hz ▸ IsSumSq.zero)
  let e := LinearEquiv.toSpanNonzeroSingleton ℝ A 1 h10
  let f : A →ₗ.[ℝ] ℝ := ⟨Submodule.span ℝ {1}, e.symm.toLinearMap⟩
  have hn := neg_one_notMem_sosSeparatingCone hb ha
  have hscalar (r : ℝ) (hr : r • (1:A) ∈ sosSeparatingCone a) : 0 ≤ r := by
    by_contra h
    have hrneg : r < 0 := lt_of_not_ge h
    have hc := (sosSeparatingCone a).smul_mem
      (show 0 < -r⁻¹ by rw [← inv_neg]; exact inv_pos.mpr (neg_pos.mpr hrneg)) hr
    have he : (-r⁻¹) • (r • (1:A)) = -1 := by
      rw [smul_smul, neg_mul, inv_mul_cancel₀ hrneg.ne, neg_one_smul]
    exact hn (he ▸ hc)
  obtain ⟨L, hL, hpos⟩ := riesz_extension (sosSeparatingCone a) f
    (fun x hx => hscalar (e.symm x) (by
      rwa [LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul])) (by
      intro y
      obtain ⟨N, hN, _⟩ := hb y
      refine ⟨e (N:ℝ), ?_⟩
      change (N:ℝ) • (1:A) + y ∈ sosSeparatingCone a
      simpa [Algebra.smul_def] using mem_sosSeparatingCone (a := a) hN)
  refine ⟨L, ?_, fun x hx => hpos x (mem_sosSeparatingCone hx), ?_⟩
  · have h := hL (e 1)
    change L (e 1) = e.symm (e 1) at h
    rw [e.symm_apply_apply] at h
    simpa [e] using h
  · have h := hpos (-a) ⟨0, 1, IsSumSq.zero, zero_le_one, by simp⟩
    simpa using h

end CZExposure.PolynomialGeometry
