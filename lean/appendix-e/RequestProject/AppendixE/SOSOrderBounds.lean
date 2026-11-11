module
public import RequestProject.AppendixE.MatrixSOSInput
public import Mathlib.Algebra.Ring.SumsOfSquares

/-! Archimedean order bounds in the polynomial quotient's actual sum-of-squares cone.
No partial-order instance is imposed: this cone need not be pointed. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry
open MvPolynomial

section Algebra
variable {A : Type*} [CommRing A] [Algebra ℝ A]

theorem isSumSq_algebraMap_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    IsSumSq (algebraMap ℝ A r) := by
  have he : algebraMap ℝ A r = algebraMap ℝ A (Real.sqrt r) * algebraMap ℝ A (Real.sqrt r) := by
    rw [← map_mul, Real.mul_self_sqrt hr]
  rw [he]
  exact IsSumSq.mul_self _

/-- A natural constant bounds the square, in the SOS cone rather than pointwise. -/
def SOSSquareBounded (a : A) : Prop := ∃ N : ℕ, IsSumSq ((N : A) - a^2)

theorem SOSSquareBounded.scalar (r : ℝ) : SOSSquareBounded (algebraMap ℝ A r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (r^2)
  refine ⟨N, ?_⟩
  have h := isSumSq_algebraMap_of_nonneg (A := A) (sub_nonneg.mpr hN)
  simpa using h

omit [Algebra ℝ A] in
theorem SOSSquareBounded.add {a b : A} (ha : SOSSquareBounded a) (hb : SOSSquareBounded b) :
    SOSSquareBounded (a+b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  refine ⟨2*N+2*M, ?_⟩
  have h := ((IsSumSq.natCast 2).mul hN).add
    (((IsSumSq.natCast 2).mul hM).add (IsSumSq.mul_self (a-b)))
  convert h using 1
  push_cast
  ring

omit [Algebra ℝ A] in
theorem SOSSquareBounded.mul {a b : A} (ha : SOSSquareBounded a) (hb : SOSSquareBounded b) :
    SOSSquareBounded (a*b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  refine ⟨N*M, ?_⟩
  have h := ((IsSumSq.natCast M).mul hN).add ((IsSumSq.mul_self a).mul hM)
  convert h using 1
  push_cast
  ring

/-- The same natural bound works with both signs. -/
theorem SOSSquareBounded.order_bounds {a : A} (ha : SOSSquareBounded a) :
    ∃ N : ℕ, IsSumSq ((N : A)+a) ∧ IsSumSq ((N : A)-a) := by
  obtain ⟨N, hN⟩ := ha
  have hq := isSumSq_algebraMap_of_nonneg (A := A) (by norm_num : (0:ℝ) ≤ 3/4)
  have he (b : A) : (b + algebraMap ℝ A (1/2))^2 =
      b^2 + b + algebraMap ℝ A (1/4) := by
    have hhalf : (2:A) * algebraMap ℝ A (1/2) = 1 := by
      have h := congrArg (algebraMap ℝ A) (show (2:ℝ)*(1/2) = 1 by norm_num)
      simpa only [map_mul, map_ofNat, map_one] using h
    have hquarter : algebraMap ℝ A (1/2) ^ 2 = algebraMap ℝ A (1/4) := by
      rw [← map_pow]; norm_num
    linear_combination b * hhalf + hquarter
  have hc : algebraMap ℝ A (1/4) + algebraMap ℝ A (3/4) = 1 := by
    rw [← map_add]; norm_num
  refine ⟨N+1, ?_, ?_⟩
  · have h := hN.add ((IsSumSq.mul_self (a + algebraMap ℝ A (1/2))).add hq)
    rw [← pow_two, he] at h
    convert h using 1
    push_cast
    linear_combination -hc
  · have h := hN.add ((IsSumSq.mul_self (-a + algebraMap ℝ A (1/2))).add hq)
    rw [← pow_two, he] at h
    convert h using 1
    push_cast
    linear_combination -hc

end Algebra

variable {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℝ))

omit [Fintype σ] in
theorem IsSOS.quotient_sumSq {d : ℕ} {s : MvPolynomial σ ℝ} (hs : CZExposure.IsSOS d s) :
    IsSumSq (Ideal.Quotient.mk I s) := by
  obtain ⟨m, f, _, rfl⟩ := hs
  simpa only [map_sum, map_pow] using
    IsSumSq.sum_sq Finset.univ (fun l : Fin m => Ideal.Quotient.mk I (f l))

theorem IdealArchimedean.variable_square_bounded (hI : IdealArchimedean I) (i : σ) :
    SOSSquareBounded (Ideal.Quotient.mk I (X i)) := by
  classical
  obtain ⟨N, d, s, hs, hi⟩ := hI
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
  rw [map_sub, map_sub, map_sum] at hz
  have he : (N : (MvPolynomial σ ℝ) ⧸ I) -
      ∑ j : σ, (Ideal.Quotient.mk I (X j))^2 = Ideal.Quotient.mk I s := by
    simpa using sub_eq_zero.mp hz
  refine ⟨N, ?_⟩
  have h := (IsSOS.quotient_sumSq I hs).add
    (IsSumSq.sum_sq (Finset.univ.erase i) (fun j => Ideal.Quotient.mk I (X j)))
  rw [← he] at h
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j => (Ideal.Quotient.mk I (X j))^2) (Finset.mem_univ i)
  convert h using 1
  linear_combination -hsum

/-- The coordinate Archimedean witness bounds every polynomial's square. -/
theorem IdealArchimedean.polynomial_square_bounded (hI : IdealArchimedean I)
    (p : MvPolynomial σ ℝ) : SOSSquareBounded (Ideal.Quotient.mk I p) := by
  induction p using MvPolynomial.induction_on with
  | C r => exact SOSSquareBounded.scalar r
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hI.variable_square_bounded I i)

/-- M1: every quotient element is order-bounded by one natural constant in
both directions, with finite sums of squares and no closure operation. -/
theorem IdealArchimedean.quotient_order_bounds (hI : IdealArchimedean I)
    (a : (MvPolynomial σ ℝ) ⧸ I) :
    ∃ N : ℕ, IsSumSq ((N : (MvPolynomial σ ℝ) ⧸ I)+a) ∧
      IsSumSq ((N : (MvPolynomial σ ℝ) ⧸ I)-a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (hI.polynomial_square_bounded I p).order_bounds

private theorem sumSq_finite {A : Type*} [CommRing A] {a : A} (h : IsSumSq a) :
    ∃ m : ℕ, ∃ f : Fin m → A, a = ∑ l, (f l)^2 := by
  induction h with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | sq_add a hs ih =>
    obtain ⟨m, f, hf⟩ := ih
    exact ⟨m+1, Fin.cons a f, by simp [Fin.sum_univ_succ, hf, pow_two]⟩

omit [Fintype σ] in
/-- Quotient SOS membership is exactly a finite, degree-bounded project
certificate modulo the ideal, not merely positivity on its real zero set. -/
theorem isSumSq_quotient_iff (p : MvPolynomial σ ℝ) :
    IsSumSq (Ideal.Quotient.mk I p) ↔
      ∃ d s, CZExposure.IsSOS d s ∧ p-s ∈ I := by
  constructor
  · intro h
    obtain ⟨m, g, hg⟩ := sumSq_finite h
    choose f hf using (fun l : Fin m => Ideal.Quotient.mk_surjective (g l))
    refine ⟨∑ l, (f l).totalDegree, ∑ l, (f l)^2, ⟨m, f, ?_, rfl⟩, ?_⟩
    · intro l
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (f j).totalDegree) (Finset.mem_univ l)
    · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simpa only [map_sum, map_pow, hf] using hg
  · rintro ⟨d, s, hs, hi⟩
    rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hi]
    exact IsSOS.quotient_sumSq I hs

/-- Polynomial representatives of the two order bounds, in the existing IsSOS format. -/
theorem IdealArchimedean.polynomial_order_certificates (hI : IdealArchimedean I)
    (p : MvPolynomial σ ℝ) :
    ∃ (N dp dm : ℕ) (sp sm : MvPolynomial σ ℝ),
      CZExposure.IsSOS dp sp ∧ CZExposure.IsSOS dm sm ∧
      C (N : ℝ)+p-sp ∈ I ∧ C (N : ℝ)-p-sm ∈ I := by
  obtain ⟨N, hp, hm⟩ := hI.quotient_order_bounds I (Ideal.Quotient.mk I p)
  obtain ⟨dp, sp, hsp, hip⟩ := (isSumSq_quotient_iff I (C (N : ℝ)+p)).mp (by simpa using hp)
  obtain ⟨dm, sm, hsm, him⟩ := (isSumSq_quotient_iff I (C (N : ℝ)-p)).mp (by simpa using hm)
  exact ⟨N, dp, dm, sp, sm, hsp, hsm, hip, him⟩

end CZExposure.PolynomialGeometry
