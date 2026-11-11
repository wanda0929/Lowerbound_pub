import LowerBoundCZ.SlackData
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.IntervalCases

/-! Endpoint-polynomial arithmetic for the pinned strengthened bound.
These results alone do not establish any trajectory's accumulated slack. -/
noncomputable section
namespace LowerBoundCZ.Certification.Slack
open Polynomial Finset
open scoped unitInterval

def bernsteinSum (n : ℕ) (a : Fin (n+1) → ℚ) : ℚ[X] :=
  ∑ i, C (a i) * bernsteinPolynomial ℚ n i

theorem bernsteinSum_eval (n : ℕ) (a : Fin (n+1) → ℚ) (t : unitInterval) :
    (bernsteinSum n a).eval₂ (Rat.castHom ℝ) t =
      ∑ i, (a i : ℝ) * bernstein n i t := by
  simp [bernsteinSum, eval₂_finset_sum, bernsteinPolynomial, bernstein_apply, eval₂_pow]

theorem bernsteinSum_pos (n : ℕ) (a : Fin (n+1) → ℚ)
    (ha : ∀ i, 0 < a i) (t : unitInterval) :
    0 < (bernsteinSum n a).eval₂ (Rat.castHom ℝ) t := by
  rw [bernsteinSum_eval]
  have hw : 0 < ∑ i : Fin (n+1), bernstein n i t := by
    rw [bernstein.probability]; norm_num
  obtain ⟨i, hi, hp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun _ _ => bernstein_nonneg)).mp hw
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Rat.cast_nonneg.mpr (ha j).le) bernstein_nonneg
  · exact ⟨i, hi, mul_pos (Rat.cast_pos.mpr (ha i)) hp⟩

def base : ℚ := 5861/2000
def endpoint : ℚ[X] := bernsteinSum 13 SlackData.endpoint
def parentEndpoint : ℚ[X] := bernsteinSum 13 SlackData.parentEndpoint
def ratio : ℚ := (SlackData.bound - base) / (SlackData.parentBound - base)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem endpoint_coefficients_pos : ∀ i, 0 < SlackData.endpoint i := by
  intro i
  fin_cases i <;> norm_num [SlackData.endpoint]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Exact equality of rational polynomials, not positivity inferred from samples. -/
theorem endpoint_composition : endpoint =
    parentEndpoint.comp (C ratio * X) + C SlackData.gain -
      C (SlackData.bound - SlackData.parentBound) := by
  unfold endpoint parentEndpoint bernsteinSum
  simp only [Fin.sum_univ_succ]
  norm_num [bernsteinPolynomial, SlackData.endpoint, SlackData.parentEndpoint,
    SlackData.gain, ratio, SlackData.bound, SlackData.parentBound, base,
    Nat.choose, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp]
  ring_nf
  simp only [← Polynomial.C_pow]
  ext n
  by_cases hn : n ≤ 13
  · interval_cases n <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_C, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  · have hn' : 13 < n := by omega
    have hne : ∀ k ≤ 13, k ≠ n := by omega
    have hne' : ∀ k ≤ 13, n ≠ k := by omega
    simp (disch := omega) only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_C,
      ← Polynomial.C_pow, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_natCast, Polynomial.coeff_mul_ofNat,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_neg, hne, hne', if_false, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero]

theorem endpoint_pos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < endpoint.eval₂ (Rat.castHom ℝ) t :=
  bernsteinSum_pos 13 SlackData.endpoint endpoint_coefficients_pos ⟨t, ht⟩

theorem bound_values : (base : ℝ) = 2.9305 ∧
    (SlackData.bound : ℝ) = 2.931287735220 ∧
    (SlackData.bound : ℝ) < 733/250 := by
  norm_num [base, SlackData.bound]

/-- The final contradiction step. The scalar inequality must come from the
proved integral slack decomposition and credited profiles, not an external
trajectory-bound hypothesis in a certificate interface. -/
theorem endpoint_excludes {C : ℝ} (hL : (base : ℝ) ≤ C)
    (hB : C ≤ (SlackData.bound : ℝ))
    (hslack : (SlackData.bound : ℝ) - base +
      endpoint.eval₂ (Rat.castHom ℝ) ((C-base)/(SlackData.bound-base)) ≤ C-base) : False := by
  have hgap : (0 : ℝ) < SlackData.bound - base := by
    norm_num [SlackData.bound, base]
  have ht : (C-base)/(SlackData.bound-base) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hL) hgap.le,
      (div_le_one hgap).mpr (sub_le_sub_right hB _)⟩
  have hp := endpoint_pos _ ht
  linarith

end LowerBoundCZ.Certification.Slack
