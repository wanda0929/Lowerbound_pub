/-
Copyright (c) 2026 LowerBoundCZ authors.
Released under the repository license.
Authors: formalization of "Certifying the Rydberg-exposure limit of a
globally driven controlled-Z gate".
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Algebraic preliminaries

Coupling constants, the instantaneous exposure density, and a handful of
complex identities used throughout the formalization of
`main.tex` / `control-appendices.tex`.
-/

noncomputable section

namespace LowerBoundCZ

open Complex

/-- Sector coupling `κ_k = √k / 2` from Eq. (schrod) / Eq. (schrod_lab). -/
def kappa (k : ℕ) : ℝ := Real.sqrt (k : ℝ) / 2

lemma kappa_nonneg (k : ℕ) : 0 ≤ kappa k := by
  unfold kappa
  positivity

lemma kappa_pos {k : ℕ} (hk : 0 < k) : 0 < kappa k := by
  unfold kappa
  positivity

lemma kappa_sq (k : ℕ) : kappa k ^ 2 = (k : ℝ) / 4 := by
  unfold kappa
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

lemma two_mul_kappa (k : ℕ) : 2 * kappa k = Real.sqrt (k : ℝ) := by
  unfold kappa
  ring

lemma four_mul_kappa_sq (k : ℕ) : 4 * kappa k ^ 2 = (k : ℝ) := by
  rw [kappa_sq]
  ring

lemma kappa_one : kappa 1 = 1 / 2 := by
  unfold kappa
  simp [Real.sqrt_one]

lemma kappa_two : kappa 2 = Real.sqrt 2 / 2 := by
  unfold kappa
  norm_num

lemma kappa_two_eq_sqrt_two_mul_kappa_one : kappa 2 = Real.sqrt 2 * kappa 1 := by
  rw [kappa_one, kappa_two]
  ring

/-- Instantaneous input-averaged Rydberg exposure `c(x) = (2|r₁|² + |r₂|²)/4`. -/
def pointCost (r1 r2 : ℂ) : ℝ := (2 * normSq r1 + normSq r2) / 4

lemma pointCost_nonneg (r1 r2 : ℂ) : 0 ≤ pointCost r1 r2 := by
  unfold pointCost
  have h1 : 0 ≤ normSq r1 := normSq_nonneg _
  have h2 : 0 ≤ normSq r2 := normSq_nonneg _
  positivity

lemma pointCost_eq (r1 r2 : ℂ) :
    pointCost r1 r2 = (2 * normSq r1 + normSq r2) / 4 := rfl

/-- Ground-population coordinate `n_k = |g_k|²`. -/
abbrev groundPop (g : ℂ) : ℝ := normSq g

lemma groundPop_add_rydberg (g r : ℂ) (h : normSq g + normSq r = 1) :
    normSq r = 1 - groundPop g := by
  linarith

lemma re_star_mul (z w : ℂ) : (star z * w).re = z.re * w.re + z.im * w.im := by
  simp [mul_re]

lemma im_star_mul (z w : ℂ) : (star z * w).im = z.re * w.im - z.im * w.re := by
  simp [mul_im]
  ring

lemma re_neg_I_mul (z : ℂ) : (-I * z).re = z.im := by
  simp [neg_mul, mul_re, I_re, I_im]

lemma im_neg_I_mul (z : ℂ) : (-I * z).im = -z.re := by
  simp [neg_mul, mul_im, I_re, I_im]

lemma re_neg_I_mul_real (κ : ℝ) (z : ℂ) : (-I * κ * z).re = κ * z.im := by
  simp [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]

lemma normSq_neg_I (z : ℂ) : normSq (-I * z) = normSq z := by
  rw [normSq_mul, normSq_neg, normSq_I, one_mul]

lemma normSq_ofReal_mul (κ : ℝ) (z : ℂ) : normSq (κ * z) = κ ^ 2 * normSq z := by
  rw [normSq_mul, normSq_ofReal]
  ring

/-- Schrödinger velocity of the ground amplitude: `ġ = -i κ u r`. -/
def groundVel (k : ℕ) (u r : ℂ) : ℂ := -I * kappa k * u * r

/-- Schrödinger velocity of the Rydberg amplitude: `ṙ = -i κ ū g`. -/
def rydbergVel (k : ℕ) (u g : ℂ) : ℂ := -I * kappa k * star u * g

lemma groundVel_zero_ctrl (k : ℕ) (r : ℂ) : groundVel k 0 r = 0 := by
  unfold groundVel
  simp

lemma rydbergVel_zero_ctrl (k : ℕ) (g : ℂ) : rydbergVel k 0 g = 0 := by
  unfold rydbergVel
  simp

lemma pointCost_idle_left (r2 : ℂ) : pointCost 0 r2 = normSq r2 / 4 := by
  unfold pointCost
  simp

/-- The two-sector inner product that appears in `d/ds(|g|²+|r|²)` vanishes. -/
lemma re_norm_flux (k : ℕ) (g r u : ℂ) :
    (star g * groundVel k u r + star r * rydbergVel k u g).re = 0 := by
  unfold groundVel rydbergVel
  -- Direct expansion: the flux is `-I κ` times a self-adjoint (hence real) scalar.
  simp [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

lemma two_re_star_groundVel (k : ℕ) (g r u : ℂ) :
    2 * (star g * groundVel k u r).re
      = 2 * kappa k * (star g * u * r).im := by
  unfold groundVel
  have h : (star g * (-I * kappa k * u * r)).re
      = kappa k * (star g * u * r).im := by
    have := re_neg_I_mul_real (kappa k) (star g * u * r)
    -- rearrange associativity
    convert this using 2
    ring
  linarith

/-- Fiber triangle envelope `M(x,y)` from the companion-state argument. -/
def fiberEnvelope (x y : ℝ) : ℝ :=
  (1 - x) * Real.sqrt (1 - y) + Real.sqrt (2 * x * (1 - x) * y)

/-- Pointwise cost-to-speed density `h(x,y)` on the companion-state fiber. -/
def fiberDensity (x y : ℝ) : ℝ :=
  (Real.sqrt 2 / 4) * (2 / Real.sqrt y + Real.sqrt y / x)

/-- The five-cell exact dual target `293/100`. -/
def splitBound : ℚ := 293 / 100

/-- Exposure ceiling used to compactify competitive trajectories. -/
def exposureCeiling : ℚ := 2935887 / 1000000

/-- Published decimal form of the interval-certified upper endpoint. -/
def upperEndpoint : ℝ := 2.935875225844105

lemma splitBound_lt_ceiling : (splitBound : ℝ) < (exposureCeiling : ℝ) := by
  unfold splitBound exposureCeiling
  norm_num

lemma splitBound_lt_upper : (splitBound : ℝ) < upperEndpoint := by
  unfold splitBound upperEndpoint
  norm_num

end LowerBoundCZ
