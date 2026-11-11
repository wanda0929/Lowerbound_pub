/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Companion-state fiber bound and Schmidt closed form
-/

noncomputable section

namespace LowerBoundCZ

open MeasureTheory

/-- Abstract fiber envelope, Eq. (c_fib_def). -/
def cFib (r : ℝ) : ℝ :=
  sInf { t | ∃ x y : ℝ, 0 < x ∧ x ≤ 1 ∧ 0 < y ∧ y ≤ 1 ∧
    r ≤ fiberEnvelope x y ∧ t = fiberDensity x y }

/-- Pointwise cost-to-speed comparison, Eq. (fiber_pointwise),
written in multiplied form to avoid division-ring bookkeeping. -/
lemma fiber_pointwise {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((2 * x + y) / 4) * Real.sqrt 2
      = fiberDensity x y * (x * Real.sqrt y) := by
  unfold fiberDensity
  have hy0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  field_simp [hx.ne', hy0.ne', hy2]
  rw [hy2]

lemma fiberDensity_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ fiberDensity x y := by
  unfold fiberDensity
  have hy0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  positivity

/-- The sharp speed bound `|q'| ≤ x √y / √2` saturates `c = h · (max |q'|)`. -/
lemma fiber_density_saturates {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    fiberDensity x y * (x * Real.sqrt y / Real.sqrt 2) = (2 * x + y) / 4 := by
  have h := fiber_pointwise hx hy
  have h2 : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2)).ne'
  field_simp [h2] at h ⊢
  linarith [h]

/-- Eq. (fiber_pointwise): `c / |q'| ≥ h(x,y)` whenever `|q'|` is at most
the companion-state speed. -/
lemma fiber_pointwise_ratio {x y qdot : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hspd : |qdot| ≤ x * Real.sqrt y / Real.sqrt 2) :
    fiberDensity x y * |qdot| ≤ (2 * x + y) / 4 := by
  have hden : 0 ≤ fiberDensity x y := fiberDensity_nonneg hx hy
  have hsat := fiber_density_saturates hx hy
  have hspd' : 0 ≤ x * Real.sqrt y / Real.sqrt 2 := by
    have : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
    positivity
  calc
    fiberDensity x y * |qdot|
        ≤ fiberDensity x y * (x * Real.sqrt y / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hspd hden
    _ = (2 * x + y) / 4 := hsat

lemma abs_overlap_le_moduli (g1 r1 g2 r2 : ℂ) :
    ‖star g2 * g1 ^ 2 + Real.sqrt 2 * star r2 * g1 * r1‖
      ≤ ‖g2‖ * ‖g1‖ ^ 2
        + Real.sqrt 2 * ‖r2‖ * ‖g1‖ * ‖r1‖ := by
  refine (norm_add_le _ _).trans_eq ?_
  have hA : ‖star g2 * g1 ^ 2‖ = ‖g2‖ * ‖g1‖ ^ 2 := by
    simp [norm_pow]
  have hB : ‖(Real.sqrt 2 : ℂ) * star r2 * g1 * r1‖
      = Real.sqrt 2 * ‖r2‖ * ‖g1‖ * ‖r1‖ := by
    simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))]
  rw [hA, hB]

/-- Even integrand identity used by the area formula in Theorem fiber. -/
lemma even_abs_integral {f : ℝ → ℝ}
    (hf0 : IntervalIntegrable (fun r => f |r|) volume (-1) 0)
    (hf1 : IntervalIntegrable (fun r => f |r|) volume 0 1)
    (hsubst : (∫ r in (-1 : ℝ)..(0 : ℝ), f |r|) = ∫ r in (0 : ℝ)..(1 : ℝ), f r)
    (hpos : (∫ r in (0 : ℝ)..(1 : ℝ), f |r|) = ∫ r in (0 : ℝ)..(1 : ℝ), f r) :
    (∫ r in (-1 : ℝ)..(1 : ℝ), f |r|)
      = 2 * ∫ r in (0 : ℝ)..(1 : ℝ), f r := by
  have hsum :=
    intervalIntegral.integral_add_adjacent_intervals hf0 hf1
  rw [← hsum, hsubst, hpos]
  ring

/-- Algebraic evaluation of the Schmidt integral, Eq. (schmidt_bound). -/
lemma schmidt_algebra
    {I : ℝ} (hlog : Real.log 2 ≠ 0)
    (hI : I =
      (8 / 3) * (1 - 1 / (2 * Real.sqrt 2)) / Real.log 2
        + 2 * (1 - 1 / Real.sqrt 2) / Real.log 2) :
    (Real.log 2 / Real.sqrt 2) * I = (7 * Real.sqrt 2 - 5) / 3 := by
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2)).ne'
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  rw [hI]
  field_simp [hlog, hsqrt, hsq]
  rw [hsq]
  ring

/-- Primitive of the Schmidt integrand `4 · 2^{-3s/2} + 2^{-s/2}`. -/
lemma schmidt_indefinite_eval
    (hlog : Real.log 2 ≠ 0) :
    let I :=
      (8 / 3) * (1 - 1 / (2 * Real.sqrt 2)) / Real.log 2
        + 2 * (1 - 1 / Real.sqrt 2) / Real.log 2
    (Real.log 2 / Real.sqrt 2) * I = (7 * Real.sqrt 2 - 5) / 3 :=
  schmidt_algebra hlog rfl

end LowerBoundCZ
