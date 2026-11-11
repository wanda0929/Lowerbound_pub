/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Dynamics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact control reductions

Lemmas `bang`, `master`, `osc`, `mu`, and `ratio` from `main.tex` §II.B
and `control-appendices.tex` §A.
-/

noncomputable section

namespace LowerBoundCZ

open Complex MeasureTheory

/-! ## Lemma bang (maximum-amplitude reduction) -/

lemma bang_cost_le_lab (tr : LabTrajectory)
    (hint : IntervalIntegrable (fun τ => pointCost (tr.r1 τ) (tr.r2 τ)) volume 0 tr.τf)
    (hintr : IntervalIntegrable
      (fun τ => pointCost (tr.r1 τ) (tr.r2 τ) * tr.ρ τ) volume 0 tr.τf) :
    tr.bangCost ≤ tr.exposure := by
  unfold LabTrajectory.bangCost LabTrajectory.exposure
  apply intervalIntegral.integral_mono_on tr.hτ.le hintr hint
  intro τ hτ
  exact pointCost_mul_rho_le (tr.r1 τ) (tr.r2 τ) (tr.hρ τ hτ).1 (tr.hρ τ hτ).2

lemma lemma_bang_infima {Lab Bang : Set ℝ}
    (hLab : Lab.Nonempty) (hBang : Bang.Nonempty)
    (hLabBdd : BddBelow Lab) (hBangBdd : BddBelow Bang)
    (hsubset : Bang ⊆ Lab)
    (hcompress : ∀ C ∈ Lab, ∃ C' ∈ Bang, C' ≤ C) :
    sInf Lab = sInf Bang :=
  sInf_eq_of_compression hLab hBang hBangBdd hLabBdd hsubset hcompress

/-! ## Lemma master (metric line element) -/

lemma master_geom (k : ℕ) (n ndot Φdot β : ℝ)
    (hn : 0 < n) (hn1 : n ≤ 1)
    (hndot : ndot = Real.sqrt (k : ℝ) * Real.sqrt (n * (1 - n)) * Real.sin β)
    (hΦdot : Φdot =
      -(Real.sqrt (k : ℝ) / 2) * Real.sqrt ((1 - n) / n) * Real.cos β) :
    ndot ^ 2 + 4 * n ^ 2 * Φdot ^ 2 = (k : ℝ) * n * (1 - n) := by
  have hnn : 0 ≤ n * (1 - n) := mul_nonneg hn.le (sub_nonneg.mpr hn1)
  have hquot : 0 ≤ (1 - n) / n := div_nonneg (sub_nonneg.mpr hn1) hn.le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hndot' : ndot ^ 2 = (k : ℝ) * (n * (1 - n)) * Real.sin β ^ 2 := by
    rw [hndot, mul_pow, mul_pow, Real.sq_sqrt hk, Real.sq_sqrt hnn]
  have hΦdot' : 4 * n ^ 2 * Φdot ^ 2 = (k : ℝ) * n * (1 - n) * Real.cos β ^ 2 := by
    rw [hΦdot]
    have : (-(Real.sqrt (k : ℝ) / 2) * Real.sqrt ((1 - n) / n) * Real.cos β) ^ 2
        = (Real.sqrt (k : ℝ) / 2) ^ 2 * Real.sqrt ((1 - n) / n) ^ 2 * Real.cos β ^ 2 := by
      ring
    rw [this, div_pow, Real.sq_sqrt hk, Real.sq_sqrt hquot]
    field_simp [hn.ne']
    ring
  rw [hndot', hΦdot']
  have : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  linear_combination (n * (1 - n) * (k : ℝ)) * this

/-- Polar ground-population speed, first display in the proof of Lemma master. -/
lemma polar_ndot (k : ℕ) (g r u : ℂ) {β : ℝ}
    (hβ : (star g * u * r).im = ‖g‖ * ‖r‖ * Real.sin β) :
    2 * (star g * groundVel k u r).re
      = Real.sqrt (k : ℝ) * ‖g‖ * ‖r‖ * Real.sin β := by
  rw [two_re_star_groundVel, hβ]
  have hκ : 2 * kappa k = Real.sqrt (k : ℝ) := two_mul_kappa k
  rw [← hκ]
  ring

lemma exposure_density_of_master (k : ℕ) (n ndot Φdot : ℝ)
    (hk : (k : ℝ) ≠ 0) (hn : n ≠ 0)
    (hgeom : ndot ^ 2 + 4 * n ^ 2 * Φdot ^ 2 = (k : ℝ) * n * (1 - n)) :
    1 - n = (ndot ^ 2 / n + 4 * n * Φdot ^ 2) / (k : ℝ) := by
  have := hgeom
  field_simp [hk, hn] at this ⊢
  linarith

lemma finsler_density (k : ℕ) (n ndot Φdot : ℝ)
    (hk : 0 < k) (hn : 0 < n) (hn1 : n ≤ 1)
    (hgeom : ndot ^ 2 + 4 * n ^ 2 * Φdot ^ 2 = (k : ℝ) * n * (1 - n)) :
    (1 / Real.sqrt (k : ℝ)) *
        Real.sqrt (((1 - n) / n) * (ndot ^ 2 + 4 * n ^ 2 * Φdot ^ 2))
      = 1 - n := by
  have hk0 : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h1n : 0 ≤ 1 - n := sub_nonneg.mpr hn1
  have harg : 0 ≤ ((1 - n) / n) * ((k : ℝ) * n * (1 - n)) := by
    apply mul_nonneg
    · exact div_nonneg h1n hn.le
    · exact mul_nonneg (mul_nonneg hk0.le hn.le) h1n
  rw [hgeom]
  have hprod :
      ((1 - n) / n) * ((k : ℝ) * n * (1 - n)) = (k : ℝ) * (1 - n) ^ 2 := by
    field_simp [hn.ne']
  rw [hprod, Real.sqrt_mul hk0.le, Real.sqrt_sq h1n]
  field_simp [hk0.ne']

/-! ## Lemma osc (coupled driven linear oscillators) -/

lemma star_mul_of_normSq {u : ℂ} (hu : normSq u = 1) : u * star u = 1 := by
  rw [star_def, mul_conj, hu]
  norm_cast

lemma oscillator_eq (k : ℕ) (g r u nu : ℂ) (hu : normSq u = 1) :
    -I * kappa k * ((-I * nu * u) * r + u * rydbergVel k u g)
      + I * nu * groundVel k u r
      + ((k : ℂ) / 4) * g = 0 := by
  unfold groundVel rydbergVel
  have huu : u * star u = 1 := star_mul_of_normSq hu
  have hkap : (kappa k : ℂ) * (kappa k : ℂ) = (k : ℂ) / 4 := by
    rw [← ofReal_mul, ← pow_two, kappa_sq, ofReal_div, ofReal_natCast, ofReal_ofNat]
  -- Expand, cancel the `ν` terms, and use `κ² = k/4` together with `|u| = 1`.
  -- The remaining identity is `(-κ² |u|² + k/4) g = 0`.
  have hexp :
      -I * (kappa k : ℂ) * ((-I * nu * u) * r + u * (-I * kappa k * star u * g))
        + I * nu * (-I * kappa k * u * r) + ((k : ℂ) / 4) * g
        = ((k : ℂ) / 4 - (kappa k : ℂ) * (kappa k : ℂ) * (u * star u)) * g := by
    ring_nf
    simp [I_sq]
  rw [hexp, huu, hkap]
  ring

lemma kinetic_identity (k : ℕ) (u r : ℂ) (hu : normSq u = 1) :
    normSq (groundVel k u r) = (k : ℝ) / 4 * normSq r := by
  unfold groundVel
  rw [normSq_mul, normSq_mul, normSq_mul, normSq_neg, normSq_I, one_mul,
    normSq_ofReal, hu, mul_one]
  rw [show kappa k * kappa k = kappa k ^ 2 from (sq _).symm, kappa_sq]

lemma osc_cost_density (r1 r2 u1 u2 : ℂ)
    (hu1 : normSq u1 = 1) (hu2 : normSq u2 = 1) :
    pointCost r1 r2
      = 2 * normSq (groundVel 1 u1 r1) + (1 / 2) * normSq (groundVel 2 u2 r2) := by
  have h1 := kinetic_identity 1 u1 r1 hu1
  have h2 := kinetic_identity 2 u2 r2 hu2
  have hr1 : normSq r1 = 4 * normSq (groundVel 1 u1 r1) := by linarith
  have hr2 : normSq r2 = 2 * normSq (groundVel 2 u2 r2) := by linarith
  unfold pointCost
  rw [hr1, hr2]
  ring

/-! ## Lemma mu (the μ-lock constraint) -/

def muRatio (g' r : ℂ) : ℂ := g' / r

lemma mu_formula (k : ℕ) (u r : ℂ) (hr : r ≠ 0) :
    muRatio (groundVel k u r) r = -I * kappa k * u := by
  unfold muRatio groundVel
  field_simp [hr]

lemma mu_lock (u r1 r2 : ℂ) (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) :
    muRatio (groundVel 2 u r2) r2
      = (Real.sqrt 2 : ℂ) * muRatio (groundVel 1 u r1) r1 := by
  rw [mu_formula 2 u r2 hr2, mu_formula 1 u r1 hr1, kappa_two, kappa_one]
  push_cast
  ring

/-! ## Lemma ratio (nonlocal phase off the linear trajectory) -/

def stereo (r g : ℂ) : ℂ := r / g

def syncError (z1 z2 : ℂ) : ℂ := z2 - (Real.sqrt 2 : ℂ) * z1

lemma riccati (k : ℕ) (g r u : ℂ) (hg0 : g ≠ 0) :
    (rydbergVel k u g * g - r * groundVel k u r) / g ^ 2
      = -I * kappa k * star u + I * kappa k * u * (stereo r g) ^ 2 := by
  unfold groundVel rydbergVel stereo
  have : g ^ 2 ≠ 0 := pow_ne_zero 2 hg0
  field_simp [hg0, this]
  ring

lemma syncError_deriv (z1 z2 u : ℂ) :
    (-I * kappa 2 * star u + I * kappa 2 * u * z2 ^ 2)
      - (Real.sqrt 2 : ℂ) *
          (-I * kappa 1 * star u + I * kappa 1 * u * z1 ^ 2)
      = (I / (Real.sqrt 2 : ℂ)) * u * (z2 ^ 2 - z1 ^ 2) := by
  rw [kappa_one, kappa_two]
  push_cast
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  field_simp [hne, hsq]
  simp [hsq]
  ring

lemma phase_vel (k : ℕ) (g r u : ℂ) (hg0 : g ≠ 0) :
    (groundVel k u r / g).im = -(kappa k) * (u * stereo r g).re := by
  unfold stereo groundVel
  set w : ℂ := u * (r / g)
  have hz : (-I * (kappa k : ℂ) * u * r) / g = -I * (kappa k : ℂ) * w := by
    unfold w
    field_simp [hg0]
  rw [hz]
  simp [mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im]

/-- Polar ground-phase speed, first display in the proof of Lemma master. -/
lemma polar_Phidot (k : ℕ) (g r u : ℂ) (hg0 : g ≠ 0) :
    (groundVel k u r / g).im
      = -(Real.sqrt (k : ℝ) / 2) * (u * stereo r g).re := by
  simpa [kappa] using phase_vel k g r u hg0

lemma zeta_dot (z1 z2 u : ℂ) :
    -(kappa 2) * (u * z2).re + 2 * kappa 1 * (u * z1).re
      = Real.sqrt 2 *
          ((-I * kappa 1 * u) * syncError z1 z2).im := by
  rw [kappa_one, kappa_two]
  unfold syncError
  simp [mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  ring_nf
  have : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by positivity)
  simp [this]
  ring

end LowerBoundCZ
