/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Reductions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# No-go theorems for shortcut relaxations

Theorems `free` and `relax` from `control-appendices.tex` §B.
-/

noncomputable section

namespace LowerBoundCZ

open Complex Filter Topology

def omega (c Δ : ℝ) : ℝ := Real.sqrt (c ^ 2 + Δ ^ 2 / 4)

lemma omega_pos {c Δ : ℝ} (hc : 0 < c) : 0 < omega c Δ := by
  unfold omega
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg Δ, hc]

lemma two_omega_sq (c Δ : ℝ) :
    (2 * omega c Δ) ^ 2 = 4 * c ^ 2 + Δ ^ 2 := by
  unfold omega
  have h : 0 ≤ c ^ 2 + Δ ^ 2 / 4 := by nlinarith [sq_nonneg c, sq_nonneg Δ]
  rw [mul_pow, Real.sq_sqrt h]
  ring

def phaseFactor (c Δ : ℝ) : ℝ := 1 - Δ / (2 * omega c Δ)

def chirpExposure (c Δ : ℝ) (m : ℕ) : ℝ :=
  m * Real.pi * c ^ 2 / (2 * omega c Δ ^ 3)

/-- Closed-form chirp exposure after eliminating `Δ` via the phase map. -/
def chirpExposureClosed (c Q : ℝ) (m : ℕ) : ℝ :=
  (Real.pi / 2) / |c| *
    (2 * Q - Q ^ 2 / (m : ℝ)) ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ)

/-- Algebraic inversion of the chirp phase map. -/
lemma omega_sq_of_phase_target {c Δ Q : ℝ} {m : ℕ}
    (hc : 0 < c) (h : phaseFactor c Δ = Q / m) :
    Δ = 2 * omega c Δ * (1 - Q / m) := by
  have hω : 0 < omega c Δ := omega_pos hc
  unfold phaseFactor at h
  have : Δ / (2 * omega c Δ) = 1 - Q / m := by linarith
  have h2 : 2 * omega c Δ ≠ 0 := by positivity
  field_simp [h2] at this
  linarith

/-- The identity `ω² = c² + ω² (1 - Q/m)²` after substituting the phase map. -/
lemma omega_sq_from_phase {c Δ Q : ℝ} {m : ℕ}
    (hc : 0 < c) (hm : (m : ℝ) ≠ 0) (h : phaseFactor c Δ = Q / m) :
    omega c Δ ^ 2 * (2 * Q / m - Q ^ 2 / m ^ 2) = c ^ 2 := by
  have hΔ := omega_sq_of_phase_target hc h
  have hdef : omega c Δ ^ 2 = c ^ 2 + Δ ^ 2 / 4 := by
    unfold omega
    exact Real.sq_sqrt (by nlinarith [sq_nonneg c, sq_nonneg Δ])
  have hsq : Δ ^ 2 = (2 * omega c Δ * (1 - Q / m)) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hΔ
  have hΔsq : Δ ^ 2 / 4 = omega c Δ ^ 2 * (1 - Q / m) ^ 2 := by
    rw [hsq]
    ring
  have hexp : omega c Δ ^ 2 = c ^ 2 + omega c Δ ^ 2 * (1 - Q / m) ^ 2 := by
    calc
      omega c Δ ^ 2 = c ^ 2 + Δ ^ 2 / 4 := hdef
      _ = c ^ 2 + omega c Δ ^ 2 * (1 - Q / m) ^ 2 := by rw [hΔsq]
  have hfac :
      1 - (1 - Q / m) ^ 2 = 2 * Q / m - Q ^ 2 / m ^ 2 := by
    field_simp [hm]
    ring
  calc
    omega c Δ ^ 2 * (2 * Q / m - Q ^ 2 / m ^ 2)
        = omega c Δ ^ 2 * (1 - (1 - Q / m) ^ 2) := by rw [hfac]
    _ = omega c Δ ^ 2 - omega c Δ ^ 2 * (1 - Q / m) ^ 2 := by ring
    _ = c ^ 2 := by linarith [hexp]

lemma of_unit_norm_arg_pi {z : ℂ} (hn : ‖z‖ = 1) (ha : arg z = Real.pi) :
    z = -1 := by
  have hz0 : z ≠ 0 := by
    intro hz; simp [hz] at hn
  rw [← norm_mul_exp_arg_mul_I z, hn, ha]
  simp [exp_pi_mul_I]

/-- Stationary (zero-amplitude) control realizes the trivial target at zero
exposure. This is the `|v| = 0` laboratory idle; it is not a max-amplitude
path. -/
theorem theorem_free_trivial_zero (k : ℕ) :
    ∃ L : ClosedLoop k, L.exposure = 0 ∧ L.g L.S = 1 := by
  refine ⟨{
      S := 1
      hS := by norm_num
      g := fun _ => 1
      r := fun _ => 0
      u := fun _ => 0
      hu := by intro _ _; simp [normSq]
      hg := by
        intro s _
        simpa [groundVel_zero_ctrl] using hasDerivAt_const s (1 : ℂ)
      hr := by
        intro s _
        simpa [rydbergVel_zero_ctrl] using hasDerivAt_const s (0 : ℂ)
      nrm := by intro _ _; simp [normSq]
      g_init := rfl
      r_init := rfl
      r_final := rfl }, ?_, rfl⟩
  change (∫ s in (0 : ℝ)..(1 : ℝ), normSq (0 : ℂ)) = 0
  simp

lemma inv_sqrt_succ_tendsto_zero :
    Tendsto (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))

lemma chirpExposureClosed_nonneg {c Q : ℝ} {m : ℕ}
    (hQ : 0 < Q) (hQ2 : Q < 2) (hm : 0 < m) :
    0 ≤ chirpExposureClosed c Q m := by
  unfold chirpExposureClosed
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt hm
  have hQm : Q / (m : ℝ) ≤ Q := div_le_self hQ.le hm1
  have harg : 0 ≤ 2 * Q - Q ^ 2 / (m : ℝ) := by
    have hlt : Q / (m : ℝ) < 2 := lt_of_le_of_lt hQm hQ2
    have hfac : 0 ≤ 2 - Q / (m : ℝ) := le_of_lt (sub_pos.mpr hlt)
    have : 2 * Q - Q ^ 2 / (m : ℝ) = Q * (2 - Q / (m : ℝ)) := by
      field_simp [hm0.ne']
    rw [this]
    exact mul_nonneg hQ.le hfac
  positivity

/-- The closed-form chirp exposures tend to zero, using an inverse-square-root upper bound. -/
lemma chirpExposureClosed_tendsto_zero {c Q : ℝ} (hQ : 0 < Q) (hQ2 : Q < 2) :
    Tendsto (fun n : ℕ => chirpExposureClosed c Q (n + 1)) atTop (nhds 0) := by
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  set K : ℝ := (Real.pi / 2) / |c| * (2 * Q) ^ ((3 : ℝ) / 2)
  have hup : Tendsto (fun n : ℕ => K * (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
      atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := K)).mul inv_sqrt_succ_tendsto_zero
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h0 hup ?_ ?_
  · intro n
    exact chirpExposureClosed_nonneg hQ hQ2 (Nat.succ_pos _)
  · intro n
    have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hm0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have hQm : Q / ((n + 1 : ℕ) : ℝ) ≤ Q := div_le_self hQ.le hm1
    have harg0 : 0 ≤ 2 * Q - Q ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      have hlt : Q / ((n + 1 : ℕ) : ℝ) < 2 := lt_of_le_of_lt hQm hQ2
      have hfac : 0 ≤ 2 - Q / ((n + 1 : ℕ) : ℝ) := le_of_lt (sub_pos.mpr hlt)
      have : 2 * Q - Q ^ 2 / ((n + 1 : ℕ) : ℝ)
          = Q * (2 - Q / ((n + 1 : ℕ) : ℝ)) := by
        field_simp [hm0.ne']
      rw [this]
      exact mul_nonneg hQ.le hfac
    have hargle : 2 * Q - Q ^ 2 / ((n + 1 : ℕ) : ℝ) ≤ 2 * Q := by
      have : 0 ≤ Q ^ 2 / ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hpow :=
      Real.rpow_le_rpow harg0 hargle (by positivity : (0 : ℝ) ≤ 3 / 2)
    have hsqrt0 : 0 ≤ (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hpre : 0 ≤ (Real.pi / 2) / |c| := by positivity
    unfold chirpExposureClosed
    calc
      (Real.pi / 2) / |c| *
          (2 * Q - Q ^ 2 / ((n + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2)
            / Real.sqrt ((n + 1 : ℕ) : ℝ)
          = (Real.pi / 2) / |c| *
              (2 * Q - Q ^ 2 / ((n + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2)
                * (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
            field_simp
      _ ≤ K * (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
            unfold K
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow hpre) hsqrt0

namespace Chirp

private def rot (a s : ℝ) : ℂ := exp ((a * s : ℝ) * I)

private lemma rot_mul (a b s : ℝ) : rot a s * rot b s = rot (a + b) s := by
  simp only [rot, ← exp_add]
  congr 1
  push_cast
  ring

private lemma rot_norm (a s : ℝ) : normSq (rot a s) = 1 := by
  rw [rot, normSq_eq_norm_sq, norm_exp_ofReal_mul_I]
  norm_num

private lemma rot_deriv (a s : ℝ) :
    HasDerivAt (rot a) (a * I * rot a s) s := by
  have h := (((hasDerivAt_id s).const_mul a).ofReal_comp.mul_const I).cexp
  apply h.congr_deriv
  simp only [rot, id_eq, mul_one, ofReal_mul]
  ring

/-- Rotating-frame solution, returned to the original ground amplitude. -/
private def g (c Δ s : ℝ) : ℂ := rot (-Δ / 2) s *
  ((Real.cos (omega c Δ * s) : ℂ) + I * (Δ / (2 * omega c Δ) : ℝ) *
    (Real.sin (omega c Δ * s) : ℂ))

private def r (c Δ s : ℝ) : ℂ := rot (Δ / 2) s *
  (-I * (c / omega c Δ : ℝ) * (Real.sin (omega c Δ * s) : ℂ))

private lemma r_norm (c Δ s : ℝ) : normSq (r c Δ s) =
    c ^ 2 / omega c Δ ^ 2 * Real.sin (omega c Δ * s) ^ 2 := by
  simp only [r, normSq_mul, rot_norm, normSq_neg, normSq_I, normSq_ofReal,
    one_mul, ← pow_two, div_pow]

private lemma g_norm (c Δ s : ℝ) : normSq (g c Δ s) =
    Real.cos (omega c Δ * s) ^ 2 + (Δ / (2 * omega c Δ)) ^ 2 *
      Real.sin (omega c Δ * s) ^ 2 := by
  rw [g, normSq_mul, rot_norm, one_mul]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im]
  ring

private lemma g_deriv (k : ℕ) (hk : 0 < k) (Δ s : ℝ) :
    HasDerivAt (g (kappa k) Δ)
      (groundVel k (rot (-Δ) s) (r (kappa k) Δ s)) s := by
  set c := kappa k
  set w := omega c Δ
  have hw : w ≠ 0 := (omega_pos (kappa_pos hk)).ne'
  have hd := (rot_deriv (-Δ / 2) s).mul
    ((((hasDerivAt_id s).const_mul w).cos.ofReal_comp).add
      ((((hasDerivAt_id s).const_mul w).sin.ofReal_comp).const_mul
        (I * (Δ / (2 * w) : ℝ))))
  apply hd.congr_deriv
  symm
  unfold groundVel r
  have hexp : rot (-Δ) s * rot (Δ / 2) s = rot (-Δ / 2) s := by
    rw [rot_mul]; congr 1; ring
  simp only [id_eq, mul_one, Pi.add_apply]
  rw [show -I * (kappa k : ℂ) * rot (-Δ) s *
      (rot (Δ / 2) s * (-I * (c / w : ℝ) * (Real.sin (w * s) : ℂ))) =
      (-I * (kappa k : ℂ)) * (rot (-Δ) s * rot (Δ / 2) s) *
        (-I * (c / w : ℝ) * (Real.sin (w * s) : ℂ)) by ring, hexp]
  have hw2 := two_omega_sq (c := c) (Δ := Δ)
  have hwc : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw
  simp only [ofReal_div, ofReal_mul, ofReal_neg, ofReal_ofNat]
  field_simp
  simp only [I_sq]
  have hw2c : (2 * (w : ℂ)) ^ 2 = 4 * (c : ℂ) ^ 2 + (Δ : ℂ) ^ 2 := by
    exact_mod_cast hw2
  linear_combination (norm := skip) rot (-Δ / 2) s * (Real.sin (w * s) : ℂ) * hw2c
  ring_nf
  simp only [I_sq, neg_div]
  ring

private lemma r_deriv (k : ℕ) (hk : 0 < k) (Δ s : ℝ) :
    HasDerivAt (r (kappa k) Δ)
      (rydbergVel k (rot (-Δ) s) (g (kappa k) Δ s)) s := by
  set c := kappa k
  set w := omega c Δ
  have hw : w ≠ 0 := (omega_pos (kappa_pos hk)).ne'
  have hd := (rot_deriv (Δ / 2) s).mul
    ((((hasDerivAt_id s).const_mul w).sin.ofReal_comp).const_mul
      (-I * (c / w : ℝ)))
  apply hd.congr_deriv
  symm
  unfold rydbergVel g
  have hconj : star (rot (-Δ) s) = rot Δ s := by
    simp only [rot, star_def, ← exp_conj, map_mul, conj_ofReal, conj_I]
    congr 1
    push_cast
    ring
  rw [hconj]
  have hexp : rot Δ s * rot (-Δ / 2) s = rot (Δ / 2) s := by
    rw [rot_mul]; congr 1; ring
  simp only [id_eq, mul_one]
  rw [show -I * (kappa k : ℂ) * rot Δ s *
      (rot (-Δ / 2) s * ((Real.cos (w * s) : ℂ) +
        I * (Δ / (2 * w) : ℝ) * (Real.sin (w * s) : ℂ))) =
      (-I * (kappa k : ℂ)) * (rot Δ s * rot (-Δ / 2) s) *
        ((Real.cos (w * s) : ℂ) + I * (Δ / (2 * w) : ℝ) *
          (Real.sin (w * s) : ℂ)) by ring, hexp]
  have hwc : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw
  simp only [ofReal_div, ofReal_mul, ofReal_ofNat]
  field_simp
  ring

private lemma normalized (c Δ s : ℝ) (hc : 0 < c) :
    normSq (g c Δ s) + normSq (r c Δ s) = 1 := by
  rw [g_norm, r_norm]
  have hw := omega_pos (Δ := Δ) hc
  have hw2 := two_omega_sq (c := c) (Δ := Δ)
  have htrig := Real.sin_sq_add_cos_sq (omega c Δ * s)
  field_simp
  linear_combination -(Real.sin (omega c Δ * s)) ^ 2 * hw2 +
    4 * omega c Δ ^ 2 * htrig

private lemma exposure (c Δ : ℝ) (hc : 0 < c) (m : ℕ) :
    (∫ s in (0 : ℝ)..(m * Real.pi / omega c Δ), normSq (r c Δ s)) =
      chirpExposure c Δ m := by
  have hw := omega_pos (Δ := Δ) hc
  simp_rw [r_norm]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun s : ℝ => Real.sin s ^ 2) hw.ne']
  rw [mul_zero, mul_div_cancel₀ _ hw.ne', integral_sin_sq]
  simp only [Real.sin_zero, Real.sin_nat_mul_pi, zero_mul, sub_zero, zero_add]
  unfold chirpExposure
  simp only [smul_eq_mul]
  ring

end Chirp

/-- The explicit rotating-frame solution gives a closed loop for every
positive sector and return count. The terminal phase is modulo `2π`,
expressed as a complex exponential rather than an unbounded principal arg. -/
theorem exists_chirp_loop (k : ℕ) (hk : 0 < k) (Δ : ℝ) (m : ℕ) (hm : 0 < m) :
  ∃ L : ClosedLoop k,
    L.exposure = chirpExposure (kappa k) Δ m ∧
      L.g L.S = exp ((m * Real.pi * phaseFactor (kappa k) Δ : ℝ) * I) := by
  set c := kappa k
  set w := omega c Δ
  have hc : 0 < c := kappa_pos hk
  have hw : 0 < w := omega_pos hc
  have htime : omega c Δ * (m * Real.pi / w) = m * Real.pi := by
    change w * (m * Real.pi / w) = m * Real.pi
    field_simp
  let L : ClosedLoop k := {
    S := m * Real.pi / w
    hS := by positivity
    g := Chirp.g c Δ
    r := Chirp.r c Δ
    u := Chirp.rot (-Δ)
    hu := by intro s _; rw [Chirp.rot_norm]
    hg := by intro s _; exact Chirp.g_deriv k hk Δ s
    hr := by intro s _; exact Chirp.r_deriv k hk Δ s
    nrm := by intro s _; exact Chirp.normalized c Δ s hc
    g_init := by simp [Chirp.g, Chirp.rot]
    r_init := by simp [Chirp.r, Chirp.rot]
    r_final := by simp only [Chirp.r, htime, Real.sin_nat_mul_pi, ofReal_zero, mul_zero] }
  refine ⟨L, Chirp.exposure c Δ hc m, ?_⟩
  change Chirp.g c Δ (m * Real.pi / w) = _
  simp only [Chirp.g, htime, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, ofReal_zero,
    mul_zero, add_zero, ofReal_pow, ofReal_neg, ofReal_one]
  rw [← exp_pi_mul_I, ← exp_nat_mul, Chirp.rot, ← exp_add]
  congr 1
  unfold phaseFactor
  dsimp [w]
  push_cast
  ring

/-- Explicit detuning realizing any target ratio in `(0, 2)`. -/
theorem exists_detuning_for_phase (c Q : ℝ) (m : ℕ)
    (hc : 0 < c) (hQ : 0 < Q) (hQ2 : Q < 2) (hm : 1 ≤ m) :
    ∃ Δ : ℝ, phaseFactor c Δ = Q / m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  set q := Q / (m : ℝ)
  have hq : 0 < q := div_pos hQ hm0
  have hq2 : q < 2 := lt_of_le_of_lt (div_le_self hQ.le hm1) hQ2
  set t := 1 - q
  have ht : 0 < 1 - t ^ 2 := by dsimp [t]; nlinarith
  set r := Real.sqrt (1 - t ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr ht
  have hr2 : r ^ 2 = 1 - t ^ 2 := Real.sq_sqrt ht.le
  have hw : omega c (2 * c * t / r) = c / r := by
    unfold omega
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp
    nlinarith [sq_nonneg c]
  refine ⟨2 * c * t / r, ?_⟩
  unfold phaseFactor
  rw [hw]
  dsimp [t]
  field_simp
  ring

/-- Equality of the two chirp-exposure presentations after eliminating `Δ`. -/
theorem chirpExposure_eq_closed {c Δ Q : ℝ} {m : ℕ}
    (hc : 0 < c) (hm : 0 < m)
    (h : phaseFactor c Δ = Q / m) :
    chirpExposure c Δ m = chirpExposureClosed c Q m := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hw := omega_pos (Δ := Δ) hc
  have heq := omega_sq_from_phase hc hm0.ne' h
  set a := 2 * Q - Q ^ 2 / (m : ℝ)
  have haeq : omega c Δ ^ 2 * a = c ^ 2 * m := by
    dsimp [a]
    field_simp at heq ⊢
    nlinarith
  have ha : 0 < a := by nlinarith [sq_pos_of_pos hc]
  have hs : Real.sqrt a = c * Real.sqrt (m : ℝ) / omega c Δ := by
    apply (Real.sqrt_eq_iff_eq_sq ha.le (by positivity)).2
    rw [div_pow, mul_pow, Real.sq_sqrt hm0.le]
    exact (eq_div_iff (pow_ne_zero _ hw.ne')).2 (by nlinarith [haeq])
  have hp : a ^ ((3 : ℝ) / 2) = a * Real.sqrt a := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ha,
      Real.rpow_one, Real.sqrt_eq_rpow]
  unfold chirpExposure chirpExposureClosed
  rw [abs_of_pos hc]
  change _ = Real.pi / 2 / c * a ^ ((3 : ℝ) / 2) / Real.sqrt (m : ℝ)
  rw [hp, hs]
  field_simp
  nlinarith [haeq]

/-- Theorem free: every nontrivial unit phase is attained exactly by closed
loops with arbitrarily small exposure. It is the zero-exposure infimum,
not the target phase, that is approached. -/
theorem theorem_free (k : ℕ) (hk : 0 < k) {Φ Q : ℝ}
    (hQ : 0 < Q) (hQ2 : Q < 2) (hΦ : Φ = Q * Real.pi) :
    ∀ ε > 0, ∃ L : ClosedLoop k, L.exposure < ε ∧ L.g L.S = exp (Φ * I) := by
  intro ε hε
  have hc : 0 < kappa k := kappa_pos hk
  have htend := chirpExposureClosed_tendsto_zero (c := kappa k) hQ hQ2
  have hlim : ∀ᶠ n : ℕ in atTop, chirpExposureClosed (kappa k) Q (n + 1) < ε :=
    htend.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := hlim.exists
  have hm : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨Δ, hΔ⟩ := exists_detuning_for_phase (kappa k) Q (N + 1) hc hQ hQ2 hm
  obtain ⟨L, hE, harg⟩ := exists_chirp_loop k hk Δ (N + 1) (Nat.succ_pos _)
  refine ⟨L, ?_, ?_⟩
  · have hclosed :
        chirpExposure (kappa k) Δ (N + 1) =
          chirpExposureClosed (kappa k) Q (N + 1) :=
      chirpExposure_eq_closed hc (Nat.succ_pos _) hΔ
    have hlt : chirpExposureClosed (kappa k) Q (N + 1) < ε := hN
    linarith [hE, hclosed, hlt]
  · have : (↑(N + 1) : ℝ) * Real.pi * phaseFactor (kappa k) Δ = Φ := by
      rw [hΔ, hΦ]
      field_simp
    rw [harg, this]

/-- Theorem relax: independent drives allow vanishing exposure. -/
theorem theorem_relax
    (hfree : ∀ ε > 0, ∃ L : ClosedLoop 2,
      L.exposure < ε ∧ L.g L.S = -1) :
    ∀ ε > 0, ∃ tr : IndependentTrajectory, tr.IsCZ ∧ tr.exposure < ε := by
  intro ε hε
  have h4 : (0 : ℝ) < 4 * ε := by positivity
  obtain ⟨L, hE, hΦ⟩ := hfree (4 * ε) h4
  refine ⟨{
      S := L.S
      hS := L.hS
      g1 := fun _ => 1
      r1 := fun _ => 0
      g2 := L.g
      r2 := L.r
      u1 := fun _ => 0
      u2 := L.u
      hu1 := by intro _ _; simp [normSq]
      hu2 := L.hu
      hg1 := by
        intro s _
        simpa [groundVel_zero_ctrl] using hasDerivAt_const s (1 : ℂ)
      hr1 := by
        intro s _
        simpa [rydbergVel_zero_ctrl] using hasDerivAt_const s (0 : ℂ)
      hg2 := L.hg
      hr2 := L.hr
      n1 := by intro _ _; simp [normSq]
      n2 := L.nrm
      g1_init := rfl
      r1_init := rfl
      g2_init := L.g_init
      r2_init := L.r_init }, ?_, ?_⟩
  · refine ⟨rfl, L.r_final, ?_⟩
    simp [hΦ]
  · have hcost : ∀ s, pointCost (0 : ℂ) (L.r s) = normSq (L.r s) / 4 :=
      fun _ => pointCost_idle_left _
    have hE' : L.exposure < 4 * ε := hE
    change (∫ s in (0 : ℝ)..L.S, pointCost (0 : ℂ) (L.r s)) < ε
    simp only [hcost]
    have hdiv :
        (∫ s in (0 : ℝ)..L.S, normSq (L.r s) / 4)
          = (∫ s in (0 : ℝ)..L.S, normSq (L.r s)) / 4 :=
      intervalIntegral.integral_div (4 : ℝ) (fun s => normSq (L.r s))
    rw [hdiv]
    have : L.exposure / 4 < ε := by nlinarith [hE']
    simpa [ClosedLoop.exposure] using this

/-- Combining Theorems free and relax: the lock-free infimum is zero. -/
theorem theorem_relax' :
    ∀ ε > 0, ∃ tr : IndependentTrajectory, tr.IsCZ ∧ tr.exposure < ε := by
  apply theorem_relax
  simpa using (theorem_free 2 (by norm_num) (Φ := Real.pi) (Q := 1)
    (by norm_num) (by norm_num) (by ring))

end LowerBoundCZ
