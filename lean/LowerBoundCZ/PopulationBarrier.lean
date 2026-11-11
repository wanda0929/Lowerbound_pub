import LowerBoundCZ.SlackReachability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Population barriers used by the order-8 and order-64 reachability tests.
The series estimates are proved for every order, not assumed from a checker. -/
noncomputable section
namespace LowerBoundCZ.Certification.Slack
open CZExposure MeasureTheory Set

def barrierCoeff : ℕ → ℚ
  | 0 => 1
  | n+1 => barrierCoeff n * (2*n+1)/(2*n+2)

def barrierSeries : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, p => barrierSeries n p + (barrierCoeff (n+1) : ℝ)*p^(n+1)

private def seriesSlope : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, p => seriesSlope n p + (barrierCoeff (n+1) : ℝ)*(n+1)*p^n

theorem barrierCoeff_pos (n : ℕ) : 0 < barrierCoeff n := by
  induction n with
  | zero => norm_num [barrierCoeff]
  | succ n ih => dsimp [barrierCoeff]; positivity

private theorem coeff_step (n : ℕ) :
    (barrierCoeff (n+1) : ℝ)*(2*n+2) = (barrierCoeff n : ℝ)*(2*n+1) := by
  simp only [barrierCoeff, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one]
  field_simp

theorem barrierSeries_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ barrierSeries n p := by
  induction n with
  | zero => norm_num [barrierSeries]
  | succ n ih =>
    exact add_nonneg ih (mul_nonneg (Rat.cast_nonneg.mpr (barrierCoeff_pos _).le) (pow_nonneg hp _))

private theorem series_deriv (n : ℕ) (p : ℝ) :
    HasDerivAt (barrierSeries n) (seriesSlope n p) p := by
  induction n with
  | zero => exact hasDerivAt_const _ _
  | succ n ih =>
    simpa only [barrierSeries, seriesSlope, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, mul_assoc] using
      ih.add ((hasDerivAt_pow (n+1) p).const_mul (barrierCoeff (n+1) : ℝ))

private theorem series_identity (n : ℕ) (p : ℝ) :
    2*(1-p)*seriesSlope n p - barrierSeries n p =
      -(2*n+1)*(barrierCoeff n : ℝ)*p^n := by
  induction n with
  | zero => norm_num [barrierSeries, seriesSlope, barrierCoeff]
  | succ n ih =>
    simp only [seriesSlope, barrierSeries, Nat.cast_add, Nat.cast_one, pow_succ]
    have hc := coeff_step n
    linear_combination ih + p^n*hc

/-- The truncated binomial series never exceeds the reciprocal square-root
barrier. This uniform proof includes both orders used by the certificate. -/
theorem barrierSeries_sqrt_le (n : ℕ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Real.sqrt (1-p)*barrierSeries n p ≤ 1 := by
  let f := fun p => Real.sqrt (1-p)*barrierSeries n p
  have hc : Continuous f := (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).mul
    (continuous_iff_continuousAt.mpr (fun p => (series_deriv n p).continuousAt))
  have hd (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt f (-(2*n+1)*(barrierCoeff n : ℝ)*p^n/(2*Real.sqrt (1-p))) p := by
    have hr := ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).sqrt
      (show 1-p ≠ 0 by linarith [hp.2])
    convert hr.mul (series_deriv n p) using 1
    have hs := Real.sq_sqrt (by linarith [hp.2] : 0 ≤ 1-p)
    have hpos : 0 < Real.sqrt (1-p) := Real.sqrt_pos.2 (by linarith [hp.2])
    have hi := series_identity n p
    dsimp
    field_simp
    rw [hs]
    linarith
  have hm : AntitoneOn f (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx).deriv]
      have hcoef : (0 : ℝ) < barrierCoeff n := Rat.cast_pos.mpr (barrierCoeff_pos n)
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hcoef.le) (pow_nonneg hx.1.le _)
  have hzero : ∀ n, barrierSeries n 0 = 1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [barrierSeries, ih]
  simpa [f, hzero] using hm ⟨le_rfl, by norm_num⟩ hp hp.1

theorem barrierSeries_eq_sum (n : ℕ) (p : ℝ) :
    barrierSeries n p = ∑ k ∈ Finset.range (n+1), (barrierCoeff k : ℝ)*p^k := by
  induction n with
  | zero => simp [barrierSeries, barrierCoeff]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

def barrierG (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (barrierCoeff k : ℝ)*p^((k : ℝ)+3/2)/(2*k+3)

private theorem term_deriv (k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    HasDerivAt (fun p : ℝ => (barrierCoeff k : ℝ)*p^((k : ℝ)+3/2)/(2*k+3))
      (Real.sqrt p/2*((barrierCoeff k : ℝ)*p^k)) p := by
  have h := ((Real.hasDerivAt_rpow_const (x := p) (p := (k : ℝ)+3/2)
    (Or.inr (by have := Nat.cast_nonneg (α := ℝ) k; linarith))).const_mul
      (barrierCoeff k : ℝ)).div_const (2*k+3)
  convert h using 1
  rw [show (k : ℝ)+3/2-1 = (k : ℝ)+1/2 by ring,
    Real.rpow_add_of_nonneg hp (Nat.cast_nonneg k) (by norm_num),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  field_simp

theorem barrierG_deriv (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    HasDerivAt (barrierG n) (Real.sqrt p/2*barrierSeries n p) p := by
  have h := HasDerivAt.sum (u := Finset.range (n+1)) (fun k _ => term_deriv k hp)
  convert h using 1
  · funext t
    simp [barrierG]
  · rw [barrierSeries_eq_sum, Finset.mul_sum]

theorem barrierG_contDiff (n : ℕ) : ContDiff ℝ 1 (barrierG n) := by
  apply ContDiff.sum
  intro k hk
  exact (contDiff_const.mul (Real.contDiff_rpow_const_of_le (n := 1)
    (p := (k : ℝ)+3/2) (by norm_num; have := Nat.cast_nonneg (α := ℝ) k; linarith))).div_const _

theorem barrierG_zero (n : ℕ) : barrierG n 0 = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [Real.zero_rpow (by positivity : (k : ℝ)+3/2 ≠ 0)]
  ring

theorem barrierG_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ barrierG n p := by
  apply Finset.sum_nonneg
  intro k hk
  exact div_nonneg (mul_nonneg (Rat.cast_nonneg.mpr (barrierCoeff_pos k).le)
    (Real.rpow_nonneg hp _)) (by positivity)

theorem barrierG_mono (n : ℕ) : MonotoneOn (barrierG n) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _) (barrierG_contDiff n).continuous.continuousOn
  · exact (barrierG_contDiff n).differentiable (by decide) |>.differentiableOn
  · intro p hp
    rw [interior_Ici] at hp
    rw [(barrierG_deriv n hp.le).deriv]
    exact mul_nonneg (by positivity) (barrierSeries_nonneg n hp.le)

/-- The rational polynomial scaled by three is the checker's `h` array. -/
def barrierH (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), 3*(barrierCoeff k : ℝ)/(2*k+3)*p^k

theorem barrierG_closed (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    barrierG n p = p*Real.sqrt p*barrierH n p/3 := by
  unfold barrierG barrierH
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.rpow_add_of_nonneg hp (Nat.cast_nonneg k) (by norm_num), Real.rpow_natCast]
  rw [show (3/2 : ℝ) = 1+1/2 by norm_num,
    Real.rpow_add_of_nonneg hp (by norm_num) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  ring

def populationBarrier (n : ℕ) (p q : ℝ) : ℝ :=
  barrierG n p + barrierG n q/(2*Real.sqrt 2)

def barrierValue (n : ℕ) (x : State) : ℝ :=
  populationBarrier n (‖r1 x‖^2) (‖r2 x‖^2)

private def sectorSlope (n : ℕ) (z v : ℂ) : ℝ :=
  (Real.sqrt (‖z‖^2)/2*barrierSeries n (‖z‖^2))*(2*inner ℝ z v)

private theorem sector_speed (n : ℕ) (z g v : ℂ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hnorm : ‖g‖^2+‖z‖^2 = 1) (hv : ‖v‖ ≤ κ*‖g‖/2) :
    |sectorSlope n z v| ≤ κ*‖z‖^2/2 := by
  have hp : ‖z‖^2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [sq_nonneg ‖g‖]⟩
  have hs := barrierSeries_nonneg n hp.1
  have hg : Real.sqrt (1-‖z‖^2) = ‖g‖ := by
    rw [show 1-‖z‖^2 = ‖g‖^2 by linarith, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hbound := barrierSeries_sqrt_le n hp
  rw [hg] at hbound
  calc
    |sectorSlope n z v| = ‖z‖*barrierSeries n (‖z‖^2)*|inner ℝ z v| := by
      simp only [sectorSlope, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hs]
      ring
    _ ≤ ‖z‖*barrierSeries n (‖z‖^2)*(‖z‖*(κ*‖g‖/2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hs)
      exact (abs_real_inner_le_norm z v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    _ = (κ*‖z‖^2/2)*(‖g‖*barrierSeries n (‖z‖^2)) := by ring
    _ ≤ κ*‖z‖^2/2 := mul_le_of_le_one_right (by positivity) hbound

def barrierVelocity (n : ℕ) (x : State) (u : ℂ) : ℝ :=
  sectorSlope n (r1 x) (fC x u 1) + sectorSlope n (r2 x) (fC x u 3)/(2*Real.sqrt 2)

theorem barrier_deriv (n : ℕ) {x : ℝ → State} {u : ℂ} {t : ℝ}
    (hx : HasDerivAt x (vf (x t) u) t) :
    HasDerivAt (fun s => barrierValue n (x s)) (barrierVelocity n (x t) u) t := by
  have hr1 := amplitude_deriv hx 2 3
  have hr2 := amplitude_deriv hx 6 7
  change HasDerivAt (fun s => r1 (x s)) (fC (x t) u 1) t at hr1
  change HasDerivAt (fun s => r2 (x s)) (fC (x t) u 3) t at hr2
  exact ((barrierG_deriv n (sq_nonneg ‖r1 (x t)‖)).comp t hr1.norm_sq).add
    (((barrierG_deriv n (sq_nonneg ‖r2 (x t)‖)).comp t hr2.norm_sq).div_const _)

theorem barrier_speed_le (n : ℕ) (x : State) (hx : x ∈ Xset) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    |barrierVelocity n x u| ≤ cost x := by
  have hv1 : ‖fC x u 1‖ ≤ 1*‖g1 x‖/2 := by
    change ‖-(Complex.I/2)*(star u*g1 x)‖ ≤ 1*‖g1 x‖/2
    simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_ofNat, norm_star]
    nlinarith [mul_le_mul_of_nonneg_right hu (norm_nonneg (g1 x))]
  have hv2 : ‖fC x u 3‖ ≤ Real.sqrt 2*‖g2 x‖/2 := by
    change ‖-(Complex.I/2)*((Real.sqrt 2 : ℂ)*star u*g2 x)‖ ≤ Real.sqrt 2*‖g2 x‖/2
    simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_ofNat, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (norm_nonneg (g2 x)))
      (Real.sqrt_nonneg 2)
    nlinarith
  have h1 := sector_speed n (r1 x) (g1 x) (fC x u 1) (κ := 1) (by norm_num) hx.1 hv1
  have h2 := sector_speed n (r2 x) (g2 x) (fC x u 3) (Real.sqrt_nonneg 2) hx.2 hv2
  have h2' : |sectorSlope n (r2 x) (fC x u 3)/(2*Real.sqrt 2)| ≤
      (Real.sqrt 2*‖r2 x‖^2/2)/(2*Real.sqrt 2) := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.sqrt 2)]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have h := (abs_add_le (sectorSlope n (r1 x) (fC x u 1))
    (sectorSlope n (r2 x) (fC x u 3)/(2*Real.sqrt 2))).trans (add_le_add h1 h2')
  convert h using 1
  unfold cost
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem barrierValue_contDiff (n : ℕ) : ContDiff ℝ 1 (barrierValue n) := by
  have h1 : ContDiff ℝ 1 (fun x : State => ‖r1 x‖^2) := by
    simp only [r1, Complex.sq_norm, Complex.normSq_apply]
    fun_prop
  have h2 : ContDiff ℝ 1 (fun x : State => ‖r2 x‖^2) := by
    simp only [r2, Complex.sq_norm, Complex.normSq_apply]
    fun_prop
  exact ((barrierG_contDiff n).comp h1).add (((barrierG_contDiff n).comp h2).div_const _)

theorem barrier_ac (n : ℕ) (P : PhysicalSegment) :
    AbsolutelyContinuousOnInterval (fun t => barrierValue n (P.path t)) 0 P.duration := by
  have hc := isCompact_Icc.image_of_continuousOn P.path_lipschitzOn.continuousOn
  obtain ⟨K, hK⟩ := (barrierValue_contDiff n).locallyLipschitz.locallyLipschitzOn
    |>.exists_lipschitzOnWith_of_compact hc
  have h := hK.comp P.path_lipschitzOn (fun t ht => mem_image_of_mem _ ht)
  rw [← uIcc_of_le P.duration_nonneg] at h
  exact h.absolutelyContinuousOnInterval

theorem barrier_increment (n : ℕ) (P : PhysicalSegment) {a b : ℝ}
    (ha : a ∈ Icc 0 P.duration) (hb : b ∈ Icc 0 P.duration) (hab : a ≤ b) :
    |barrierValue n (P.path b) - barrierValue n (P.path a)| ≤
      ∫ t in a..b, cost (P.path t) := by
  have hAC := (barrier_ac n P).mono (uIcc_subset_uIcc_of_mem ha hb)
  rw [← hAC.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  apply intervalIntegral.integral_mono_ae_restrict hab hAC.intervalIntegrable_deriv.norm
    (P.cost_intervalIntegrable.mono_set (uIcc_subset_uIcc_of_mem ha hb))
  have hd := P.ae_hasDerivAt_path.filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono (Icc_subset_Icc ha.1 hb.2) le_rfl))
  filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht htab
  rw [(barrier_deriv n ht).deriv, Real.norm_eq_abs]
  exact barrier_speed_le n _ (P.path_mem t ⟨ha.1.trans htab.1, htab.2.trans hb.2⟩) _
    (P.control_bound t ⟨ha.1.trans htab.1, htab.2.trans hb.2⟩)

/-- The excursion and the return both consume exposure. No duration bound,
strictly positive population, or extra smoothness of the control is assumed. -/
theorem population_budget (n : ℕ) (γ : ActivePulse) {s : ℝ} (hs : s ∈ Icc 0 γ.S) :
    barrierValue n (γ.x s) ≤ min (γ.cumI s) (γ.exposure - γ.cumI s) := by
  let P := (toLab γ).toSegment
  have hi : barrierValue n (γ.x 0) = 0 := by
    change barrierValue n ((toLab γ).x 0) = 0
    rw [(toLab γ).initial]
    change barrierG n (‖(0 : ℂ)‖^2) + barrierG n (‖(0 : ℂ)‖^2)/(2*Real.sqrt 2) = 0
    simp [barrierG_zero]
  have ht : barrierValue n (γ.x γ.S) = 0 := by
    simp [barrierValue, populationBarrier, γ.terminal.2.1, γ.terminal.2.2.1, barrierG_zero]
  have hf := barrier_increment n P ⟨le_rfl, γ.S_nonneg⟩ hs hs.1
  have hr := barrier_increment n P hs ⟨γ.S_nonneg, le_rfl⟩ hs.2
  change |barrierValue n (γ.x s) - barrierValue n (γ.x 0)| ≤ _ at hf
  change |barrierValue n (γ.x γ.S) - barrierValue n (γ.x s)| ≤ _ at hr
  rw [hi, sub_zero] at hf
  rw [ht, zero_sub, abs_neg] at hr
  have he (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S) :
      (∫ t in a..b, cost (P.path t)) = γ.cumI b - γ.cumI a := by
    rw [γ.cumI_sub ha hab hb]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    change cost (P.path t) = cost (γ.traj t)
    rw [γ.traj_eq ⟨ha.trans ht.1, ht.2.trans hb⟩]
    rfl
  rw [he 0 s le_rfl hs.1 hs.2, γ.cumI_zero, sub_zero] at hf
  rw [he s γ.S hs.1 hs.2 le_rfl, γ.cumI_S] at hr
  exact (le_abs_self _).trans (le_min hf hr)

theorem population_interval_budget (n : ℕ) (γ : ActivePulse) {s H l r : ℝ}
    (hs : s ∈ Icc 0 γ.S) (hH : γ.exposure ≤ H)
    (hl : l ≤ γ.cumI s) (hr : γ.cumI s ≤ r) :
    barrierValue n (γ.x s) ≤ min r (H-l) :=
  (population_budget n γ hs).trans (min_le_min hr (by linarith))

/-- Exact rational quantity used by the checkers, with their factor of 3
in `h`. Its value is nine times the square of the sector barrier. -/
def barrierEnergy (n : ℕ) (p : ℝ) : ℝ := p^3*(barrierH n p)^2

theorem barrierEnergy_rat (n : ℕ) (p : ℚ) :
    barrierEnergy n (p : ℝ) =
      ((p^3*(∑ k ∈ Finset.range (n+1), 3*barrierCoeff k/(2*k+3)*p^k)^2 : ℚ) : ℝ) := by
  unfold barrierEnergy barrierH
  push_cast
  rfl

theorem barrierEnergy_eq (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    barrierEnergy n p = 9*(barrierG n p)^2 := by
  rw [barrierG_closed n hp]
  unfold barrierEnergy
  ring_nf
  rw [Real.sq_sqrt hp]
  ring

/-- The actual rational exclusion predicate: either the sum already exceeds
the squared budget, or the positive cross term makes it exceed the budget. -/
def PopulationBoxExcluded (n : ℕ) (p q R : ℝ) : Prop :=
  let A := 8*barrierEnergy n p
  let D := barrierEnergy n q
  let T := 72*R^2
  T < A+D ∨ (T-A-D)^2 < 4*A*D

theorem population_rational_excludes (n : ℕ) {p q R : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hex : PopulationBoxExcluded n p q R) : R < populationBarrier n p q := by
  by_contra hn
  have hw := le_of_not_gt hn
  have hu := barrierG_nonneg n hp
  have hv := barrierG_nonneg n hq
  have hw0 : 0 ≤ populationBarrier n p q := add_nonneg hu (div_nonneg hv (by positivity))
  have hsq := (sq_le_sq₀ hw0 hR).mpr hw
  have hs : (Real.sqrt 2)^2 = 2 := by norm_num
  have hcross : 72*(populationBarrier n p q)^2 =
      72*(barrierG n p)^2+9*(barrierG n q)^2+
        36*Real.sqrt 2*barrierG n p*barrierG n q := by
    unfold populationBarrier
    have hne : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    ring_nf
    norm_num
    rw [show (Real.sqrt 2)^3 = 2*Real.sqrt 2 by rw [pow_succ, hs]]
    ring
  have hc0 : 0 ≤ 36*Real.sqrt 2*barrierG n p*barrierG n q := by positivity
  have hc : 36*Real.sqrt 2*barrierG n p*barrierG n q ≤
      72*R^2-72*(barrierG n p)^2-9*(barrierG n q)^2 := by linarith
  have hc2 := (sq_le_sq₀ hc0 (hc0.trans hc)).mpr hc
  have hprod : (36*Real.sqrt 2*barrierG n p*barrierG n q)^2 =
      4*(72*(barrierG n p)^2)*(9*(barrierG n q)^2) := by
    ring_nf
    norm_num
    ring
  unfold PopulationBoxExcluded at hex
  rw [barrierEnergy_eq n hp, barrierEnergy_eq n hq] at hex
  rcases hex with h | h
  · nlinarith
  · nlinarith [hprod]

/-- Only the lower corner is needed: `W_n` is increasing in both populations.
Together with the exposure interval budget, the checker's rational predicate
therefore excludes every point of the closed population rectangle. -/
theorem population_box_excludes (n : ℕ) (γ : ActivePulse) {s H l r a c : ℝ}
    (hs : s ∈ Icc 0 γ.S) (hH : γ.exposure ≤ H)
    (hl : l ≤ γ.cumI s) (hr : γ.cumI s ≤ r)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hp : a ≤ ‖r1 (γ.x s)‖^2) (hq : c ≤ ‖r2 (γ.x s)‖^2)
    (hex : PopulationBoxExcluded n a c (min r (H-l))) : False := by
  have hm : populationBarrier n a c ≤ barrierValue n (γ.x s) :=
    add_le_add (barrierG_mono n ha (sq_nonneg ‖r1 (γ.x s)‖) hp)
      (div_le_div_of_nonneg_right (barrierG_mono n hc (sq_nonneg ‖r2 (γ.x s)‖) hq) (by positivity))
  have hb := population_interval_budget n γ hs hH hl hr
  have hR : 0 ≤ min r (H-l) :=
    (add_nonneg (barrierG_nonneg n ha) (div_nonneg (barrierG_nonneg n hc) (by positivity))).trans
      (hm.trans hb)
  exact (not_lt_of_ge (hm.trans hb)) (population_rational_excludes n ha hc hR hex)

end LowerBoundCZ.Certification.Slack
