import LowerBoundCZ.CertificateContracts
import Mathlib.Analysis.Complex.RealDeriv

/-! Shared-drive reachability constraints for the strengthened certificate. -/
noncomputable section
namespace LowerBoundCZ.Certification.Slack
open CZExposure Complex MeasureTheory Set
set_option maxHeartbeats 2000000

def dark (x : State) : ℂ := g1 x * r2 x - (Real.sqrt 2 : ℂ) * g2 x * r1 x
def darkVelocity (x : State) (u : ℂ) : ℂ := I / 2 * u * r1 x * r2 x

theorem amplitude_deriv {x : ℝ → State} {v : State} {t : ℝ}
    (hx : HasDerivAt x v t) (i j : Fin 8) :
    HasDerivAt (fun s => (⟨x s i, x s j⟩ : ℂ)) (⟨v i, v j⟩ : ℂ) t := by
  have hi := ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hx).ofReal_comp
  have hj := ((ContinuousLinearMap.proj j : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hx).ofReal_comp
  simpa only [Complex.mk_eq_add_mul_I] using hi.add (hj.mul_const I)

theorem dark_deriv {x : ℝ → State} {u : ℂ} {t : ℝ}
    (hx : HasDerivAt x (vf (x t) u) t) :
    HasDerivAt (fun s => dark (x s)) (darkVelocity (x t) u) t := by
  have hg1 := amplitude_deriv hx 0 1
  have hr1 := amplitude_deriv hx 2 3
  have hg2 := amplitude_deriv hx 4 5
  have hr2 := amplitude_deriv hx 6 7
  change HasDerivAt (fun s => g1 (x s)) (fC (x t) u 0) t at hg1
  change HasDerivAt (fun s => r1 (x s)) (fC (x t) u 1) t at hr1
  change HasDerivAt (fun s => g2 (x s)) (fC (x t) u 2) t at hg2
  change HasDerivAt (fun s => r2 (x s)) (fC (x t) u 3) t at hr2
  convert (hg1.mul hr2).sub ((hg2.const_mul (Real.sqrt 2 : ℂ)).mul hr1) using 1
  change I / 2 * u * r1 (x t) * r2 (x t) =
    (-(I/2) * (u * r1 (x t))) * r2 (x t) +
      g1 (x t) * (-(I/2) * ((Real.sqrt 2 : ℂ) * star u * g2 (x t))) -
      ((Real.sqrt 2 : ℂ) * (-(I/2) * ((Real.sqrt 2 : ℂ) * u * r2 (x t))) * r1 (x t) +
        (Real.sqrt 2 : ℂ) * g2 (x t) * (-(I/2) * (star u * g1 (x t))))
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    norm_num
  linear_combination -(I / 2 * u * r1 (x t) * r2 (x t)) * hs

/-- The nonnegative remainder uses the common drive; no terminal information
or bound on the pulse duration enters this identity. -/
theorem dark_speed_identity (x : State) (u : ℂ) :
    cost x ^ 2 - 2 * ‖darkVelocity x u‖ ^ 2 =
      (2 * ‖r1 x‖ ^ 2 - ‖r2 x‖ ^ 2)^2 / 16 +
        (1 - ‖u‖ ^ 2) * ‖r1 x‖ ^ 2 * ‖r2 x‖ ^ 2 / 2 := by
  simp only [darkVelocity, norm_mul, norm_div, norm_I, norm_ofNat, cost]
  ring

theorem dark_speed_le (x : State) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖darkVelocity x u‖ ≤ cost x / Real.sqrt 2 := by
  have hi := dark_speed_identity x u
  have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hh : 0 ≤ (1 - ‖u‖ ^ 2) * ‖r1 x‖ ^ 2 * ‖r2 x‖ ^ 2 / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg _))
      (sq_nonneg _)) (by norm_num)
  have hs : (Real.sqrt 2)^2 = 2 := by norm_num
  have hp : 0 < Real.sqrt 2 := by positivity
  apply (le_div_iff₀ hp).mpr
  have hn := norm_nonneg (darkVelocity x u)
  have hc := cost_nonneg x
  nlinarith [sq_nonneg (2 * ‖r1 x‖^2 - ‖r2 x‖^2), sq_nonneg (‖darkVelocity x u‖ * Real.sqrt 2 + cost x)]

theorem dark_initial : dark x0 = 0 := by
  change (1 : ℂ) * 0 - (Real.sqrt 2 : ℂ) * 1 * 0 = 0
  ring
theorem dark_terminal (x : State) (hx : x ∈ XCZ) : dark x = 0 := by
  simp [dark, hx.2.1, hx.2.2.1]

theorem dark_reverse_triangle (x : State) :
    |‖g1 x‖ * ‖r2 x‖ - Real.sqrt 2 * ‖g2 x‖ * ‖r1 x‖| ≤ ‖dark x‖ := by
  have h := abs_norm_sub_norm_le (g1 x * r2 x) ((Real.sqrt 2 : ℂ) * g2 x * r1 x)
  simpa only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)] using h

private def amplitudeMap (i j : Fin 8) : State →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i) +
    (ContinuousLinearMap.proj j : State →L[ℝ] ℝ).smulRight I

private theorem amplitudeMap_apply (i j : Fin 8) (x : State) :
    amplitudeMap i j x = (⟨x i, x j⟩ : ℂ) := by
  simp [amplitudeMap, Complex.mk_eq_add_mul_I, Complex.real_smul]

private theorem amplitude_ac (P : PhysicalSegment) (i j : Fin 8) :
    AbsolutelyContinuousOnInterval (fun t => (⟨P.path t i, P.path t j⟩ : ℂ)) 0 P.duration := by
  have h := (amplitudeMap i j).lipschitz.comp_lipschitzOnWith P.path_lipschitzOn
  rw [← uIcc_of_le P.duration_nonneg] at h
  simpa only [Function.comp_def, amplitudeMap_apply] using h.absolutelyContinuousOnInterval

theorem dark_ac (P : PhysicalSegment) :
    AbsolutelyContinuousOnInterval (fun t => dark (P.path t)) 0 P.duration := by
  have h1 := (amplitude_ac P 0 1).fun_smul (amplitude_ac P 6 7)
  have h2 := ((amplitude_ac P 4 5).const_smul (Real.sqrt 2 : ℂ)).fun_smul
    (amplitude_ac P 2 3)
  simpa only [dark, g1, r1, g2, r2, smul_eq_mul] using h1.sub h2

private theorem dark_components_ac (P : PhysicalSegment) :
    AbsolutelyContinuousOnInterval (fun t => (dark (P.path t)).re) 0 P.duration ∧
    AbsolutelyContinuousOnInterval (fun t => (dark (P.path t)).im) 0 P.duration := by
  have h (i : Fin 8) : AbsolutelyContinuousOnInterval (fun t => P.path t i) 0 P.duration := by
    have hi := (ContinuousLinearMap.proj i : State →L[ℝ] ℝ).lipschitz.comp_lipschitzOnWith
      P.path_lipschitzOn
    rw [← uIcc_of_le P.duration_nonneg] at hi
    exact hi.absolutelyContinuousOnInterval
  constructor
  · have hh := ((h 0).fun_mul (h 6) |>.sub ((h 1).fun_mul (h 7))).sub
      (((h 4).fun_mul (h 2) |>.sub ((h 5).fun_mul (h 3))).const_mul (Real.sqrt 2))
    simpa [dark, g1, r1, g2, r2, mul_sub, mul_add, mul_assoc, Pi.sub_apply] using hh
  · have hh := ((h 0).fun_mul (h 7) |>.add ((h 1).fun_mul (h 6))).sub
      (((h 4).fun_mul (h 3) |>.add ((h 5).fun_mul (h 2))).const_mul (Real.sqrt 2))
    simpa [dark, g1, r1, g2, r2, mul_sub, mul_add, mul_assoc, Pi.sub_apply, Pi.add_apply] using hh

/-- Integrated speed bound on any physical subinterval, including stalls
and switching times. Absolute continuity comes from the integral model. -/
theorem dark_increment (P : PhysicalSegment) {a b : ℝ}
    (ha : a ∈ Icc 0 P.duration) (hb : b ∈ Icc 0 P.duration) (hab : a ≤ b) :
    ‖dark (P.path b) - dark (P.path a)‖ ≤
      (∫ t in a..b, cost (P.path t)) / Real.sqrt 2 := by
  have hre := (dark_components_ac P).1.mono (uIcc_subset_uIcc_of_mem ha hb)
  have him := (dark_components_ac P).2.mono (uIcc_subset_uIcc_of_mem ha hb)
  let f := fun t => dark (P.path t)
  let d := fun t => ((deriv (fun s => (f s).re) t : ℝ) : ℂ) +
    ((deriv (fun s => (f s).im) t : ℝ) : ℂ) * I
  have hir : IntervalIntegrable (fun t => ((deriv (fun s => (f s).re) t : ℝ) : ℂ)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hre.intervalIntegrable_deriv.1,
      Complex.ofRealCLM.integrable_comp hre.intervalIntegrable_deriv.2⟩
  have hii : IntervalIntegrable (fun t => ((deriv (fun s => (f s).im) t : ℝ) : ℂ)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp him.intervalIntegrable_deriv.1,
      Complex.ofRealCLM.integrable_comp him.intervalIntegrable_deriv.2⟩
  have hid : IntervalIntegrable d volume a b := hir.add (hii.mul_const I)
  have he : (∫ t in a..b, d t) = dark (P.path b) - dark (P.path a) := by
    rw [intervalIntegral.integral_add hir (hii.mul_const I), intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    rw [hre.integral_deriv_eq_sub, him.integral_deriv_eq_sub]
    simp only [ofReal_sub]
    apply Complex.ext <;> simp
  have hcost := P.cost_intervalIntegrable.mono_set (uIcc_subset_uIcc_of_mem ha hb)
  rw [← he]
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_mono_ae_restrict hab hid.norm
    (hcost.div_const _)
  have hd := P.ae_hasDerivAt_path.filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono (Icc_subset_Icc ha.1 hb.2) le_rfl))
  filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht htab
  have hr := reCLM.hasFDerivAt.comp_hasDerivAt t (dark_deriv ht)
  have hi := imCLM.hasFDerivAt.comp_hasDerivAt t (dark_deriv ht)
  change HasDerivAt (fun s => (dark (P.path s)).re) (darkVelocity (P.path t) (P.control t)).re t at hr
  change HasDerivAt (fun s => (dark (P.path s)).im) (darkVelocity (P.path t) (P.control t)).im t at hi
  change ‖((deriv (fun s => (dark (P.path s)).re) t : ℝ) : ℂ) +
    ((deriv (fun s => (dark (P.path s)).im) t : ℝ) : ℂ) * I‖ ≤ _
  rw [hr.deriv, hi.deriv]
  rw [Complex.re_add_im]
  exact dark_speed_le _ _ (P.control_bound t ⟨ha.1.trans htab.1, htab.2.trans hb.2⟩)

/-- Both endpoints matter: the second inequality charges the return to the
zero-excitation face, not just the initial excursion. -/
theorem dark_budget (γ : ActivePulse) {s : ℝ} (hs : s ∈ Icc 0 γ.S) :
    ‖dark (γ.x s)‖ ≤ min (γ.cumI s) (γ.exposure - γ.cumI s) / Real.sqrt 2 := by
  let P := (toLab γ).toSegment
  have h0 : (0 : ℝ) ∈ Icc 0 P.duration := ⟨le_rfl, γ.S_nonneg⟩
  have hS : γ.S ∈ Icc 0 P.duration := ⟨γ.S_nonneg, le_rfl⟩
  have hi : dark (γ.x 0) = 0 := by
    change dark ((toLab γ).x 0) = 0
    rw [(toLab γ).initial]
    exact dark_initial
  have ht : dark (γ.x γ.S) = 0 := dark_terminal _ γ.terminal
  have hf := dark_increment P h0 hs hs.1
  have hr := dark_increment P hs hS hs.2
  change ‖dark (γ.x s) - dark (γ.x 0)‖ ≤ _ at hf
  change ‖dark (γ.x γ.S) - dark (γ.x s)‖ ≤ _ at hr
  rw [hi, sub_zero] at hf
  rw [ht, zero_sub, norm_neg] at hr
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
  rw [← min_div_div_right (by positivity : (0 : ℝ) ≤ Real.sqrt 2)]
  exact le_min hf hr

/-- The population expression is a necessary condition, not a replacement
for the phase-sensitive common-drive dynamics. -/
theorem dark_population (x : State) (hx : x ∈ Xset) :
    |Real.sqrt ((1 - ‖r1 x‖^2) * ‖r2 x‖^2) -
      Real.sqrt (2 * (1 - ‖r2 x‖^2) * ‖r1 x‖^2)| ≤ ‖dark x‖ := by
  have hg1 : 1 - ‖r1 x‖^2 = ‖g1 x‖^2 := by linarith [hx.1]
  have hg2 : 1 - ‖r2 x‖^2 = ‖g2 x‖^2 := by linarith [hx.2]
  rw [hg1, hg2, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_mul (mul_nonneg (by norm_num) (sq_nonneg _)),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    dark_reverse_triangle x

/-- A whole exposure interval has a common budget. `H` bounds exposure,
never duration. The conclusion includes equality at box boundaries. -/
theorem dark_interval_budget (γ : ActivePulse) {s H l r : ℝ}
    (hs : s ∈ Icc 0 γ.S) (hH : γ.exposure ≤ H)
    (hl : l ≤ γ.cumI s) (hr : γ.cumI s ≤ r) :
    2 * ‖dark (γ.x s)‖^2 ≤ (min r (H-l))^2 := by
  have hright : γ.exposure - γ.cumI s ≤ H-l := by linarith
  have h := (dark_budget γ hs).trans
    (div_le_div_of_nonneg_right (min_le_min hr hright) (Real.sqrt_nonneg 2))
  have hp : 0 < Real.sqrt 2 := by positivity
  have hmul := (le_div_iff₀ hp).mp h
  have hn : 0 ≤ ‖dark (γ.x s)‖ * Real.sqrt 2 := mul_nonneg (norm_nonneg _) hp.le
  have hsquare := (sq_le_sq₀ hn (hn.trans hmul)).mpr hmul
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def populationGap (p q : ℝ) : ℝ :=
  Real.sqrt ((1-p)*q) - Real.sqrt (2*(1-q)*p)

/-- The signed gap decreases with the first population and increases with
the second. These directions fix which two corners may exclude a box. -/
theorem populationGap_mono {p p' q q' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') (hp' : p' ≤ 1)
    (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1) :
    populationGap p' q ≤ populationGap p q' := by
  apply sub_le_sub
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul (by linarith) hqq hq (by linarith)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul (by linarith) hpp hp (by linarith)

/-- Rational strict inequalities imply a strict squared gap. Thus equality
in either test is never used to exclude a population box. -/
theorem rational_gap_test {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hν : 0 < A+B-R^2/2) (htest : 4*A*B < (A+B-R^2/2)^2) :
    R^2 < 2*(Real.sqrt A - Real.sqrt B)^2 := by
  have hprod : (Real.sqrt A * Real.sqrt B)^2 = A*B := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hlt : 2*(Real.sqrt A * Real.sqrt B) < A+B-R^2/2 := by
    by_contra hn
    have hle := le_of_not_gt hn
    have hsq := (sq_le_sq₀ hν.le (by positivity : 0 ≤ 2*(Real.sqrt A*Real.sqrt B))).mpr hle
    nlinarith
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- A positive signed lower corner, or a negative signed upper corner,
controls the absolute gap at every point of the closed rectangle. -/
theorem population_box_gap {a b c d p q : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hc : 0 ≤ c) (hd : d ≤ 1)
    (hp : p ∈ Icc a b) (hq : q ∈ Icc c d) :
    (0 ≤ populationGap b c → populationGap b c ≤ |populationGap p q|) ∧
    (populationGap a d ≤ 0 → -populationGap a d ≤ |populationGap p q|) := by
  have hlo := populationGap_mono (ha.trans hp.1) hp.2 hb hc hq.1 (hq.2.trans hd)
  have hhi := populationGap_mono ha hp.1 (hp.2.trans hb) (hc.trans hq.1) hq.2 hd
  constructor
  · intro _
    exact hlo.trans (le_abs_self _)
  · intro _
    exact (neg_le_neg hhi).trans (neg_le_abs _)

/-- The two strict rational corner tests used by the dark checker. -/
def DarkBoxExcluded (a b c d R : ℝ) : Prop :=
  let test := fun A B => B < A ∧ 0 < A+B-R^2/2 ∧ 4*A*B < (A+B-R^2/2)^2
  test ((1-b)*c) (2*(1-c)*b) ∨ test (2*(1-d)*a) ((1-a)*d)

/-- The checker's rational tests exclude actual integral-model trajectories,
not merely points of a phase-free relaxation. -/
theorem dark_box_excludes (γ : ActivePulse) {s H l r a b c d : ℝ}
    (hs : s ∈ Icc 0 γ.S) (hH : γ.exposure ≤ H)
    (hl : l ≤ γ.cumI s) (hr : γ.cumI s ≤ r)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hc : 0 ≤ c) (hd : d ≤ 1)
    (hp : ‖r1 (γ.x s)‖^2 ∈ Icc a b) (hq : ‖r2 (γ.x s)‖^2 ∈ Icc c d)
    (hex : DarkBoxExcluded a b c d (min r (H-l))) : False := by
  have hab : a ≤ b := hp.1.trans hp.2
  have hcd : c ≤ d := hq.1.trans hq.2
  have hphys := dark_population (γ.x s) (γ.x_mem s hs)
  change |populationGap (‖r1 (γ.x s)‖^2) (‖r2 (γ.x s)‖^2)| ≤ _ at hphys
  have hbudget := dark_interval_budget γ hs hH hl hr
  have hcorners := population_box_gap ha hb hc hd hp hq
  have impossible (z : ℝ) (hz : 0 ≤ z) (hle : z ≤ ‖dark (γ.x s)‖)
      (hstrict : (min r (H-l))^2 < 2*z^2) : False := by
    have hsq := (sq_le_sq₀ hz (norm_nonneg _)).mpr hle
    linarith
  rcases hex with ⟨hsign, hν, htest⟩ | ⟨hsign, hν, htest⟩
  · have hz : 0 ≤ populationGap b c := sub_nonneg.mpr (Real.sqrt_le_sqrt hsign.le)
    apply impossible _ hz ((hcorners.1 hz).trans hphys)
    exact rational_gap_test (mul_nonneg (by linarith) hc)
      (mul_nonneg (by linarith) (ha.trans hab)) hν htest
  · have hz : populationGap a d ≤ 0 := sub_nonpos.mpr (Real.sqrt_le_sqrt hsign.le)
    apply impossible _ (neg_nonneg.mpr hz) ((hcorners.2 hz).trans hphys)
    have h := rational_gap_test (mul_nonneg (by linarith) ha)
      (mul_nonneg (by linarith) (hc.trans hcd)) hν htest
    simpa only [populationGap, neg_sub] using h

end LowerBoundCZ.Certification.Slack
