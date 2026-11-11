module
public import RequestProject.AppendixE.PhysicalSegment

/-!
# Sharp cubic exposure bound for physical segments

For a `PhysicalSegment` starting on the zero-cost face `F`, the rydberg
coordinates satisfy `|r₁(s)| ≤ s/2`, `|r₂(s)| ≤ √2 s/2`, hence
`c(x(s)) ≤ s²/4`; cumulative exposure is at most `s³/12`, and total
exposure at most `D³/12`.  Time reversal yields the same total bound
for a segment ending on `F`, with running cost at most `(D−s)²/4`.
These are bounds for *supplied* segments; no controllability or
steering-existence claim is made.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-! ## Sharp velocity bounds for the rydberg channel -/

theorem norm_fC_rydberg1_le {x : State} (hx : x ∈ Xset) {u : ℂ}
    (hu : ‖u‖ ≤ 1) : ‖fC x u 1‖ ≤ 1/2 := by
  rw [show ‖fC x u 1‖ = 2⁻¹ * (‖u‖ * ‖g1 x‖) by simp [fC]]
  have hp : ‖u‖ * ‖g1 x‖ ≤ 1 * 1 :=
    mul_le_mul hu (norm_g1_le_one hx) (norm_nonneg _) (by norm_num)
  linarith

theorem norm_fC_rydberg2_le {x : State} (hx : x ∈ Xset) {u : ℂ}
    (hu : ‖u‖ ≤ 1) : ‖fC x u 3‖ ≤ Real.sqrt 2 / 2 := by
  rw [show ‖fC x u 3‖ = 2⁻¹ * (Real.sqrt 2 * (‖u‖ * ‖g2 x‖)) by
    simp [fC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), mul_assoc]]
  have hp : ‖u‖ * ‖g2 x‖ ≤ 1 :=
    (mul_le_mul hu (norm_g2_le_one hx) (norm_nonneg _)
      (by norm_num)).trans_eq (mul_one 1)
  have hv : Real.sqrt 2 * (‖u‖ * ‖g2 x‖) ≤ Real.sqrt 2 * 1 :=
    mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg 2)
  linarith

/-! ## Rydberg-coordinate integral equations -/

/-- Real-linear continuous map extracting the complex `r₁` coordinate. -/
private def r1CLM : State →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (2 : Fin 8)) +
    (Complex.I : ℂ) •
      Complex.ofRealCLM.comp (ContinuousLinearMap.proj (3 : Fin 8))

/-- Real-linear continuous map extracting the complex `r₂` coordinate. -/
private def r2CLM : State →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (6 : Fin 8)) +
    (Complex.I : ℂ) •
      Complex.ofRealCLM.comp (ContinuousLinearMap.proj (7 : Fin 8))

private theorem r1CLM_apply (x : State) : r1CLM x = r1 x := by
  apply Complex.ext <;> simp [r1CLM, r1]

private theorem r2CLM_apply (x : State) : r2CLM x = r2 x := by
  apply Complex.ext <;> simp [r2CLM, r2]

private theorem r1CLM_vf (x : State) (u : ℂ) :
    r1CLM (vf x u) = fC x u 1 := by
  rw [r1CLM_apply]
  apply Complex.ext <;> simp [r1, vf]

private theorem r2CLM_vf (x : State) (u : ℂ) :
    r2CLM (vf x u) = fC x u 3 := by
  rw [r2CLM_apply]
  apply Complex.ext <;> simp [r2, vf]

namespace PhysicalSegment

variable (P : PhysicalSegment)

theorem rydberg_integralEquations {s : ℝ} (hs : s ∈ Set.Icc 0 P.duration) :
    r1 (P.path s) = r1 (P.path 0) +
      ∫ t in (0 : ℝ)..s, fC (P.path t) (P.control t) 1 ∧
    r2 (P.path s) = r2 (P.path 0) +
      ∫ t in (0 : ℝ)..s, fC (P.path t) (P.control t) 3 := by
  have hint : IntervalIntegrable (fun t => vf (P.path t) (P.control t))
      volume 0 s :=
    P.velocity_integrable_subinterval
      (Set.left_mem_Icc.mpr P.duration_nonneg) hs
  have h1 := r1CLM.intervalIntegral_comp_comm hint
  have h2 := r2CLM.intervalIntegral_comp_comm hint
  rw [show (fun t => r1CLM (vf (P.path t) (P.control t))) =
      fun t => fC (P.path t) (P.control t) 1 from
    funext fun t => r1CLM_vf _ _] at h1
  rw [show (fun t => r2CLM (vf (P.path t) (P.control t))) =
      fun t => fC (P.path t) (P.control t) 3 from
    funext fun t => r2CLM_vf _ _] at h2
  constructor
  · have hp := P.integralEquation s hs
    conv_lhs => rw [hp]
    simp only [← r1CLM_apply, map_add]
    congr 1
    exact h1.symm
  · have hp := P.integralEquation s hs
    conv_lhs => rw [hp]
    simp only [← r2CLM_apply, map_add]
    congr 1
    exact h2.symm

theorem norm_r1_le_time (hstart : P.path 0 ∈ Fface) {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) : ‖r1 (P.path s)‖ ≤ s/2 := by
  obtain ⟨h1, -⟩ := P.rydberg_integralEquations hs
  rw [h1, hstart.2.1, zero_add]
  have hb : ∀ t ∈ Set.uIoc (0:ℝ) s, ‖fC (P.path t) (P.control t) 1‖ ≤ 1/2 := by
    intro t ht
    have htI : t ∈ Set.Icc 0 P.duration := mem_Icc_of_mem_uIoc hs ht
    exact norm_fC_rydberg1_le (P.path_mem t htI) (P.control_bound t htI)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero] at hbound
  calc ‖∫ t in (0:ℝ)..s, fC (P.path t) (P.control t) 1‖
      ≤ (1/2) * |s| := hbound
    _ = s/2 := by rw [abs_of_nonneg hs.1]; ring

theorem norm_r2_le_time (hstart : P.path 0 ∈ Fface) {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) :
    ‖r2 (P.path s)‖ ≤ Real.sqrt 2 * s / 2 := by
  obtain ⟨-, h2⟩ := P.rydberg_integralEquations hs
  rw [h2, hstart.2.2, zero_add]
  have hb : ∀ t ∈ Set.uIoc (0:ℝ) s,
      ‖fC (P.path t) (P.control t) 3‖ ≤ Real.sqrt 2 / 2 := by
    intro t ht
    have htI : t ∈ Set.Icc 0 P.duration := mem_Icc_of_mem_uIoc hs ht
    exact norm_fC_rydberg2_le (P.path_mem t htI) (P.control_bound t htI)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero] at hbound
  calc ‖∫ t in (0:ℝ)..s, fC (P.path t) (P.control t) 3‖
      ≤ (Real.sqrt 2 / 2) * |s| := hbound
    _ = Real.sqrt 2 * s / 2 := by rw [abs_of_nonneg hs.1]; ring

theorem cost_le_time_sq_div_four (hstart : P.path 0 ∈ Fface) {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) : cost (P.path s) ≤ s^2/4 := by
  have hr1 := P.norm_r1_le_time hstart hs
  have hr2 := P.norm_r2_le_time hstart hs
  have hr1sq : ‖r1 (P.path s)‖ ^ 2 ≤ (s/2)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hr1 2
  have hr2sq : ‖r2 (P.path s)‖ ^ 2 ≤ (Real.sqrt 2 * s / 2)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hr2 2
  have hs1 : (s/2)^2 = s^2/4 := by ring
  have hs2 : (Real.sqrt 2 * s / 2)^2 = s^2/2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hs1] at hr1sq
  rw [hs2] at hr2sq
  show (2 * ‖r1 (P.path s)‖^2 + ‖r2 (P.path s)‖^2)/4 ≤ s^2/4
  linarith

theorem cumulative_exposure_le_cube_div_twelve (hstart : P.path 0 ∈ Fface)
    {s : ℝ} (hs : s ∈ Set.Icc 0 P.duration) :
    (∫ t in (0 : ℝ)..s, cost (P.path t)) ≤ s^3/12 := by
  have hic : IntervalIntegrable (fun t => cost (P.path t)) volume 0 s :=
    P.cost_intervalIntegrable.mono_set
      (uIcc_subset_uIcc_of_mem (Set.left_mem_Icc.mpr P.duration_nonneg) hs)
  have hi_pow : IntervalIntegrable (fun t : ℝ => t^2/4) volume 0 s :=
    (by continuity : Continuous fun t : ℝ => t^2/4).intervalIntegrable 0 s
  have hm := intervalIntegral.integral_mono_on hs.1 hic hi_pow
    (fun t ht => P.cost_le_time_sq_div_four hstart
      ⟨ht.1, le_trans ht.2 hs.2⟩)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) s,
      HasDerivAt (fun x => x^3/12) (t^2/4) t := by
    intro t _
    have h := (hasDerivAt_pow 3 t).div_const 12
    have hsimpl : (↑(3 : ℕ) : ℝ) * t ^ (3 - 1) / 12 = t^2/4 := by
      field_simp
      ring
    rwa [hsimpl] at h
  have hp2 : (∫ t in (0:ℝ)..s, t^2/4) = s^3/12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi_pow]
    simp
  exact hm.trans_eq hp2

theorem exposure_le_cube_div_twelve (hstart : P.path 0 ∈ Fface) :
    P.exposure ≤ P.duration^3/12 :=
  P.cumulative_exposure_le_cube_div_twelve hstart
    (Set.right_mem_Icc.mpr P.duration_nonneg)

theorem cost_le_remaining_time_sq_div_four (hend : P.path P.duration ∈ Fface)
    {s : ℝ} (hs : s ∈ Set.Icc 0 P.duration) :
    cost (P.path s) ≤ (P.duration - s)^2/4 := by
  have hstart : P.reverse.path 0 ∈ Fface := by
    rw [reverse_path, sub_zero]
    exact hend
  have hmem : P.duration - s ∈ Set.Icc 0 P.reverse.duration := by
    rw [reverse_duration]
    exact mem_Icc_sub hs
  have h := P.reverse.cost_le_time_sq_div_four hstart hmem
  rwa [reverse_path, sub_sub_self] at h

theorem exposure_le_cube_div_twelve_of_end (hend : P.path P.duration ∈ Fface) :
    P.exposure ≤ P.duration^3/12 := by
  have hstart : P.reverse.path 0 ∈ Fface := by
    rw [reverse_path, sub_zero]
    exact hend
  have h := P.reverse.exposure_le_cube_div_twelve hstart
  rwa [reverse_exposure, reverse_duration] at h

end PhysicalSegment

end CZExposure
