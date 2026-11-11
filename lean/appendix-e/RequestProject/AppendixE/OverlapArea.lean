import Mathlib

noncomputable section

namespace CZExposure

open MeasureTheory Set Filter

/-- Nonnegative continuous tests suffice to compare finite real measures. -/
theorem measure_le_of_nonnegative_tests {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      (∀ x, 0 ≤ f x) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  have hk : ∀ K : Set ℝ, IsCompact K → μ K ≤ ν K := by
    intro K hK
    rw [hK.measure_eq_biInf_integral_hasCompactSupport ν]
    simp only [le_iInf_iff]
    intro f hc hs he hn
    exact ((hc.integrable_of_hasCompactSupport hs).measure_le_integral
      (Eventually.of_forall hn) (fun x hx => (he hx).ge)).trans
      (ENNReal.ofReal_le_ofReal (h f hc hs hn))
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact]
  exact iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => (hk K hK).trans (measure_mono hKs)

/-- The primitive of a continuous test is C¹, with its actual derivative. -/
theorem continuous_primitive {f : ℝ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (fun x => ∫ y in (0 : ℝ)..x, f y) ∧
      ∀ x, HasDerivAt (fun x => ∫ y in (0 : ℝ)..x, f y) (f x) x := by
  have hd : ∀ x, HasDerivAt (fun x => ∫ y in (0 : ℝ)..x, f y) (f x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt, ?_⟩, hd⟩
  simpa only [funext (fun x => (hd x).deriv)] using hf

/-- Counting overlap progress with absolute speed dominates Lebesgue
measure between the endpoints, even when the curve backtracks. -/
theorem overlap_area_measure {q : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcomp : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F →
      AbsolutelyContinuousOnInterval (fun t => F (q t)) 0 T)
    (h0 : q 0 = 1) (h1 : q T = -1) :
    volume.restrict (Icc (-1 : ℝ) 1) ≤
      Measure.map q ((volume.restrict (Icc 0 T)).withDensity
        (fun t => ENNReal.ofReal |deriv q t|)) := by
  have hac : AbsolutelyContinuousOnInterval q 0 T := hcomp id contDiff_id
  have hqi : IntegrableOn (fun t => |deriv q t|) (Icc 0 T) volume := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hac.intervalIntegrable_deriv.norm
  let ρ := (volume.restrict (Icc 0 T)).withDensity (fun t => ENNReal.ofReal |deriv q t|)
  haveI : IsFiniteMeasure ρ := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hqi (Eventually.of_forall (fun t => abs_nonneg _))]
    exact ENNReal.ofReal_ne_top)
  have hqm : AEMeasurable q ρ := by
    apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
    simpa only [uIcc_of_le hT] using
      (hac.continuousOn.aestronglyMeasurable measurableSet_uIcc).aemeasurable
  apply measure_le_of_nonnegative_tests
  intro f hf hfc hfn
  rw [integral_map hqm hf.aestronglyMeasurable]
  dsimp only [ρ]
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_deriv q).abs.ennreal_ofReal) (Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
  let F : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, f y
  obtain ⟨hF, hFd⟩ := continuous_primitive hf
  have hfac := hcomp F hF
  have hprod : IntervalIntegrable (fun t => |deriv q t| * f (q t)) volume 0 T := by
    simpa only [Real.norm_eq_abs] using hac.intervalIntegrable_deriv.norm.mul_continuousOn
      (hf.comp_continuousOn hac.continuousOn)
  have hle : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      -deriv (fun s => F (q s)) t ≤ |deriv q t| * f (q t) := by
    have hdiff := hac.ae_differentiableAt
    filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem measurableSet_Icc] with t ht hi
    have hqt := ht (by rwa [uIcc_of_le hT])
    have hd := (hFd (q t)).comp t hqt.hasDerivAt
    change HasDerivAt (fun s => F (q s)) (f (q t) * deriv q t) t at hd
    rw [hd.deriv]
    nlinarith [neg_le_abs (deriv q t), hfn (q t)]
  have hi := intervalIntegral.integral_mono_ae_restrict hT
    hfac.intervalIntegrable_deriv.neg hprod hle
  simp only [Pi.neg_apply] at hi
  rw [intervalIntegral.integral_neg, hfac.integral_deriv_eq_sub, h0, h1, neg_sub] at hi
  have he : F 1 - F (-1) = ∫ y in (-1 : ℝ)..1, f y := by
    exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable (μ := volume) 0 1)
      (hf.intervalIntegrable (μ := volume) 0 (-1)))
  rw [he, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le hT] at hi
  simpa only [integral_Icc_eq_integral_Ioc] using hi

/-- A measurable nonnegative density needs no smoothness or boundedness.
The finite cost proves its integrability as well as the crossing bound. -/
theorem overlap_weighted_bound {q c f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcomp : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F →
      AbsolutelyContinuousOnInterval (fun t => F (q t)) 0 T)
    (h0 : q 0 = 1) (h1 : q T = -1)
    (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hc : IntervalIntegrable c volume 0 T)
    (hcn : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), 0 ≤ c t)
    (hbound : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), f (q t) * |deriv q t| ≤ c t) :
    IntervalIntegrable f volume (-1) 1 ∧ (∫ x in (-1 : ℝ)..1, f x) ≤ ∫ t in (0 : ℝ)..T, c t := by
  have hac : AbsolutelyContinuousOnInterval q 0 T := hcomp id contDiff_id
  let ρ := (volume.restrict (Icc 0 T)).withDensity (fun t => ENNReal.ofReal |deriv q t|)
  have hqm : AEMeasurable q ρ := by
    apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
    simpa only [uIcc_of_le hT] using
      (hac.continuousOn.aestronglyMeasurable measurableSet_uIcc).aemeasurable
  have hci := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hc
  have hl : (∫⁻ x in Icc (-1 : ℝ) 1, ENNReal.ofReal (f x)) ≤
      ENNReal.ofReal (∫ t in Icc (0 : ℝ) T, c t) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂Measure.map q ρ :=
        lintegral_mono' (overlap_area_measure hT hcomp h0 h1) le_rfl
      _ = ∫⁻ t, ENNReal.ofReal (f (q t)) ∂ρ :=
        lintegral_map' hf.ennreal_ofReal.aemeasurable hqm
      _ = ∫⁻ t in Icc 0 T, ENNReal.ofReal |deriv q t| * ENNReal.ofReal (f (q t)) :=
        lintegral_withDensity_eq_lintegral_mul₀'
          ((measurable_deriv q).abs.ennreal_ofReal.aemeasurable)
          (hf.ennreal_ofReal.comp_aemeasurable hqm)
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (c t) := by
        apply lintegral_mono_ae
        filter_upwards [hbound] with t ht
        rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
        exact ENNReal.ofReal_le_ofReal ht
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hci hcn).symm
  have hfi : IntegrableOn f (Icc (-1 : ℝ) 1) volume :=
    ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hfn)).mpr
        (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hfn)] at hl
  have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hcn)).mp hl
  simpa only [intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hr

end CZExposure
