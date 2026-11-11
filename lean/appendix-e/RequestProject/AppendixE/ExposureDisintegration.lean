module
public import RequestProject.AppendixE.ControlAveraging
public import RequestProject.AppendixE.ExposureCompactness
public import RequestProject.AppendixE.Relaxation
public import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Disintegration of exposure records over the control (Appendix E 2, Step 4)

Disintegrating an exposure record `ν` over its `Y`-marginal gives, for
`ν.fst`-almost every `y`, a probability measure `ν.condKernel y` on the controls,
supported on the closed unit disk because `ν` is supported on `Y × U`. The mean
`∫ u, u ∂(ν.condKernel y)` is then an admissible control `ν.fst`-a.e.; replacing
it by `0` off the disk gives a globally measurable disk-valued control `ū(y)`
that agrees with the mean almost everywhere. Since `u ↦ B(y, u)` is
`ℝ`-linear (see `ControlAveraging`), the averaged field `B(y, ū(y))` satisfies the
same balance equation with the same total mass. Extracting an actual pulse from
the averaged flow is not part of this step.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set
open scoped ProbabilityTheory

/-- The conditional mean control of an exposure record at `y`. -/
def exposureMeanControl (ν : Measure ExposureAmbient) [IsFiniteMeasure ν]
    (y : Fin 11 → ℝ) : ℂ := ∫ u, u ∂(ν.condKernel y)

/-- A globally defined admissible control: the conditional mean where it lies in
the closed unit disk (which holds `ν.fst`-a.e.), and `0` elsewhere. -/
def exposureAdmissibleControl (ν : Measure ExposureAmbient) [IsFiniteMeasure ν]
    (y : Fin 11 → ℝ) : ℂ :=
  if ‖exposureMeanControl ν y‖ ≤ 1 then exposureMeanControl ν y else 0

theorem measurable_exposureMeanControl (ν : Measure ExposureAmbient) [IsFiniteMeasure ν] :
    Measurable (exposureMeanControl ν) :=
  (stronglyMeasurable_id.integral_kernel (κ := ν.condKernel)).measurable

theorem measurable_exposureAdmissibleControl (ν : Measure ExposureAmbient)
    [IsFiniteMeasure ν] : Measurable (exposureAdmissibleControl ν) := by
  unfold exposureAdmissibleControl
  exact Measurable.ite (measurableSet_le (measurable_exposureMeanControl ν).norm
    measurable_const) (measurable_exposureMeanControl ν) measurable_const

theorem norm_exposureAdmissibleControl_le_one (ν : Measure ExposureAmbient)
    [IsFiniteMeasure ν] (y : Fin 11 → ℝ) :
    ‖exposureAdmissibleControl ν y‖ ≤ 1 := by
  unfold exposureAdmissibleControl
  split_ifs with h
  · exact h
  · rw [norm_zero]
    exact zero_le_one

/-- The marginal of an exposure record is supported on `Y`. -/
theorem exposure_marginal_support {ν : Measure ExposureAmbient}
    (hν : IsExposureRecord ν) : ν.fst Ysetᶜ = 0 := by
  rw [Measure.fst_apply isCompact_Yset.isClosed.measurableSet.compl]
  refine measure_mono_null ?_ hν.2.1
  exact fun p hp hmem => hp hmem.1

/-- Since `ν` is supported on `Y × U`, the conditional control measures are
supported on the closed unit disk `ν.fst`-a.e. -/
theorem exposure_condKernel_disk_support {ν : Measure ExposureAmbient}
    [IsFiniteMeasure ν] (hν : IsExposureRecord ν) :
    ∀ᵐ y ∂(ν.fst), ∀ᵐ u ∂(ν.condKernel y), ‖u‖ ≤ 1 := by
  have hdom : ∀ᵐ p ∂ν, p ∈ exposureDomain := mem_ae_iff.mpr hν.2.1
  have key : ∀ᵐ p ∂(ν.fst ⊗ₘ ν.condKernel), ‖p.2‖ ≤ 1 := by
    rw [ν.disintegrate ν.condKernel]
    exact hdom.mono fun p hp => mem_closedBall_zero_iff.mp hp.2
  exact Measure.ae_ae_of_ae_compProd key

/-- The admissible control equals the conditional mean `ν.fst`-a.e.: on the
a.e. disk the `if` takes the mean branch. -/
theorem exposureAdmissibleControl_eq_mean_ae {ν : Measure ExposureAmbient}
    [IsFiniteMeasure ν] (hν : IsExposureRecord ν) :
    exposureAdmissibleControl ν =ᵐ[ν.fst] exposureMeanControl ν := by
  filter_upwards [exposure_condKernel_disk_support hν] with y hy
  have h : ‖exposureMeanControl ν y‖ ≤ 1 := norm_mean_control_le_one hy
  unfold exposureAdmissibleControl
  rw [if_pos h]

/-- The joint balance integrand is integrable: it is measurable and bounded on
the compact support of the record. -/
theorem integrable_exposure_balance {ν : Measure ExposureAmbient}
    (hν : IsExposureRecord ν) {ψ : (Fin 11 → ℝ) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) :
    Integrable (fun p : ExposureAmbient => fderiv ℝ ψ p.1 (Bfield p.1 p.2)) ν := by
  letI : IsFiniteMeasure ν := hν.1
  obtain ⟨M, hM⟩ := isCompact_Yset.exists_bound_of_continuousOn
    (hψ.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨K, hK0, hK⟩ := Bfield_bounded
  have hdom : ∀ᵐ p ∂ν, p ∈ exposureDomain := mem_ae_iff.mpr hν.2.1
  refine (integrable_const (M * K)).mono'
    (measurable_balance_integrand hψ).aestronglyMeasurable ?_
  filter_upwards [hdom] with p hp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p.1 hp.1)
  calc ‖fderiv ℝ ψ p.1 (Bfield p.1 p.2)‖
      ≤ ‖fderiv ℝ ψ p.1‖ * ‖Bfield p.1 p.2‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * K := mul_le_mul (hM p.1 hp.1)
        (hK p.1 hp.1 p.2 (mem_closedBall_zero_iff.mp hp.2)) (norm_nonneg _) hM0

/-- A measurable function bounded `ν`-a.e. by a constant is integrable over a
finite measure. -/
private theorem integrable_of_ae_bound {E : Type*} [NormedAddCommGroup E]
    {ν : Measure (Fin 11 → ℝ)} [IsFiniteMeasure ν] {f : (Fin 11 → ℝ) → E}
    (hf : AEStronglyMeasurable f ν) {C : ℝ} (hC : ∀ᵐ y ∂ν, ‖f y‖ ≤ C) :
    Integrable f ν :=
  (integrable_const C).mono' hf hC

/-- At `ν.fst`-a.e. `y`, the inner balance integral equals the integrand at the
averaged admissible control: `u ↦ Dψ(y)(B(y, u))` is linear and the admissible
control equals the conditional mean there. -/
private theorem integral_inner_balance_eq {ν : Measure ExposureAmbient}
    [IsFiniteMeasure ν] (hν : IsExposureRecord ν) (ψ : (Fin 11 → ℝ) → ℝ) :
    ∀ᵐ y ∂(ν.fst),
      (∫ u, fderiv ℝ ψ y (Bfield y u) ∂(ν.condKernel y)) =
        fderiv ℝ ψ y (Bfield y (exposureAdmissibleControl ν y)) := by
  filter_upwards [exposure_condKernel_disk_support hν,
    exposureAdmissibleControl_eq_mean_ae hν] with y hdy hyeq
  have hint : Integrable (fun u : ℂ => u) (ν.condKernel y) :=
    integrable_control_of_disk_support hdy
  rw [integral_balance_Bfield y ψ hint]
  have hyeq' : (∫ u, u ∂(ν.condKernel y)) = exposureAdmissibleControl ν y :=
    hyeq.symm
  rw [hyeq']

/-- Control averaging of an exposure record (Appendix E 2, Step 4): there is a
measurable, globally disk-valued control `ū : Y → U` whose averaged field
`B(y, ū(y))` satisfies the original balance equation against `ν.fst`, with the
same total mass. -/
theorem exists_averaged_exposure_flow (ν : Measure ExposureAmbient)
    (hν : IsExposureRecord ν) :
    ∃ ubar : (Fin 11 → ℝ) → ℂ,
      Measurable ubar ∧
      (∀ y, ‖ubar y‖ ≤ 1) ∧
      ν.fst Ysetᶜ = 0 ∧
      Integrable (fun y => Bfield y (ubar y)) ν.fst ∧
      (∀ ψ : (Fin 11 → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun y => fderiv ℝ ψ y (Bfield y (ubar y))) ν.fst ∧
        (∫ y, fderiv ℝ ψ y (Bfield y (ubar y)) ∂ν.fst) = ψ yPi - ψ y0) ∧
      ν.fst Set.univ = ν Set.univ := by
  letI : IsFiniteMeasure ν := hν.1
  have hubar_meas : Measurable (exposureAdmissibleControl ν) :=
    measurable_exposureAdmissibleControl ν
  have hubar1 : ∀ y, ‖exposureAdmissibleControl ν y‖ ≤ 1 :=
    norm_exposureAdmissibleControl_le_one ν
  have hY : ∀ᵐ y ∂(ν.fst), y ∈ Yset := mem_ae_iff.mpr (exposure_marginal_support hν)
  refine ⟨exposureAdmissibleControl ν, hubar_meas, hubar1,
    exposure_marginal_support hν, ?_, fun ψ hψ hψc => ?_, ?_⟩
  · obtain ⟨K, hK0, hK⟩ := Bfield_bounded
    refine integrable_of_ae_bound
      (measurable_Bfield.comp (measurable_id.prodMk hubar_meas)).aestronglyMeasurable
      (C := K) ?_
    filter_upwards [hY] with y hy
    exact hK y hy _ (hubar1 y)
  · have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_cast)
    refine ⟨?_, ?_⟩
    · obtain ⟨M, hM⟩ := isCompact_Yset.exists_bound_of_continuousOn
        (hψ1.continuous_fderiv one_ne_zero).continuousOn
      obtain ⟨K, hK0, hK⟩ := Bfield_bounded
      refine integrable_of_ae_bound (((measurable_balance_integrand hψ1).comp
        (measurable_id.prodMk hubar_meas)).aestronglyMeasurable) (C := M * K) ?_
      filter_upwards [hY] with y hy
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y hy)
      calc ‖fderiv ℝ ψ y (Bfield y (exposureAdmissibleControl ν y))‖
          ≤ ‖fderiv ℝ ψ y‖ * ‖Bfield y (exposureAdmissibleControl ν y)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * K := mul_le_mul (hM y hy) (hK y hy _ (hubar1 y))
            (norm_nonneg _) hM0
    · have hjoint : (∫ y, (∫ u, fderiv ℝ ψ y (Bfield y u) ∂(ν.condKernel y)) ∂(ν.fst))
          = ψ yPi - ψ y0 :=
        (Measure.integral_condKernel (integrable_exposure_balance hν hψ1)).trans
          (hν.2.2 ψ hψ hψc)
      exact (integral_congr_ae (integral_inner_balance_eq hν ψ)).symm.trans hjoint
  · exact Measure.fst_univ

end CZExposure
