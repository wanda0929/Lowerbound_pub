module
public import RequestProject.AppendixE.ExposureCurrent
public import RequestProject.AppendixE.VectorMeasureDensity

/-!
# Polar representation and Euclidean current data (Appendix E support)

From the exact variation equality `(μ.withDensityᵥ v).variation =
μ.withDensity (‖v ·‖ₑ)` (proved for finite μ and integrable v in
`VectorMeasureDensity.lean`) we obtain `F.vectorMeasure.variation =
F.massBound`, the polar direction `v/‖v‖` (unit norm a.e. for the variation,
zero where `v = 0`), reconstruction of the original vector measure and action,
and a finite source–sink boundary datum.

`EuclideanNormalCurrentData` is a finite-vector-measure PRESENTATION of a
normal current: it is not a metric-current conversion, asserts no AK
continuity/locality, and does not claim equivalence with metric currents.
`boundaryPlus`/`boundaryMinus` are finite positive measures, not asserted
Jordan parts.  No acyclicity, decomposition, or tangent existence is claimed.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set Filter

/-- Finite vector measure with unit polar direction, action representation,
and a distributional boundary evaluated against smooth compact tests and
expressed by finite positive measures `boundaryPlus`/`boundaryMinus` (not
asserted Jordan parts).  This is the Euclidean vector-measure presentation of
a normal current, not a metric-current identification. -/
structure EuclideanNormalCurrentData where
  vectorMeasure : VectorMeasure ExposureEuclidean ExposureEuclidean
  finite_variation : IsFiniteMeasure vectorMeasure.variation
  direction : ExposureEuclidean → ExposureEuclidean
  measurable_direction : Measurable direction
  direction_integrable : Integrable direction vectorMeasure.variation
  direction_unit : ∀ᵐ z ∂vectorMeasure.variation, ‖direction z‖ = 1
  represents : vectorMeasure = vectorMeasure.variation.withDensityᵥ direction
  boundaryPlus : Measure ExposureEuclidean
  finite_boundaryPlus : IsFiniteMeasure boundaryPlus
  boundaryMinus : Measure ExposureEuclidean
  finite_boundaryMinus : IsFiniteMeasure boundaryMinus
  boundary : ∀ ψ : ExposureEuclidean → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    Integrable (fun z => fderiv ℝ ψ z (direction z)) vectorMeasure.variation ∧
      (∫ z, fderiv ℝ ψ z (direction z) ∂vectorMeasure.variation) =
        (∫ z, ψ z ∂boundaryPlus) - (∫ z, ψ z ∂boundaryMinus)

def EuclideanNormalCurrentData.action (T : EuclideanNormalCurrentData)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) : ℝ :=
  ∫ z, ω z (T.direction z) ∂T.vectorMeasure.variation

namespace EuclideanExposureFlow

variable (F : EuclideanExposureFlow)

theorem variation_eq_massBound :
    F.vectorMeasure.variation = F.massBound := by
  letI := F.finite_stateMeasure
  exact withDensity_vectorMeasure_variation_eq F.velocity_integrable

def polarDirection (z : ExposureEuclidean) : ExposureEuclidean :=
  ‖F.velocity z‖⁻¹ • F.velocity z

theorem measurable_polarDirection : Measurable F.polarDirection :=
  F.measurable_velocity.norm.inv.smul F.measurable_velocity

theorem norm_smul_polarDirection (z : ExposureEuclidean) :
    ‖F.velocity z‖ • F.polarDirection z = F.velocity z := by
  by_cases hv : F.velocity z = 0
  · simp [hv, polarDirection]
  · simp only [polarDirection, smul_smul]
    rw [mul_inv_cancel₀ (norm_pos_iff.mpr hv).ne', one_smul]

theorem norm_polarDirection_of_ne_zero {z : ExposureEuclidean}
    (hz : F.velocity z ≠ 0) : ‖F.polarDirection z‖ = 1 := by
  simp only [polarDirection, norm_smul]
  rw [norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_pos_iff.mpr hz).ne']

theorem ae_velocity_ne_zero_variation :
    ∀ᵐ z ∂F.vectorMeasure.variation, F.velocity z ≠ 0 := by
  rw [variation_eq_massBound]
  simp only [EuclideanExposureFlow.massBound]
  rw [ae_withDensity_iff (F.measurable_velocity.enorm)]
  filter_upwards with z
  exact mt enorm_eq_zero.mpr

theorem ae_norm_polarDirection :
    ∀ᵐ z ∂F.vectorMeasure.variation, ‖F.polarDirection z‖ = 1 :=
  F.ae_velocity_ne_zero_variation.mono fun _ hz =>
    F.norm_polarDirection_of_ne_zero hz

theorem integrable_polarDirection :
    Integrable F.polarDirection F.vectorMeasure.variation := by
  rw [variation_eq_massBound]
  simp only [EuclideanExposureFlow.massBound]
  refine (integrable_withDensity_iff_integrable_smul'
    F.measurable_velocity.enorm
    (ae_lt_top F.measurable_velocity.enorm
      F.velocity_integrable.hasFiniteIntegral.ne)).mpr ?_
  have hpt : (fun z => ((‖F.velocity z‖ₑ).toReal) • F.polarDirection z) =
      F.velocity := funext fun z => by
    rw [toReal_enorm]
    exact F.norm_smul_polarDirection z
  rw [hpt]
  exact F.velocity_integrable

theorem vectorMeasure_eq_withDensity_polar :
    F.vectorMeasure =
      F.vectorMeasure.variation.withDensityᵥ F.polarDirection := by
  rw [variation_eq_massBound]
  simp only [EuclideanExposureFlow.massBound]
  have h := withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
    (F.measurable_velocity.enorm.aemeasurable)
    (ae_lt_top F.measurable_velocity.enorm
      F.velocity_integrable.hasFiniteIntegral.ne)
    (g := F.polarDirection) ?_
  · have hpt : (fun x => (‖F.velocity x‖ₑ).toReal • F.polarDirection x) =
        F.velocity := funext fun z => by
        rw [toReal_enorm]
        exact F.norm_smul_polarDirection z
    rw [hpt] at h
    exact h
  · simp_rw [toReal_enorm]
    simpa only [norm_smul_polarDirection] using F.velocity_integrable

theorem integrable_action_polar_iff
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) :
    Integrable (fun z => ω z (F.polarDirection z)) F.vectorMeasure.variation ↔
      Integrable (fun z => ω z (F.velocity z)) F.stateMeasure := by
  rw [variation_eq_massBound]
  simp only [EuclideanExposureFlow.massBound]
  have h := integrable_withDensity_iff_integrable_smul'
    (g := fun z => ω z (F.polarDirection z))
    F.measurable_velocity.enorm
    (ae_lt_top F.measurable_velocity.enorm
      F.velocity_integrable.hasFiniteIntegral.ne)
  have hpt : (fun z => (‖F.velocity z‖ₑ).toReal •
      ω z (F.polarDirection z)) =
      (fun z => ω z (F.velocity z)) := funext fun z => by
    rw [toReal_enorm, ← ContinuousLinearMap.map_smul,
      norm_smul_polarDirection]
  rw [hpt] at h
  exact h

theorem action_eq_integral_polar
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) :
    F.action ω =
      ∫ z, ω z (F.polarDirection z) ∂F.vectorMeasure.variation := by
  rw [variation_eq_massBound]
  simp only [EuclideanExposureFlow.massBound]
  rw [integral_withDensity_eq_integral_toReal_smul
    F.measurable_velocity.enorm
    (ae_lt_top F.measurable_velocity.enorm
      F.velocity_integrable.hasFiniteIntegral.ne)]
  apply integral_congr_ae
  filter_upwards with z
  rw [toReal_enorm, ← ContinuousLinearMap.map_smul, norm_smul_polarDirection]

theorem polar_boundary_integrable {ψ : ExposureEuclidean → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z => fderiv ℝ ψ z (F.polarDirection z))
      F.vectorMeasure.variation := by
  have h := (F.integrable_action_polar_iff
    (fun z => fderiv ℝ ψ z)).mpr (F.balance ψ hψ hψc).1
  exact h

theorem polar_boundary_eq {ψ : ExposureEuclidean → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ z, fderiv ℝ ψ z (F.polarDirection z) ∂F.vectorMeasure.variation) =
      ψ (exposureEuclideanEquiv yPi) - ψ (exposureEuclideanEquiv y0) := by
  rw [← F.action_eq_integral_polar fun z => fderiv ℝ ψ z]
  exact F.boundary_eq hψ hψc

def toNormalCurrentData : EuclideanNormalCurrentData where
  vectorMeasure := F.vectorMeasure
  finite_variation := ⟨F.variation_univ_lt_top⟩
  direction := F.polarDirection
  measurable_direction := F.measurable_polarDirection
  direction_integrable := F.integrable_polarDirection
  direction_unit := F.ae_norm_polarDirection
  represents := F.vectorMeasure_eq_withDensity_polar
  boundaryPlus := Measure.dirac (exposureEuclideanEquiv yPi)
  finite_boundaryPlus := inferInstance
  boundaryMinus := Measure.dirac (exposureEuclideanEquiv y0)
  finite_boundaryMinus := inferInstance
  boundary := by
    intro ψ hψ hψc
    refine ⟨F.polar_boundary_integrable hψ hψc, ?_⟩
    simpa only [integral_dirac] using F.polar_boundary_eq hψ hψc

theorem toNormalCurrentData_action
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) :
    F.toNormalCurrentData.action ω = F.action ω :=
  (F.action_eq_integral_polar ω).symm

end EuclideanExposureFlow

end CZExposure
