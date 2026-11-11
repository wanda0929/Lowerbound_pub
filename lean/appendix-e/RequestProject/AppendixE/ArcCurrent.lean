module
public import RequestProject.AppendixE.ExposureArc
public import RequestProject.AppendixE.ExposurePolarCurrent
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Vector current of one simple unit-speed arc, with exact local mass and boundary. -/
@[expose] public section
noncomputable section
namespace CZExposure.EuclideanArc
open MeasureTheory Set intervalIntegral

variable (γ : EuclideanArc)

def intervalPath : Icc (0:ℝ) γ.length → ExposureEuclidean := fun s => γ.path s

private theorem intervalPath_embedding : MeasurableEmbedding γ.intervalPath := by
  have hc : Continuous γ.intervalPath := γ.lipschitz.continuous.comp continuous_subtype_val
  exact (hc.isClosedEmbedding (fun s t h =>
    Subtype.ext (γ.injectiveOn s.property t.property h))).measurableEmbedding

/-- Extend the tangent from the embedded parameter interval by zero.
Injectivity prevents cancellation between different visits to the same point. -/
def tangentField : ExposureEuclidean → ExposureEuclidean :=
  Function.extend γ.intervalPath (fun s => deriv γ.path s.val) (fun _ => 0)

theorem measurable_tangentField : Measurable γ.tangentField :=
  γ.intervalPath_embedding.measurable_extend
    ((measurable_deriv γ.path).comp measurable_subtype_coe) measurable_const

theorem tangentField_path {s : ℝ} (hs : s ∈ Icc 0 γ.length) :
    γ.tangentField (γ.path s) = deriv γ.path s :=
  γ.intervalPath_embedding.injective.extend_apply _ _ ⟨s,hs⟩

theorem tangentField_unit : ∀ᵐ x ∂γ.lengthMeasure, ‖γ.tangentField x‖ = 1 := by
  rw [lengthMeasure, ae_map_iff γ.lipschitz.continuous.measurable.aemeasurable
    (measurableSet_eq_fun γ.measurable_tangentField.norm measurable_const)]
  filter_upwards [γ.unit_speed, ae_restrict_mem measurableSet_Icc] with s hs hm
  obtain ⟨v, hv, hn⟩ := hs
  rw [γ.tangentField_path hm, hv.deriv]
  exact hn

instance finite_lengthMeasure : IsFiniteMeasure γ.lengthMeasure := by
  constructor
  rw [γ.lengthMeasure_univ]
  exact ENNReal.ofReal_lt_top

theorem integrable_tangentField : Integrable γ.tangentField γ.lengthMeasure :=
  Integrable.mono' (integrable_const (1:ℝ))
    γ.measurable_tangentField.aestronglyMeasurable
    (γ.tangentField_unit.mono fun _ h => h.le)

/-- The oriented arc current, represented as a vector measure in state space. -/
def vectorCurrent : VectorMeasure ExposureEuclidean ExposureEuclidean :=
  γ.lengthMeasure.withDensityᵥ γ.tangentField

/-- On every measurable region the vector measure integrates the oriented
tangent over exactly the visits to that region. -/
theorem vectorCurrent_apply {s : Set ExposureEuclidean} (hs : MeasurableSet s) :
    γ.vectorCurrent s = ∫ t in γ.path ⁻¹' s, deriv γ.path t ∂γ.parameterMeasure := by
  rw [vectorCurrent, withDensityᵥ_apply γ.integrable_tangentField hs,
    ← MeasureTheory.integral_indicator hs, lengthMeasure,
    integral_map γ.lipschitz.continuous.measurable.aemeasurable
      (γ.measurable_tangentField.indicator hs).aestronglyMeasurable,
    ← MeasureTheory.integral_indicator (hs.preimage γ.lipschitz.continuous.measurable)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  by_cases hm : γ.path t ∈ s <;> simp [hm, γ.tangentField_path ht]

theorem integrable_deriv : Integrable (deriv γ.path) γ.parameterMeasure := by
  have h := γ.integrable_tangentField.comp_aemeasurable
    γ.lipschitz.continuous.measurable.aemeasurable
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact γ.tangentField_path ht

/-- Equivalent pushforward definition, with no state-space inverse in the result. -/
theorem vectorCurrent_eq_map : γ.vectorCurrent =
    (γ.parameterMeasure.withDensityᵥ (deriv γ.path)).map γ.path := by
  ext s hs
  rw [γ.vectorCurrent_apply hs, VectorMeasure.map_apply _ γ.lipschitz.continuous.measurable hs,
    withDensityᵥ_apply γ.integrable_deriv (hs.preimage γ.lipschitz.continuous.measurable)]

/-- Local equality of measures, stronger than equality of their total masses. -/
theorem vectorCurrent_variation : γ.vectorCurrent.variation = γ.lengthMeasure := by
  rw [vectorCurrent, withDensity_vectorMeasure_variation_eq γ.integrable_tangentField]
  have h : (fun x => ‖γ.tangentField x‖ₑ) =ᵐ[γ.lengthMeasure] (fun _ => (1:ENNReal)) := by
    filter_upwards [γ.tangentField_unit] with x hx
    simp only [enorm_eq_nnnorm, ENNReal.coe_eq_one]
    apply NNReal.eq
    exact hx
  rw [withDensity_congr_ae h]
  exact withDensity_one

theorem vectorCurrent_mass : γ.vectorCurrent.variation univ = ENNReal.ofReal γ.length := by
  rw [γ.vectorCurrent_variation, γ.lengthMeasure_univ]

theorem vectorCurrent_compact_support :
    ∃ K : Set ExposureEuclidean, IsCompact K ∧ γ.vectorCurrent.variation Kᶜ = 0 := by
  let K := γ.path '' Icc 0 γ.length
  have hK : IsCompact K := isCompact_Icc.image γ.lipschitz.continuous
  refine ⟨K, hK, ?_⟩
  rw [γ.vectorCurrent_variation, lengthMeasure,
    Measure.map_apply γ.lipschitz.continuous.measurable hK.isClosed.measurableSet.compl,
    parameterMeasure, Measure.restrict_apply
      (hK.isClosed.measurableSet.compl.preimage γ.lipschitz.continuous.measurable)]
  have hz : γ.path ⁻¹' Kᶜ ∩ Icc 0 γ.length = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht, hI⟩
    exact ht ⟨t, hI, rfl⟩
  rw [hz, measure_empty]

/-- Pairing in state space agrees with integration along the oriented arc. -/
theorem integral_tangentField (F : ExposureEuclidean → ExposureEuclidean → ℝ)
    (hF : Measurable (fun x => F x (γ.tangentField x))) :
    (∫ x, F x (γ.tangentField x) ∂γ.lengthMeasure) =
      ∫ s, F (γ.path s) (deriv γ.path s) ∂γ.parameterMeasure := by
  rw [lengthMeasure, integral_map γ.lipschitz.continuous.measurable.aemeasurable
    hF.aestronglyMeasurable]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [γ.tangentField_path hs]

/-- The distributional boundary has the orientation terminal minus initial. -/
theorem boundary (ψ : ExposureEuclidean → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    Integrable (fun x => fderiv ℝ ψ x (γ.tangentField x)) γ.lengthMeasure ∧
      (∫ x, fderiv ℝ ψ x (γ.tangentField x) ∂γ.lengthMeasure) =
        ψ (γ.path γ.length) - ψ (γ.path 0) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hψ (by simp)
  have hAC : AbsolutelyContinuousOnInterval (fun s => ψ (γ.path s)) 0 γ.length :=
    (hK.comp γ.lipschitz).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : (fun s => deriv (fun t => ψ (γ.path t)) s) =ᵐ[γ.parameterMeasure]
      (fun s => fderiv ℝ ψ (γ.path s) (deriv γ.path s)) := by
    filter_upwards [γ.unit_speed] with s hs
    obtain ⟨v, hv, _⟩ := hs
    rw [hv.deriv]
    exact ((hψ.differentiable (by simp) (γ.path s)).hasFDerivAt.comp_hasDerivAt s hv).deriv
  have hi : Integrable (fun s => deriv (fun t => ψ (γ.path t)) s) γ.parameterMeasure :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le γ.length_pos.le).mp hAC.intervalIntegrable_deriv
  have hm : Measurable (fun x => fderiv ℝ ψ x (γ.tangentField x)) := by
    have he : Continuous (fun p : (ExposureEuclidean →L[ℝ] ℝ) × ExposureEuclidean => p.1 p.2) := by
      fun_prop
    exact he.measurable.comp ((hψ.continuous_fderiv (by simp)).measurable.prodMk γ.measurable_tangentField)
  have hcomp : (fun s => fderiv ℝ ψ (γ.path s) (γ.tangentField (γ.path s))) =ᵐ[γ.parameterMeasure]
      (fun s => fderiv ℝ ψ (γ.path s) (deriv γ.path s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [γ.tangentField_path hs]
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable
    γ.lipschitz.continuous.measurable.aemeasurable).mpr ((hi.congr hd).congr hcomp.symm), ?_⟩
  rw [γ.integral_tangentField _ hm, ← MeasureTheory.integral_congr_ae hd]
  have h := hAC.integral_deriv_eq_sub
  rw [integral_of_le γ.length_pos.le, ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- A single arc supplies all fields of the existing normal-current record. -/
def toNormalCurrentData : EuclideanNormalCurrentData where
  vectorMeasure := γ.vectorCurrent
  finite_variation := by rw [γ.vectorCurrent_variation]; infer_instance
  direction := γ.tangentField
  measurable_direction := γ.measurable_tangentField
  direction_integrable := by rw [γ.vectorCurrent_variation]; exact γ.integrable_tangentField
  direction_unit := by rw [γ.vectorCurrent_variation]; exact γ.tangentField_unit
  represents := by rw [γ.vectorCurrent_variation]; rfl
  boundaryPlus := Measure.dirac (γ.path γ.length)
  finite_boundaryPlus := inferInstance
  boundaryMinus := Measure.dirac (γ.path 0)
  finite_boundaryMinus := inferInstance
  boundary := by
    intro ψ hψ hs
    rw [γ.vectorCurrent_variation]
    simpa using γ.boundary ψ hψ hs

/-- The existing current action is the usual oriented line integral. -/
theorem action_eq (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ))
    (hω : Measurable (fun x => ω x (γ.tangentField x))) :
    γ.toNormalCurrentData.action ω =
      ∫ t, ω (γ.path t) (deriv γ.path t) ∂γ.parameterMeasure := by
  change (∫ x, ω x (γ.tangentField x) ∂γ.vectorCurrent.variation) = _
  rw [γ.vectorCurrent_variation]
  exact γ.integral_tangentField (fun x v => ω x v) hω

end CZExposure.EuclideanArc
