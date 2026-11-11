module
public import RequestProject.AppendixE.ExposureDecomposition
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Parameterized arcs and the exposure clock (Appendix E support)

This file defines genuine parameterized Euclidean arcs — positive-length,
injective, unit-speed Lipschitz curves — together with their length measure
`Measure.map path (volume.restrict (Icc 0 length))`, the inverse-speed
exposure clock, and the bridge structure `ExposureArcRealization` connecting
the measure-level decomposition data of `ExposureDecomposition.lean` to
actual curve functions.

All results are conditional on supplied arcs and realization hypotheses:
no arc decomposition is asserted to exist, no identification with the
Paolini–Stepanov current framework is made, and neither tangent alignment
(`IsDirectedBy`) nor an ODE for the reparameterized path is proved here.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set intervalIntegral

/-- A positive-length, injective, unit-speed Lipschitz arc in the Euclidean
exposure space. `parameterMeasure` is `ds` on `[0, length]` and
`lengthMeasure` is its pushforward along the path. -/
structure EuclideanArc where
  length : ℝ
  length_pos : 0 < length
  path : ℝ → ExposureEuclidean
  lipschitz : LipschitzWith 1 path
  injectiveOn : Set.InjOn path (Set.Icc 0 length)
  unit_speed : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 length)),
    ∃ w : ExposureEuclidean, HasDerivAt path w s ∧ ‖w‖ = 1

namespace EuclideanArc

/-- The parameter measure `ds` on `[0, length]`. -/
def parameterMeasure (γ : EuclideanArc) : Measure ℝ :=
  volume.restrict (Set.Icc 0 γ.length)

/-- The pushed-forward length measure of the arc. -/
def lengthMeasure (γ : EuclideanArc) : Measure ExposureEuclidean :=
  Measure.map γ.path γ.parameterMeasure

/-- Total inverse-speed time of the arc. Infinity absorbs any stationary
stretch. -/
def exposureTime (γ : EuclideanArc) (F : EuclideanExposureFlow) : ENNReal :=
  ∫⁻ z, F.exposureTimeWeight z ∂γ.lengthMeasure

/-- Ordinary real inverse speed, used only under finite `exposureTime` for
clock theorems.  At zero speed it is `0` by the real-field convention; the
ENNReal accounting stays `∞`. -/
def inverseSpeed (γ : EuclideanArc) (F : EuclideanExposureFlow) (s : ℝ) : ℝ :=
  ‖F.velocity (γ.path s)‖⁻¹

/-- The exposure-time clock along the arc. -/
def exposureClock (γ : EuclideanArc) (F : EuclideanExposureFlow) (s : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..s, γ.inverseSpeed F q

/-- Future alignment interface: the path derivative equals inverse-speed times
the field a.e.  Not assumed to hold automatically and not proved here. -/
def IsDirectedBy (γ : EuclideanArc) (F : EuclideanExposureFlow) : Prop :=
  ∀ᵐ s ∂γ.parameterMeasure,
    HasDerivAt γ.path (γ.inverseSpeed F s • F.velocity (γ.path s)) s

theorem lengthMeasure_univ (γ : EuclideanArc) :
    γ.lengthMeasure Set.univ = ENNReal.ofReal γ.length := by
  rw [lengthMeasure,
    Measure.map_apply γ.lipschitz.continuous.measurable MeasurableSet.univ,
    Set.preimage_univ, parameterMeasure,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, sub_zero]

theorem lengthMeasure_eq_map_speed (γ : EuclideanArc) :
    γ.lengthMeasure = Measure.map γ.path
      (γ.parameterMeasure.withDensity (fun s => ‖deriv γ.path s‖ₑ)) := by
  have h1 : (fun s => ‖deriv γ.path s‖ₑ) =ᵐ[γ.parameterMeasure]
      (1 : ℝ → ENNReal) := by
    filter_upwards [γ.unit_speed] with s ⟨w, hw, hnorm⟩
    rw [hw.deriv]
    simp only [Pi.one_apply, enorm_eq_nnnorm, ENNReal.coe_eq_one]
    ext
    exact hnorm
  have h2 : γ.parameterMeasure.withDensity (fun s => ‖deriv γ.path s‖ₑ) =
      γ.parameterMeasure := by
    rw [MeasureTheory.withDensity_congr_ae h1]
    exact MeasureTheory.withDensity_one
  rw [h2]
  rfl

theorem lintegral_lengthMeasure (γ : EuclideanArc)
    {w : ExposureEuclidean → ENNReal} (hw : Measurable w) :
    (∫⁻ z, w z ∂γ.lengthMeasure) =
      ∫⁻ s, w (γ.path s) ∂γ.parameterMeasure :=
  lintegral_map hw γ.lipschitz.continuous.measurable

theorem ae_path_of_ae_lengthMeasure (γ : EuclideanArc)
    {P : ExposureEuclidean → Prop} (hP : ∀ᵐ z ∂γ.lengthMeasure, P z) :
    ∀ᵐ s ∂γ.parameterMeasure, P (γ.path s) :=
  MeasureTheory.ae_of_ae_map γ.lipschitz.continuous.measurable.aemeasurable hP

theorem mapsTo_of_ae_mem_closed (γ : EuclideanArc)
    {K : Set ExposureEuclidean} (hK : IsClosed K)
    (hKae : ∀ᵐ z ∂γ.lengthMeasure, z ∈ K) :
    Set.MapsTo γ.path (Set.Icc 0 γ.length) K := by
  have hKae' : ∀ᵐ s ∂γ.parameterMeasure, γ.path s ∈ K :=
    γ.ae_path_of_ae_lengthMeasure hKae
  have hg : Continuous (fun s => Metric.infEDist (γ.path s) K) :=
    Metric.continuous_infEDist.comp γ.lipschitz.continuous
  have hg0 : ∀ᵐ s ∂γ.parameterMeasure, Metric.infEDist (γ.path s) K = 0 := by
    filter_upwards [hKae'] with s hs
    exact Metric.infEDist_zero_of_mem hs
  have hEq : Set.EqOn (fun s => Metric.infEDist (γ.path s) K) 0
      (Set.Icc 0 γ.length) :=
    Measure.eqOn_Icc_of_ae_eq volume γ.length_pos.ne hg0 hg.continuousOn
      continuousOn_const
  intro s hs
  rw [Metric.mem_iff_infEDist_zero_of_closed hK]
  exact hEq hs

theorem exposureTime_eq_lintegral (γ : EuclideanArc) (F : EuclideanExposureFlow) :
    γ.exposureTime F = ∫⁻ s, F.exposureTimeWeight (γ.path s) ∂γ.parameterMeasure :=
  γ.lintegral_lengthMeasure F.measurable_exposureTimeWeight

theorem measurable_weight_path (γ : EuclideanArc) (F : EuclideanExposureFlow) :
    Measurable (fun s => F.exposureTimeWeight (γ.path s)) :=
  F.measurable_exposureTimeWeight.comp γ.lipschitz.continuous.measurable

theorem ae_velocity_ne_zero (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤) :
    ∀ᵐ s ∂γ.parameterMeasure, F.velocity (γ.path s) ≠ 0 := by
  have hw : ∀ᵐ s ∂γ.parameterMeasure, F.exposureTimeWeight (γ.path s) < ⊤ :=
    ae_lt_top (γ.measurable_weight_path F)
      (by rw [← γ.exposureTime_eq_lintegral]; exact hfinite.ne)
  filter_upwards [hw] with s hs hv0
  exact hs.ne (F.exposureTimeWeight_eq_top_of_velocity_eq_zero hv0)

theorem inverseSpeed_eq_toReal (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (s : ℝ) :
    γ.inverseSpeed F s = (F.exposureTimeWeight (γ.path s)).toReal := by
  simp [inverseSpeed, EuclideanExposureFlow.exposureTimeWeight]

theorem integrable_inverseSpeed (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤) :
    Integrable (γ.inverseSpeed F) γ.parameterMeasure := by
  have hne : (∫⁻ s, F.exposureTimeWeight (γ.path s) ∂γ.parameterMeasure) ≠ ⊤ := by
    rw [← γ.exposureTime_eq_lintegral]; exact hfinite.ne
  have h := integrable_toReal_of_lintegral_ne_top
    (γ.measurable_weight_path F).aemeasurable hne
  have hfun : γ.inverseSpeed F =
      fun s => (F.exposureTimeWeight (γ.path s)).toReal :=
    funext (γ.inverseSpeed_eq_toReal F)
  rw [hfun]
  exact h

theorem integral_inverseSpeed (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤) :
    (∫ s, γ.inverseSpeed F s ∂γ.parameterMeasure) = (γ.exposureTime F).toReal := by
  have hlt : ∀ᵐ s ∂γ.parameterMeasure, F.exposureTimeWeight (γ.path s) < ⊤ :=
    ae_lt_top (γ.measurable_weight_path F)
      (by rw [← γ.exposureTime_eq_lintegral]; exact hfinite.ne)
  simp only [γ.inverseSpeed_eq_toReal F]
  rw [integral_toReal (γ.measurable_weight_path F).aemeasurable hlt,
    ← γ.exposureTime_eq_lintegral]

theorem intervalIntegrable_inverseSpeed (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤) :
    IntervalIntegrable (γ.inverseSpeed F) volume 0 γ.length := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le γ.length_pos.le]
  exact γ.integrable_inverseSpeed F hfinite

theorem exposureClock_zero (γ : EuclideanArc) (F : EuclideanExposureFlow) :
    γ.exposureClock F 0 = 0 := by
  simp [exposureClock]

theorem exposureClock_terminal (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤) :
    γ.exposureClock F γ.length = (γ.exposureTime F).toReal := by
  show (∫ q in (0 : ℝ)..γ.length, γ.inverseSpeed F q) = (γ.exposureTime F).toReal
  rw [intervalIntegral.integral_of_le γ.length_pos.le]
  show (∫ s, γ.inverseSpeed F s ∂volume.restrict (Set.Ioc 0 γ.length)) = _
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  exact γ.integral_inverseSpeed F hfinite

theorem absolutelyContinuous_exposureClock (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤) :
    AbsolutelyContinuousOnInterval (γ.exposureClock F) 0 γ.length :=
  (γ.intervalIntegrable_inverseSpeed F hfinite).absolutelyContinuousOnInterval_intervalIntegral
    Set.left_mem_uIcc

end EuclideanArc

/-- Raw realization hypotheses connecting decomposition data to actual arc
functions: for a.e. index, the component measure is the arc's length measure
and the declared endpoints are the arc's endpoints.  No existence assertion is
made; a future Paolini–Stepanov application must construct these unit-speed
parameterizations and prove the links.  There is intentionally no tangent
premise hidden in these fields, and the index space `A` need not yet be a
particular curve quotient. -/
structure ExposureArcRealization {F : EuclideanExposureFlow} {A : Type*}
    [MeasurableSpace A] (D : ExposureMeasureDecomposition F A) where
  arc : A → EuclideanArc
  component_eq : ∀ᵐ a ∂D.ensemble,
    D.massDecomposition.component a = (arc a).lengthMeasure
  initial_eq : ∀ᵐ a ∂D.ensemble, D.initial a = (arc a).path 0
  terminal_eq : ∀ᵐ a ∂D.ensemble,
    D.terminal a = (arc a).path (arc a).length

namespace ExposureArcRealization

variable {F : EuclideanExposureFlow} {A : Type*} [MeasurableSpace A]
    {D : ExposureMeasureDecomposition F A}

theorem exists_arc_le_exposure_mass (R : ExposureArcRealization D)
    (Good : EuclideanArc → Prop)
    (hGood : ∀ᵐ a ∂D.ensemble, Good (R.arc a)) :
    ∃ γ : EuclideanArc, Good γ ∧
      γ.path 0 = exposureEuclideanEquiv y0 ∧
      γ.path γ.length = exposureEuclideanEquiv yPi ∧
      Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain ∧
      (∀ᵐ s ∂γ.parameterMeasure, F.velocity (γ.path s) ≠ 0) ∧
      γ.exposureTime F ≤ F.stateMeasure Set.univ ∧
      γ.exposureTime F < ⊤ := by
  letI := D.isProbabilityMeasure_ensemble
  have hGood' : ∀ᵐ a ∂D.ensemble,
      (Good (R.arc a) ∧
        D.massDecomposition.component a = (R.arc a).lengthMeasure ∧
        D.initial a = (R.arc a).path 0 ∧
        D.terminal a = (R.arc a).path (R.arc a).length) := by
    filter_upwards [hGood, R.component_eq, R.initial_eq, R.terminal_eq]
      with a hG hc hi ht
    exact ⟨hG, hc, hi, ht⟩
  obtain ⟨a, ⟨hG, hcomp, hi, ht⟩, hi0, htP, hdom, hvel, hle, hlt⟩ :=
    D.exists_component_le_exposure_mass _ hGood'
  refine ⟨R.arc a, hG, hi.symm.trans hi0, ht.symm.trans htP, ?_, ?_, ?_, ?_⟩
  · apply (R.arc a).mapsTo_of_ae_mem_closed
      isCompact_euclideanExposureDomain.isClosed
    rw [← hcomp]
    exact hdom
  · have hvel' : ∀ᵐ z ∂(R.arc a).lengthMeasure, F.velocity z ≠ 0 := by
      rw [← hcomp]
      exact hvel
    exact (R.arc a).ae_path_of_ae_lengthMeasure hvel'
  · show (∫⁻ z, F.exposureTimeWeight z ∂(R.arc a).lengthMeasure) ≤
      F.stateMeasure Set.univ
    rw [← hcomp]
    exact hle
  · show (∫⁻ z, F.exposureTimeWeight z ∂(R.arc a).lengthMeasure) < ⊤
    rw [← hcomp]
    exact hlt

end ExposureArcRealization

end CZExposure
