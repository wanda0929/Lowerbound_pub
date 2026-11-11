module
public import RequestProject.AppendixE.ArcCurrent
public import RequestProject.AppendixE.PolarAlignment
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! A concrete compact-open parameter space for stopped simple arcs.
No measure on this space, or decomposition of a current, is assumed to exist. -/
@[expose] public section
noncomputable section
namespace CZExposure
open MeasureTheory Set

/-- The ambient topology is length times compact-open convergence of paths.
Only the simple unit-speed arcs with constant tails are retained. -/
abbrev ArcSpace := {c : ℝ × C(ℝ, ExposureEuclidean) //
  0 < c.1 ∧ LipschitzWith 1 c.2 ∧ InjOn c.2 (Icc 0 c.1) ∧
  (∀ᵐ t ∂(volume.restrict (Icc 0 c.1)),
    ∃ v, HasDerivAt c.2 v t ∧ ‖v‖ = 1) ∧
  (∀ t, t ≤ 0 → c.2 t = c.2 0) ∧
  (∀ t, c.1 ≤ t → c.2 t = c.2 c.1)}

namespace ArcSpace
instance : MeasurableSpace ArcSpace := borel ArcSpace
instance : BorelSpace ArcSpace := ⟨rfl⟩

def length (a : ArcSpace) : ℝ := a.val.1
def path (a : ArcSpace) : C(ℝ, ExposureEuclidean) := a.val.2

def toArc (a : ArcSpace) : EuclideanArc where
  length := a.length
  length_pos := a.property.1
  path := a.path
  lipschitz := a.property.2.1
  injectiveOn := a.property.2.2.1
  unit_speed := a.property.2.2.2.1

/-- Every existing arc has a canonical constant-tail representative. -/
def ofArc (γ : EuclideanArc) : ArcSpace := by
  let q : ℝ → ExposureEuclidean := fun t => γ.path (max 0 (min t γ.length))
  have hq : LipschitzWith 1 q := by
    simpa only [one_mul] using γ.lipschitz.comp ((LipschitzWith.id.min_const γ.length).const_max 0)
  have he (t : ℝ) (ht : t ∈ Icc 0 γ.length) : q t = γ.path t := by
    simp [q, min_eq_left ht.2, max_eq_right ht.1]
  refine ⟨⟨γ.length, ⟨q, hq.continuous⟩⟩, γ.length_pos, hq, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht h
    change q s = q t at h
    exact γ.injectiveOn hs ht (by simpa only [he s hs, he t ht] using h)
  · have hm : ∀ᵐ t ∂γ.parameterMeasure, t ∈ Ioo 0 γ.length := by
      rw [EuclideanArc.parameterMeasure, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [γ.unit_speed, hm] with t ht hti
    obtain ⟨v, hv, hn⟩ := ht
    refine ⟨v, hv.congr_of_eventuallyEq ?_, hn⟩
    filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
    exact he s ⟨hs.1.le, hs.2.le⟩
  · intro t ht
    change q t = q 0
    simp [q, min_eq_left (ht.trans γ.length_pos.le), max_eq_left ht, γ.length_pos.le]
  · intro t ht
    change q t = q γ.length
    simp [q, min_eq_right ht, γ.length_pos.le]

@[simp] theorem ofArc_length (γ : EuclideanArc) : (ofArc γ).length = γ.length := rfl

theorem ofArc_path (γ : EuclideanArc) {t : ℝ} (ht : t ∈ Icc 0 γ.length) :
    (ofArc γ).path t = γ.path t := by
  change γ.path (max 0 (min t γ.length)) = γ.path t
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem ofArc_deriv (γ : EuclideanArc) :
    (fun t => deriv (ofArc γ).path t) =ᵐ[γ.parameterMeasure] deriv γ.path := by
  have hm : ∀ᵐ t ∂γ.parameterMeasure, t ∈ Ioo 0 γ.length := by
    rw [EuclideanArc.parameterMeasure, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hm] with t ht
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact ofArc_path γ ⟨hs.1.le, hs.2.le⟩

theorem ofArc_lengthMeasure (γ : EuclideanArc) : (ofArc γ).toArc.lengthMeasure = γ.lengthMeasure := by
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact ofArc_path γ ht

theorem ofArc_vectorCurrent (γ : EuclideanArc) : (ofArc γ).toArc.vectorCurrent = γ.vectorCurrent := by
  classical
  apply VectorMeasure.ext
  intro s hs
  rw [EuclideanArc.vectorCurrent_apply _ hs, γ.vectorCurrent_apply hs]
  change (∫ t in (ofArc γ).path ⁻¹' s, deriv (ofArc γ).path t ∂γ.parameterMeasure) = _
  rw [← integral_indicator (hs.preimage (ofArc γ).path.continuous.measurable),
    ← integral_indicator (hs.preimage γ.lipschitz.continuous.measurable)]
  change (∫ t, _ ∂γ.parameterMeasure) = _
  apply integral_congr_ae
  filter_upwards [ofArc_deriv γ, ae_restrict_mem measurableSet_Icc] with t hd ht
  by_cases hm : γ.path t ∈ s <;> simp [hm, ofArc_path γ ht, hd]

theorem continuous_length : Continuous length := continuous_fst.comp continuous_subtype_val
theorem continuous_path : Continuous path := continuous_snd.comp continuous_subtype_val
theorem continuous_eval : Continuous (fun p : ArcSpace × ℝ => p.1.path p.2) := by
  exact (continuous_path.comp continuous_fst).eval continuous_snd
theorem continuous_initial : Continuous (fun a : ArcSpace => a.path 0) :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)
theorem continuous_terminal : Continuous (fun a : ArcSpace => a.path a.length) :=
  continuous_eval.comp (continuous_id.prodMk continuous_length)

theorem measurable_tangent : Measurable (fun p : ArcSpace × ℝ => deriv p.1.path p.2) :=
  measurable_deriv_with_param (f := fun a : ArcSpace => (a.path : ℝ → ExposureEuclidean)) continuous_eval

/-- The length measure is a measurable kernel, including moving endpoints. -/
theorem measurable_lengthMeasure : Measurable (fun a : ArcSpace => a.toArc.lengthMeasure) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let B : Set (ArcSpace × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1.length ∧ p.1.path p.2 ∈ s}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd (continuous_length.measurable.comp measurable_fst)).inter
        (hs.preimage continuous_eval.measurable))
  have hm : Measurable (fun a : ArcSpace => ∫⁻ t, B.indicator (fun _ => (1:ENNReal)) (a,t)) :=
    Measurable.lintegral_prod_right (f := fun a t => B.indicator (fun _ => (1:ENNReal)) (a,t))
      (measurable_const.indicator hB)
  convert hm using 1
  funext a
  rw [EuclideanArc.lengthMeasure, Measure.map_apply a.toArc.lipschitz.continuous.measurable hs,
    EuclideanArc.parameterMeasure, Measure.restrict_apply (hs.preimage a.toArc.lipschitz.continuous.measurable)]
  change volume (a.path ⁻¹' s ∩ Icc 0 a.length) =
    ∫⁻ t, B.indicator (fun _ => (1:ENNReal)) (a,t)
  rw [← lintegral_indicator_one (s := a.path ⁻¹' s ∩ Icc 0 a.length)]
  · apply lintegral_congr
    intro t
    simp [B, Set.indicator_apply, and_comm, and_assoc]
  · exact (hs.preimage a.path.continuous.measurable).inter measurableSet_Icc

/-- Vector-current evaluation on a measurable region varies measurably with
the arc. This uses parameter derivatives, not independently chosen inverses. -/
theorem measurable_vectorCurrent_apply {s : Set ExposureEuclidean} (hs : MeasurableSet s) :
    Measurable (fun a : ArcSpace => a.toArc.vectorCurrent s) := by
  classical
  let B : Set (ArcSpace × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1.length ∧ p.1.path p.2 ∈ s}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd (continuous_length.measurable.comp measurable_fst)).inter
        (hs.preimage continuous_eval.measurable))
  have hm := (measurable_tangent.indicator hB).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert hm.measurable using 1
  funext a
  rw [a.toArc.vectorCurrent_apply hs, EuclideanArc.parameterMeasure]
  change (∫ t in a.path ⁻¹' s, deriv a.path t ∂volume.restrict (Icc 0 a.length)) = _
  rw [Measure.restrict_restrict (hs.preimage a.path.continuous.measurable),
    ← integral_indicator ((hs.preimage a.path.continuous.measurable).inter measurableSet_Icc)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp [B, Set.indicator_apply, and_comm, and_assoc]

/-- The pairing with any measurable vector field is measurable in the arc;
this does not assert its integrability against an arbitrary ensemble. -/
theorem measurable_pairing (q : ExposureEuclidean → ExposureEuclidean) (hq : Measurable q) :
    Measurable (fun a : ArcSpace => EuclideanCurrentArcData.arcPairing a.toArc q) := by
  classical
  let B : Set (ArcSpace × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1.length}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (continuous_length.measurable.comp measurable_fst))
  have hm := (((hq.comp continuous_eval.measurable).inner (𝕜 := ℝ) measurable_tangent).indicator hB).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert hm.measurable using 1
  funext a
  rw [EuclideanCurrentArcData.arcPairing, EuclideanArc.parameterMeasure,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp [B, Set.indicator_apply, toArc]

/-- Pull a measurable family into the existing realization interface.
Continuity of the family is not required. -/
def measurableArcs {A : Type*} [MeasurableSpace A]
    {T : EuclideanNormalCurrentData} {source sink : ExposureEuclidean}
    (D : EuclideanCurrentArcData T source sink A)
    (f : A → ArcSpace) (hf : Measurable f) (he : ∀ a, D.arc a = (f a).toArc) :
    D.MeasurableArcs where
  path_measurable := by
    simp_rw [he]
    exact continuous_eval.measurable.comp (hf.prodMap measurable_id)
  tangent := fun p => deriv (f p.1).path p.2
  tangent_measurable := measurable_tangent.comp (hf.prodMap measurable_id)
  tangent_deriv := by
    apply Filter.Eventually.of_forall
    intro a
    rw [he]
    exact (f a).toArc.unit_speed.mono fun t ⟨v, hv, _⟩ => by
      change HasDerivAt (f a).path (deriv (f a).path t) t
      have hd : deriv (f a).path t = v := hv.deriv
      rwa [hd]

end ArcSpace
end CZExposure
