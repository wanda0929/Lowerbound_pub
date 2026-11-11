module
public import RequestProject.AppendixE.ArcSpace
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Compactness for the relaxed stopped paths needed before an arc
decomposition limit. Simplicity and unit speed are deliberately not imposed:
neither is preserved by compact-open limits. This does not construct a
decomposition of a current. -/
@[expose] public section
noncomputable section
namespace CZExposure
open MeasureTheory Set
open scoped NNReal ENNReal

/-- A duration and a stopped 1-Lipschitz path; duration may be zero, and is
not asserted to equal geometric length. -/
abbrev StoppedPathSpace := {c : ℝ × C(ℝ, ExposureEuclidean) //
  0 ≤ c.1 ∧ LipschitzWith 1 c.2 ∧
    ∀ t, c.2 t = c.2 (max 0 (min t c.1))}

namespace StoppedPathSpace
instance : MeasurableSpace StoppedPathSpace := borel StoppedPathSpace
instance : BorelSpace StoppedPathSpace := ⟨rfl⟩

def duration (a : StoppedPathSpace) : ℝ := a.val.1
def path (a : StoppedPathSpace) : C(ℝ, ExposureEuclidean) := a.val.2

theorem continuous_duration : Continuous duration := continuous_fst.comp continuous_subtype_val
theorem continuous_path : Continuous path := continuous_snd.comp continuous_subtype_val
theorem continuous_eval : Continuous (fun p : StoppedPathSpace × ℝ => p.1.path p.2) :=
  (continuous_path.comp continuous_fst).eval continuous_snd
theorem continuous_initial : Continuous (fun a : StoppedPathSpace => a.path 0) :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)
theorem continuous_terminal : Continuous (fun a : StoppedPathSpace => a.path a.duration) :=
  continuous_eval.comp (continuous_id.prodMk continuous_duration)

/-- Fixed initial and terminal laws survive narrow limits of ensembles,
including limits with zero-duration or non-simple paths. -/
theorem isClosed_endpointLaws (initial terminal : ProbabilityMeasure ExposureEuclidean) :
    IsClosed {η : ProbabilityMeasure StoppedPathSpace |
      η.map continuous_initial.measurable.aemeasurable = initial ∧
      η.map continuous_terminal.measurable.aemeasurable = terminal} :=
  (isClosed_eq (ProbabilityMeasure.continuous_map continuous_initial) continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_terminal) continuous_const)

theorem isClosed_carrier : IsClosed {c : ℝ × C(ℝ, ExposureEuclidean) |
    0 ≤ c.1 ∧ LipschitzWith 1 c.2 ∧ ∀ t, c.2 t = c.2 (max 0 (min t c.1))} := by
  refine (isClosed_le continuous_const continuous_fst).inter ?_
  refine ((isClosed_setOf_lipschitzWith 1).preimage
    (continuous_pi fun t => continuous_snd.eval (continuous_const (y := t)))).inter ?_
  change IsClosed {c : ℝ × C(ℝ, ExposureEuclidean) | ∀ t, c.2 t = c.2 (max 0 (min t c.1))}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro t
  apply isClosed_eq
  · exact continuous_snd.eval continuous_const
  · exact continuous_snd.eval (continuous_const.max (continuous_const.min continuous_fst))

private theorem isCompact_lipschitzPaths {K : Set ExposureEuclidean} (hK : IsCompact K) :
    IsCompact {f : C(ℝ, ExposureEuclidean) | LipschitzWith 1 f ∧ ∀ t, f t ∈ K} := by
  let S := {f : C(ℝ, ExposureEuclidean) | LipschitzWith 1 f ∧ ∀ t, f t ∈ K}
  have himage : ContinuousMap.toFun '' S =
      {f : ℝ → ExposureEuclidean | LipschitzWith 1 f} ∩ {f | ∀ t, f t ∈ K} := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg.1, hg.2⟩
    · rintro ⟨hl, hk⟩
      exact ⟨⟨f, hl.continuous⟩, ⟨hl, hk⟩, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous S
  · rw [himage]
    exact (isCompact_pi_infinite fun _ => hK).inter_left (isClosed_setOf_lipschitzWith 1)
  · apply Metric.equicontinuous_of_continuity_modulus id Filter.tendsto_id
    intro x y f
    simpa using f.property.1.dist_le_mul x y

/-- Compact cutoff sets in the relaxed space. Variable stopping times and
constant paths are included, so no unjustified closure of simple arcs is used. -/
theorem isCompact_cutoff {K : Set ExposureEuclidean} (hK : IsCompact K) (L : ℝ) :
    IsCompact {a : StoppedPathSpace | a.duration ≤ L ∧ ∀ t, a.path t ∈ K} := by
  have hc := (isCompact_Icc (a := (0 : ℝ)) (b := L)).prod (isCompact_lipschitzPaths hK)
  have he := isClosed_carrier.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  convert he using 1
  ext a
  simp only [mem_setOf_eq, mem_preimage, mem_prod, mem_Icc]
  constructor
  · rintro ⟨hL, hK⟩
    exact ⟨⟨a.property.1, hL⟩, a.property.2.1, hK⟩
  · rintro ⟨⟨_, hL⟩, _, hK⟩
    exact ⟨hL, hK⟩

/-- A first-moment bound controls the measure outside a compact path cutoff.
It does not assert uniform integrability of the duration-weighted tails. -/
theorem cutoff_compl_le (η : Measure StoppedPathSpace) {K : Set ExposureEuclidean}
    (hK : ∀ᵐ a ∂η, ∀ t, a.path t ∈ K) (M L : ℝ≥0) (hL : 0 < L)
    (hM : (∫⁻ a, ENNReal.ofReal a.duration ∂η) ≤ M) :
    η {a : StoppedPathSpace | a.duration ≤ L ∧ ∀ t, a.path t ∈ K}ᶜ ≤
      (M : ENNReal) / L := by
  have he : {a : StoppedPathSpace | a.duration ≤ L ∧ ∀ t, a.path t ∈ K}ᶜ
      =ᵐ[η] {a | (L : ℝ) < a.duration} := by
    filter_upwards [hK] with a ha
    apply propext
    change (¬(a.duration ≤ L ∧ ∀ t, a.path t ∈ K)) ↔ (L : ℝ) < a.duration
    simp [ha]
  rw [measure_congr he]
  calc η {a : StoppedPathSpace | (L : ℝ) < a.duration}
      ≤ η {a : StoppedPathSpace | (L : ENNReal) ≤ ENNReal.ofReal a.duration} := by
        apply measure_mono
        intro a ha
        simpa using ENNReal.ofReal_le_ofReal ha.le
    _ ≤ (∫⁻ a, ENNReal.ofReal a.duration ∂η) / (L : ENNReal) :=
      meas_ge_le_lintegral_div continuous_duration.measurable.ennreal_ofReal.aemeasurable
        (by exact_mod_cast hL.ne') ENNReal.coe_ne_top
    _ ≤ (M : ENNReal) / L := ENNReal.div_le_div_right hM _

/-- Uniform compact spatial support and bounded first moments of duration
make the supplied family tight in the relaxed path space. -/
theorem isTight_of_duration_bound (S : Set (Measure StoppedPathSpace))
    {K : Set ExposureEuclidean} (hK : IsCompact K) (M : ℝ≥0)
    (hpaths : ∀ η ∈ S, ∀ᵐ a ∂η, ∀ t, a.path t ∈ K)
    (hmoment : ∀ η ∈ S, (∫⁻ a, ENNReal.ofReal a.duration ∂η) ≤ M) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδ0 : 0 < δ := by exact_mod_cast hδ
  let R : ℝ≥0 := M / δ + 1
  have hR : 0 < R := by positivity
  have hdiv : M / R ≤ δ := (div_le_iff₀ hR).mpr (by
    dsimp [R]
    rw [mul_add, mul_div_cancel₀ M hδ0.ne', mul_one]
    exact le_add_of_nonneg_right (zero_le _))
  refine ⟨{a | a.duration ≤ (R : ℝ) ∧ ∀ t, a.path t ∈ K}, isCompact_cutoff hK R, ?_⟩
  intro η hη
  refine (cutoff_compl_le η (hpaths η hη) M R hR (hmoment η hη)).trans ?_
  have hdiv' : (M : ENNReal) / R ≤ δ := by
    rw [← ENNReal.coe_div hR.ne', ENNReal.coe_le_coe]
    exact hdiv
  exact hdiv'.trans hδε.le

/-- Prokhorov supplies compactness for already constructed probability
ensembles. Existence of ensembles representing a given current is separate. -/
theorem isCompact_closure_ensembles (S : Set (ProbabilityMeasure StoppedPathSpace))
    {K : Set ExposureEuclidean} (hK : IsCompact K) (M : ℝ≥0)
    (hpaths : ∀ η ∈ S, ∀ᵐ a ∂(η : Measure StoppedPathSpace), ∀ t, a.path t ∈ K)
    (hmoment : ∀ η ∈ S, (∫⁻ a, ENNReal.ofReal a.duration ∂(η : Measure StoppedPathSpace)) ≤ M) :
    IsCompact (closure S) := by
  apply isCompact_closure_of_isTightMeasureSet
  apply isTight_of_duration_bound _ hK M
  · rintro _ ⟨η, hη, rfl⟩
    exact hpaths η hη
  · rintro _ ⟨η, hη, rfl⟩
    exact hmoment η hη

end StoppedPathSpace

/-- The simple arcs embed without changing their duration or path. -/
def ArcSpace.toStoppedPath (a : ArcSpace) : StoppedPathSpace := by
  refine ⟨a.val, a.property.1.le, a.property.2.1, ?_⟩
  intro t
  by_cases ht : t ≤ 0
  · simpa [min_eq_left (ht.trans a.property.1.le), max_eq_left ht] using
      a.property.2.2.2.2.1 t ht
  · by_cases hL : a.val.1 ≤ t
    · simpa [min_eq_right hL, max_eq_right a.property.1.le] using
        a.property.2.2.2.2.2 t hL
    · simp [min_eq_left (le_of_not_ge hL), max_eq_right (le_of_not_ge ht)]

theorem ArcSpace.continuous_toStoppedPath : Continuous ArcSpace.toStoppedPath :=
  continuous_subtype_val.subtype_mk _

end CZExposure
