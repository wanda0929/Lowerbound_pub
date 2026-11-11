module
public import RequestProject.AppendixE.CurrentArcDecomposition

/-! Polar alignment from source-shaped mass and vector-current identities.
The source data remain explicit: this module does not construct the current
representation or the Paolini–Stepanov decomposition. No field assumes
tangent alignment or a vanishing directional defect. -/

@[expose] public section
noncomputable section
namespace CZExposure.EuclideanCurrentArcData
open MeasureTheory Set
open scoped InnerProductSpace

variable {T : EuclideanNormalCurrentData} {source sink : ExposureEuclidean}
    {A : Type*} [MeasurableSpace A]

/-- Pair a bounded vector field with the oriented tangent of one arc. -/
def arcPairing (γ : EuclideanArc) (q : ExposureEuclidean → ExposureEuclidean) : ℝ :=
  ∫ s, ⟪q (γ.path s), deriv γ.path s⟫_ℝ ∂γ.parameterMeasure

/-- Localized component masses determine the arc-length function almost
everywhere; no measurable choice of parametrized paths is required. -/
theorem ae_length_eq_component_mass (D : EuclideanCurrentArcData T source sink A) :
    (fun a => (D.arc a).length) =ᵐ[D.ensemble]
      (fun a => (D.massDecomposition.component a univ).toReal) := by
  filter_upwards [D.component_eq] with a ha
  rw [ha, EuclideanArc.lengthMeasure_univ, ENNReal.toReal_ofReal (D.arc a).length_pos.le]

/-- A measurable realization of the arc ensemble and its tangents. Tangents
are derivatives, not assumed equal to the parent's polar direction. -/
structure MeasurableArcs (D : EuclideanCurrentArcData T source sink A) where
  path_measurable : Measurable (fun p : A × ℝ => (D.arc p.1).path p.2)
  tangent : A × ℝ → ExposureEuclidean
  tangent_measurable : Measurable tangent
  tangent_deriv : ∀ᵐ a ∂D.ensemble, ∀ᵐ s ∂(D.arc a).parameterMeasure,
    HasDerivAt (D.arc a).path (tangent (a, s)) s

/-- For a continuously parametrized ensemble, joint tangent measurability
comes from mathlib's derivative-with-parameters theorem. -/
def MeasurableArcs.of_continuous [TopologicalSpace A] [SecondCountableTopology A]
    [BorelSpace A] (D : EuclideanCurrentArcData T source sink A)
    (hp : Continuous (fun p : A × ℝ => (D.arc p.1).path p.2)) : D.MeasurableArcs where
  path_measurable := hp.measurable
  tangent := fun p => deriv (D.arc p.1).path p.2
  tangent_measurable := measurable_deriv_with_param (f := fun a => (D.arc a).path) hp
  tangent_deriv := Filter.Eventually.of_forall fun a =>
    (D.arc a).unit_speed.mono fun s ⟨v, hv, _⟩ => by rwa [hv.deriv]

/-- Jointly measurable positions and tangents imply measurable pairings for
every measurable vector field. Arc lengths need not be measurable everywhere:
the localized component mass supplies a measurable almost-everywhere version.
No bound or integrability of the test field is needed for this conclusion. -/
theorem MeasurableArcs.pairing_measurable {D : EuclideanCurrentArcData T source sink A}
    (M : D.MeasurableArcs) {q : ExposureEuclidean → ExposureEuclidean}
    (hq : Measurable q) :
    AEStronglyMeasurable (fun a => arcPairing (D.arc a) q) D.ensemble := by
  let L : A → ℝ := fun a => (D.massDecomposition.component a univ).toReal
  have hL : Measurable L :=
    ((Measure.measurable_coe MeasurableSet.univ).comp
      D.massDecomposition.measurable_component).ennreal_toReal
  let f : A × ℝ → ℝ := {p : A × ℝ | p.2 ∈ Icc 0 (L p.1)}.indicator
    (fun p => ⟪q ((D.arc p.1).path p.2), M.tangent p⟫_ℝ)
  have hf : Measurable f :=
    ((hq.comp M.path_measurable).inner M.tangent_measurable).indicator
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (hL.comp measurable_fst)))
  have hi : StronglyMeasurable (fun a => ∫ s, f (a, s)) :=
    hf.stronglyMeasurable.integral_prod_right'
  apply hi.aestronglyMeasurable.congr
  filter_upwards [D.ae_length_eq_component_mass, M.tangent_deriv] with a ha hd
  have he : (fun s => f (a, s)) = (Icc 0 (D.arc a).length).indicator
      (fun s => ⟪q ((D.arc a).path s), M.tangent (a, s)⟫_ℝ) := by
    funext s
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq, L, ← ha]
  rw [he, integral_indicator measurableSet_Icc]
  exact integral_congr_ae (hd.mono fun s hs => by dsimp; rw [hs.deriv])

/-- Finite retained mass gives integrable arc lengths and their exact mean. -/
theorem length_integrable_and_integral (D : EuclideanCurrentArcData T source sink A) :
    Integrable (fun a => (D.arc a).length) D.ensemble ∧
      (∫ a, (D.arc a).length ∂D.ensemble) = D.retained.variation.real univ := by
  letI := T.finite_variation
  have hfin := D.subcurrent.variation_univ_lt_top (measure_lt_top _ _)
  have hm : Measurable (fun a => D.massDecomposition.component a univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp D.massDecomposition.measurable_component
  have he := (D.massDecomposition.localized univ MeasurableSet.univ).symm
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (he.trans_lt hfin).ne
  refine ⟨hi.congr D.ae_length_eq_component_mass.symm, ?_⟩
  rw [integral_congr_ae D.ae_length_eq_component_mass,
    integral_toReal hm.aemeasurable (ae_lt_top hm (he.trans_lt hfin).ne), he]
  rfl

/-- Scalar mass preservation follows from localization and subcurrent
additivity, rather than being an additional source assumption. -/
theorem mass_identity (D : EuclideanCurrentArcData T source sink A) :
    T.vectorMeasure.variation.real univ =
      (T.vectorMeasure - D.retained).variation.real univ +
        ∫ a, (D.arc a).length ∂D.ensemble := by
  letI := T.finite_variation
  have hfin := measure_lt_top T.vectorMeasure.variation univ
  rw [D.length_integrable_and_integral.2]
  have he := congrArg ENNReal.toReal D.subcurrent.totalMass_eq
  rw [ENNReal.toReal_add (D.subcurrent.complement.variation_univ_lt_top hfin).ne
    (D.subcurrent.variation_univ_lt_top hfin).ne] at he
  exact he.symm

/-- Source-level integral identities after cycle removal and parametrization.
`current` retains the discarded cycle's vector contribution. Scalar mass
and length integrability are already proved from the localized decomposition.
The remaining measurability field records the ensemble-test measurability
for bounded measurable tests, not any directional conclusion. -/
structure CurrentIdentity (D : EuclideanCurrentArcData T source sink A) where
  remainderDirection : ExposureEuclidean → ExposureEuclidean
  remainder_measurable : Measurable remainderDirection
  remainder_unit : ∀ᵐ x ∂(T.vectorMeasure - D.retained).variation,
    ‖remainderDirection x‖ = 1
  pairing_measurable : ∀ q : ExposureEuclidean → ExposureEuclidean,
    Measurable q → (∀ x, ‖q x‖ ≤ 1) →
    AEStronglyMeasurable (fun a => arcPairing (D.arc a) q) D.ensemble
  current : ∀ q : ExposureEuclidean → ExposureEuclidean,
    Measurable q → (∀ x, ‖q x‖ ≤ 1) →
    (∫ x, ⟪q x, T.direction x⟫_ℝ ∂T.vectorMeasure.variation) =
      (∫ x, ⟪q x, remainderDirection x⟫_ℝ
        ∂(T.vectorMeasure - D.retained).variation) +
      ∫ a, arcPairing (D.arc a) q ∂D.ensemble

/-- Build the current-identity interface from measurable arc data without
assuming measurability of every tested pairing separately. -/
def CurrentIdentity.of_measurableArcs {D : EuclideanCurrentArcData T source sink A}
    (M : D.MeasurableArcs) (r : ExposureEuclidean → ExposureEuclidean)
    (hr : Measurable r)
    (hu : ∀ᵐ x ∂(T.vectorMeasure - D.retained).variation, ‖r x‖ = 1)
    (hc : ∀ q : ExposureEuclidean → ExposureEuclidean,
      Measurable q → (∀ x, ‖q x‖ ≤ 1) →
      (∫ x, ⟪q x, T.direction x⟫_ℝ ∂T.vectorMeasure.variation) =
        (∫ x, ⟪q x, r x⟫_ℝ ∂(T.vectorMeasure - D.retained).variation) +
        ∫ a, arcPairing (D.arc a) q ∂D.ensemble) : D.CurrentIdentity where
  remainderDirection := r
  remainder_measurable := hr
  remainder_unit := hu
  pairing_measurable := fun _ hq _ => M.pairing_measurable hq
  current := hc

private theorem unit_eq_of_inner_eq_one {x y : ExposureEuclidean}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (h : ⟪x, y⟫_ℝ = 1) : y = x := by
  have hn := norm_sub_sq_real x y
  rw [hx, hy, h] at hn
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

private theorem arc_pairing_integrable (γ : EuclideanArc)
    {q : ExposureEuclidean → ExposureEuclidean} (hq : Measurable q)
    (hb : ∀ x, ‖q x‖ ≤ 1) :
    Integrable (fun s => ⟪q (γ.path s), deriv γ.path s⟫_ℝ) γ.parameterMeasure := by
  haveI : IsFiniteMeasure γ.parameterMeasure := by
    dsimp [EuclideanArc.parameterMeasure]; infer_instance
  apply (integrable_const (1 : ℝ)).mono'
    ((hq.comp γ.lipschitz.continuous.measurable).inner (measurable_deriv _)).aestronglyMeasurable
  filter_upwards [γ.unit_speed] with s ⟨v, hv, hn⟩
  rw [hv.deriv]
  exact (norm_inner_le_norm _ _).trans (by simpa [hn] using hb (γ.path s))

private theorem arc_pairing_le_length (γ : EuclideanArc)
    {q : ExposureEuclidean → ExposureEuclidean} (hq : Measurable q)
    (hb : ∀ x, ‖q x‖ ≤ 1) : arcPairing γ q ≤ γ.length := by
  haveI : IsFiniteMeasure γ.parameterMeasure := by
    dsimp [EuclideanArc.parameterMeasure]; infer_instance
  have h := integral_mono_ae (arc_pairing_integrable γ hq hb)
    (integrable_const (1 : ℝ)) (by
      filter_upwards [γ.unit_speed] with s ⟨v, hv, hn⟩
      rw [hv.deriv]
      exact (real_inner_le_norm _ _).trans (by simpa [hn] using hb (γ.path s)))
  simpa [arcPairing, integral_const, EuclideanArc.parameterMeasure,
    Measure.real, Real.volume_Icc, γ.length_pos.le] using h

/-- Bounded current tests are integrable because their absolute pairings
are bounded by the already integrable arc lengths. Only measurability of
the ensemble pairing remains part of the source data. -/
theorem CurrentIdentity.pairing_integrable {D : EuclideanCurrentArcData T source sink A}
    (H : D.CurrentIdentity) {q : ExposureEuclidean → ExposureEuclidean}
    (hq : Measurable q) (hb : ∀ x, ‖q x‖ ≤ 1) :
    Integrable (fun a => arcPairing (D.arc a) q) D.ensemble := by
  apply D.length_integrable_and_integral.1.mono' (H.pairing_measurable q hq hb)
  apply Filter.Eventually.of_forall
  intro a
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨?_, arc_pairing_le_length _ hq hb⟩
  have h := arc_pairing_le_length (D.arc a) hq.neg (fun x => by simpa using hb x)
  simp only [arcPairing, inner_neg_left, integral_neg] at h ⊢
  linarith

/-- Mass preservation plus the full vector identity forces arc tangents to
equal the parent's polar direction, even when a cycle was discarded. -/
theorem CurrentIdentity.isDirected {D : EuclideanCurrentArcData T source sink A}
    (H : D.CurrentIdentity) : D.IsDirected := by
  letI := T.finite_variation
  have hfin := D.subcurrent.complement.variation_univ_lt_top
    (measure_lt_top T.vectorMeasure.variation univ)
  haveI : IsFiniteMeasure (T.vectorMeasure - D.retained).variation := ⟨hfin⟩
  let q : ExposureEuclidean → ExposureEuclidean := fun x =>
    if ‖T.direction x‖ = 1 then T.direction x else 0
  have hq : Measurable q := T.measurable_direction.ite
    (T.measurable_direction.norm (measurableSet_singleton 1)) measurable_const
  have hb : ∀ x, ‖q x‖ ≤ 1 := by
    intro x; dsimp [q]; split <;> simp_all
  have heq : q =ᵐ[T.vectorMeasure.variation] T.direction :=
    T.direction_unit.mono fun x hx => by simp [q, hx]
  have hparent : (∫ x, ⟪q x, T.direction x⟫_ℝ ∂T.vectorMeasure.variation) =
      T.vectorMeasure.variation.real univ := by
    calc
      _ = ∫ _, (1 : ℝ) ∂T.vectorMeasure.variation := integral_congr_ae (by
        filter_upwards [heq, T.direction_unit] with x hx hn
        simp [hx, hn])
      _ = _ := by simp
  have hrint : Integrable (fun x => ⟪q x, H.remainderDirection x⟫_ℝ)
      (T.vectorMeasure - D.retained).variation := by
    apply (integrable_const (1 : ℝ)).mono'
      (hq.inner H.remainder_measurable).aestronglyMeasurable
    filter_upwards [H.remainder_unit] with x hx
    exact (norm_inner_le_norm _ _).trans (by simpa [hx] using hb x)
  have hrle : (∫ x, ⟪q x, H.remainderDirection x⟫_ℝ
      ∂(T.vectorMeasure - D.retained).variation) ≤
        (T.vectorMeasure - D.retained).variation.real univ := by
    have h := integral_mono_ae hrint (integrable_const (1 : ℝ)) (by
      filter_upwards [H.remainder_unit] with x hx
      exact (real_inner_le_norm _ _).trans (by simpa [hx] using hb x))
    simpa using h
  have hi := H.pairing_integrable hq hb
  have hn : ∀ a, 0 ≤ (D.arc a).length - arcPairing (D.arc a) q :=
    fun a => sub_nonneg.mpr (arc_pairing_le_length (D.arc a) hq hb)
  have hlength := D.length_integrable_and_integral.1
  have hzero : (∫ a, (D.arc a).length - arcPairing (D.arc a) q ∂D.ensemble) = 0 := by
    rw [integral_sub hlength hi]
    have hc := H.current q hq hb
    rw [hparent] at hc
    have hm := D.mass_identity
    have hnonneg := integral_nonneg_of_ae (μ := D.ensemble) (Filter.Eventually.of_forall hn)
    rw [integral_sub hlength hi] at hnonneg
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hn (hlength.sub hi)).mp hzero
  have hunit := D.massDecomposition.ae_components
    (ae_mono (D.subcurrent.variation_le (measure_lt_top _ _)) T.direction_unit)
  filter_upwards [hae, hunit, D.component_eq] with a ha hu hcomp
  rw [hcomp] at hu
  have hpath := (D.arc a).ae_path_of_ae_lengthMeasure hu
  haveI : IsFiniteMeasure (D.arc a).parameterMeasure := by
    dsimp [EuclideanArc.parameterMeasure]; infer_instance
  have hni : ∀ᵐ s ∂(D.arc a).parameterMeasure,
      0 ≤ 1 - ⟪q ((D.arc a).path s), deriv (D.arc a).path s⟫_ℝ := by
    filter_upwards [(D.arc a).unit_speed] with s ⟨v, hv, hvn⟩
    rw [hv.deriv]
    exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa [hvn] using hb _))
  have hzi : (∫ s, 1 - ⟪q ((D.arc a).path s), deriv (D.arc a).path s⟫_ℝ
      ∂(D.arc a).parameterMeasure) = 0 := by
    rw [integral_sub (integrable_const 1) (arc_pairing_integrable _ hq hb)]
    simpa [arcPairing, integral_const, EuclideanArc.parameterMeasure, Measure.real,
      Real.volume_Icc, (D.arc a).length_pos.le] using ha
  have hz := (integral_eq_zero_iff_of_nonneg_ae hni
    ((integrable_const 1).sub (arc_pairing_integrable _ hq hb))).mp hzi
  filter_upwards [hz, hpath, (D.arc a).unit_speed] with s hs hp ⟨v, hv, hvn⟩
  have hqpath : q ((D.arc a).path s) = T.direction ((D.arc a).path s) := by simp [q, hp]
  rw [hqpath, hv.deriv] at hs
  simp only [Pi.zero_apply] at hs
  have hvEq := unit_eq_of_inner_eq_one hp hvn (by linarith)
  rwa [hvEq] at hv

end CZExposure.EuclideanCurrentArcData

namespace CZExposure
open MeasureTheory Set

/-- Source-shaped alternative to directed superposition. This still assumes
existence of the geometric decomposition and its integral identities, but
does not assume any alignment of arc tangents. -/
def EuclideanCurrentSuperposition : Prop :=
  ∀ (T : EuclideanNormalCurrentData) (source sink : ExposureEuclidean),
    source ≠ sink →
    T.boundaryPlus = Measure.dirac sink →
    T.boundaryMinus = Measure.dirac source →
    (∃ K : Set ExposureEuclidean, IsCompact K ∧
      T.vectorMeasure.variation Kᶜ = 0) →
    ∃ (A : Type) (mA : MeasurableSpace A)
      (D : @EuclideanCurrentArcData T source sink A mA), Nonempty D.CurrentIdentity

/-- Every downstream explicitly conditional result can now take the
source-shaped input through this proved implication. -/
theorem EuclideanCurrentSuperposition.directed (h : EuclideanCurrentSuperposition) :
    EuclideanDirectedArcSuperposition := by
  intro T source sink hne hplus hminus hcompact
  obtain ⟨A, mA, D, ⟨H⟩⟩ := h T source sink hne hplus hminus hcompact
  exact ⟨A, mA, D, H.isDirected⟩

end CZExposure
