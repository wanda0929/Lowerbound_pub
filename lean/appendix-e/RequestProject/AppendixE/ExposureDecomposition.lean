module
public import RequestProject.AppendixE.ExposureCurrent
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Measure decompositions of the averaged exposure current (Appendix E support)

Paolini–Stepanov's decomposition theorem for acyclic normal currents (primary
reference: <https://arxiv.org/abs/1303.5664>, Def. 4.4 eq. (4.4) for the
endpoint pushforwards and Lemma 4.17 eq. (4.14) for the localized measure
equality on Borel sets) produces, at the level of measures, a product
decomposition of the current's mass together with endpoint laws.  This file
proves the measure-theoretic consequences of those raw identities:
`LocalizedMeasureDecomposition` is the localization identity, and
`ExposureMeasureDecomposition` is the measure data expected AFTER a geometric
arc decomposition and endpoint identification has been carried out.

No existence of a current or arc decomposition is asserted here, no component
measure is identified with an arc-length measure, and no tangent alignment or
normal-current compatibility is claimed.  Those remain outstanding.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- The localized measure identity `m s = ∫ component a s dη`, the measure-level
content of a product decomposition of `m`. -/
structure LocalizedMeasureDecomposition {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X]
    (η : Measure A) (m : Measure X) where
  component : A → Measure X
  measurable_component : Measurable component
  localized : ∀ s, MeasurableSet s →
    m s = ∫⁻ a, component a s ∂η

namespace LocalizedMeasureDecomposition

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    {η : Measure A} {m : Measure X}

theorem eq_bind (D : LocalizedMeasureDecomposition η m) :
    m = η.bind D.component := by
  ext s hs
  rw [Measure.bind_apply hs D.measurable_component.aemeasurable]
  exact D.localized s hs

theorem measurable_component_lintegral (D : LocalizedMeasureDecomposition η m)
    {w : X → ENNReal} (hw : Measurable w) :
    Measurable (fun a => ∫⁻ x, w x ∂D.component a) :=
  (Measure.measurable_lintegral hw).comp D.measurable_component

theorem lintegral_components (D : LocalizedMeasureDecomposition η m)
    {w : X → ENNReal} (hw : Measurable w) :
    (∫⁻ a, ∫⁻ x, w x ∂D.component a ∂η) = ∫⁻ x, w x ∂m := by
  conv_rhs => rw [D.eq_bind]
  exact (Measure.lintegral_bind D.measurable_component.aemeasurable
    hw.aemeasurable).symm

theorem ae_components (D : LocalizedMeasureDecomposition η m)
    {P : X → Prop} (hP : ∀ᵐ x ∂m, P x) :
    ∀ᵐ a ∂η, ∀ᵐ x ∂D.component a, P x := by
  rw [D.eq_bind] at hP
  exact Measure.ae_ae_of_ae_bind D.measurable_component.aemeasurable hP

end LocalizedMeasureDecomposition

/-- Measure data expected after a geometric arc decomposition and endpoint
identification: a probability ensemble over components, a mass measure
dominated by the current's variation, its localized decomposition, and the
source/sink endpoint laws.  The fields are raw measure data only — no
statement that the component measures are arc-lengths of curves or satisfy
any differential equation. -/
structure ExposureMeasureDecomposition (F : EuclideanExposureFlow)
    (A : Type*) [MeasurableSpace A] where
  ensemble : Measure A
  mass : Measure ExposureEuclidean
  mass_le : mass ≤ F.vectorMeasure.variation
  massDecomposition : LocalizedMeasureDecomposition ensemble mass
  initial : A → ExposureEuclidean
  terminal : A → ExposureEuclidean
  measurable_initial : Measurable initial
  measurable_terminal : Measurable terminal
  initial_law : Measure.map initial ensemble =
    Measure.dirac (exposureEuclideanEquiv y0)
  terminal_law : Measure.map terminal ensemble =
    Measure.dirac (exposureEuclideanEquiv yPi)

namespace ExposureMeasureDecomposition

variable {F : EuclideanExposureFlow} {A : Type*} [MeasurableSpace A]

theorem isProbabilityMeasure_ensemble (D : ExposureMeasureDecomposition F A) :
    IsProbabilityMeasure D.ensemble := by
  have h1 : (Measure.map D.initial D.ensemble) Set.univ = 1 := by
    rw [D.initial_law]
    simp
  rw [Measure.map_apply D.measurable_initial MeasurableSet.univ,
    Set.preimage_univ] at h1
  exact ⟨h1⟩

theorem ae_endpoints (D : ExposureMeasureDecomposition F A) :
    ∀ᵐ a ∂D.ensemble,
      D.initial a = exposureEuclideanEquiv y0 ∧
      D.terminal a = exposureEuclideanEquiv yPi := by
  have hmap0 : ∀ᵐ b ∂(Measure.map D.initial D.ensemble),
      b = exposureEuclideanEquiv y0 := by
    rw [D.initial_law]
    simp
  have hmapP : ∀ᵐ b ∂(Measure.map D.terminal D.ensemble),
      b = exposureEuclideanEquiv yPi := by
    rw [D.terminal_law]
    simp
  have h0 := MeasureTheory.ae_of_ae_map D.measurable_initial.aemeasurable hmap0
  have hP := MeasureTheory.ae_of_ae_map D.measurable_terminal.aemeasurable hmapP
  filter_upwards [h0, hP] with a ha0 haP
  exact ⟨ha0, haP⟩

/-- Inverse-speed time of a component measure. -/
def componentTime (D : ExposureMeasureDecomposition F A) (a : A) : ENNReal :=
  ∫⁻ z, F.exposureTimeWeight z ∂D.massDecomposition.component a

theorem measurable_componentTime (D : ExposureMeasureDecomposition F A) :
    Measurable D.componentTime :=
  D.massDecomposition.measurable_component_lintegral F.measurable_exposureTimeWeight

theorem average_componentTime (D : ExposureMeasureDecomposition F A) :
    (∫⁻ a, D.componentTime a ∂D.ensemble) =
      ∫⁻ z, F.exposureTimeWeight z ∂D.mass :=
  D.massDecomposition.lintegral_components F.measurable_exposureTimeWeight

theorem average_componentTime_le (D : ExposureMeasureDecomposition F A) :
    (∫⁻ a, D.componentTime a ∂D.ensemble) ≤ F.stateMeasure Set.univ := by
  rw [D.average_componentTime]
  exact F.weighted_submeasure_le D.mass_le

theorem ae_componentTime_lt_top (D : ExposureMeasureDecomposition F A) :
    ∀ᵐ a ∂D.ensemble, D.componentTime a < ⊤ := by
  exact ae_lt_top D.measurable_componentTime
    (D.average_componentTime_le.trans_lt F.finite_stateMeasure.measure_univ_lt_top).ne

theorem ae_component_domain (D : ExposureMeasureDecomposition F A) :
    ∀ᵐ a ∂D.ensemble, ∀ᵐ z ∂D.massDecomposition.component a,
      z ∈ euclideanExposureDomain := by
  have hm0 : D.mass euclideanExposureDomainᶜ = 0 := by
    apply le_antisymm _ (zero_le _)
    exact (D.mass_le euclideanExposureDomainᶜ).trans F.variation_support.le
  have hP : ∀ᵐ z ∂D.mass, z ∈ euclideanExposureDomain := mem_ae_iff.mpr hm0
  exact D.massDecomposition.ae_components hP

theorem ae_component_velocity_ne_zero (D : ExposureMeasureDecomposition F A) :
    ∀ᵐ a ∂D.ensemble, ∀ᵐ z ∂D.massDecomposition.component a,
      F.velocity z ≠ 0 := by
  have hwt : ∀ᵐ z ∂D.mass, F.exposureTimeWeight z < ⊤ :=
    ae_lt_top F.measurable_exposureTimeWeight
      (F.weighted_submeasure_lt_top D.mass_le).ne
  have hP : ∀ᵐ z ∂D.mass, F.velocity z ≠ 0 := by
    filter_upwards [hwt] with z hz hv0
    exact hz.ne (F.exposureTimeWeight_eq_top_of_velocity_eq_zero hv0)
  exact D.massDecomposition.ae_components hP

theorem exists_component_le_exposure_mass (D : ExposureMeasureDecomposition F A)
    (Good : A → Prop) (hGood : ∀ᵐ a ∂D.ensemble, Good a) :
    ∃ a, Good a ∧
      D.initial a = exposureEuclideanEquiv y0 ∧
      D.terminal a = exposureEuclideanEquiv yPi ∧
      (∀ᵐ z ∂D.massDecomposition.component a, z ∈ euclideanExposureDomain) ∧
      (∀ᵐ z ∂D.massDecomposition.component a, F.velocity z ≠ 0) ∧
      D.componentTime a ≤ F.stateMeasure Set.univ ∧
      D.componentTime a < ⊤ := by
  letI := D.isProbabilityMeasure_ensemble
  have hGood' : ∀ᵐ a ∂D.ensemble,
      (Good a ∧ D.initial a = exposureEuclideanEquiv y0 ∧
        D.terminal a = exposureEuclideanEquiv yPi ∧
        (∀ᵐ z ∂D.massDecomposition.component a, z ∈ euclideanExposureDomain) ∧
        ∀ᵐ z ∂D.massDecomposition.component a, F.velocity z ≠ 0) := by
    filter_upwards [hGood, D.ae_endpoints, D.ae_component_domain,
      D.ae_component_velocity_ne_zero] with a haG haEP haD haV
    exact ⟨haG, haEP.1, haEP.2, haD, haV⟩
  obtain ⟨a, hAll, hle, hlt⟩ := F.exists_component_le_exposure_mass D.ensemble
    D.componentTime
    (fun a => Good a ∧ D.initial a = exposureEuclideanEquiv y0 ∧
      D.terminal a = exposureEuclideanEquiv yPi ∧
      (∀ᵐ z ∂D.massDecomposition.component a, z ∈ euclideanExposureDomain) ∧
      ∀ᵐ z ∂D.massDecomposition.component a, F.velocity z ≠ 0)
    D.measurable_componentTime.aemeasurable hGood' D.mass_le
    D.average_componentTime
  obtain ⟨hG, hi, ht, hd, hv⟩ := hAll
  exact ⟨a, hG, hi, ht, hd, hv, hle, hlt⟩

end ExposureMeasureDecomposition

end CZExposure
