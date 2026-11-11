module
public import RequestProject.AppendixE.ExposurePolarCurrent
public import RequestProject.AppendixE.ExposureSubcurrent
public import RequestProject.AppendixE.ExposureReparamODE

/-!
# Directed-arc superposition schema (Appendix E support)

This module defines the DATA consumed from a geometric arc decomposition —
a retained subcurrent (proved localized mass bound via `IsVectorSubcurrent`),
a localized measure decomposition, unit-speed arcs, and Dirac endpoint laws —
plus the `IsDirected` tangent-alignment predicate and the
`EuclideanDirectedArcSuperposition` hypothesis schema.  The schema packages
the unformalized Euclidean representation/metric identification (Smirnov
counterpart per PS Remark 4.5), cycle removal (Prop. 3.8), mass-preserving
decomposition (Def. 4.4), local mass/current identities (Lemma 4.17), and
polar/tangent compatibility; it is not verbatim PS Thm. 5.1 and carries no
exposure/pulse content.  All downstream theorems take the hypothesis
explicitly.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- Mass and arc data needed from a geometric decomposition.  Does not claim
by itself a full current-valued integral identity or acyclicity. -/
structure EuclideanCurrentArcData (T : EuclideanNormalCurrentData)
    (source sink : ExposureEuclidean) (A : Type*) [MeasurableSpace A] where
  retained : VectorMeasure ExposureEuclidean ExposureEuclidean
  subcurrent : IsVectorSubcurrent retained T.vectorMeasure
  ensemble : Measure A
  massDecomposition : LocalizedMeasureDecomposition ensemble retained.variation
  arc : A → EuclideanArc
  component_eq : ∀ᵐ a ∂ensemble,
    massDecomposition.component a = (arc a).lengthMeasure
  measurable_initial : Measurable (fun a => (arc a).path 0)
  measurable_terminal : Measurable (fun a => (arc a).path (arc a).length)
  initial_law : Measure.map (fun a => (arc a).path 0) ensemble =
    Measure.dirac source
  terminal_law : Measure.map (fun a => (arc a).path (arc a).length) ensemble =
    Measure.dirac sink

namespace EuclideanCurrentArcData

variable {T : EuclideanNormalCurrentData} {source sink : ExposureEuclidean}
    {A : Type*} [MeasurableSpace A]

/-- Arcs follow the parent current's polar direction.  Kept explicitly
separate from mass-and-endpoint accounting. -/
def IsDirected (D : EuclideanCurrentArcData T source sink A) : Prop :=
  ∀ᵐ a ∂D.ensemble, ∀ᵐ s ∂(D.arc a).parameterMeasure,
    HasDerivAt (D.arc a).path (T.direction ((D.arc a).path s)) s

end EuclideanCurrentArcData

/-- General Euclidean directed-arc superposition hypothesis, in the fixed
Euclidean space.  This schema includes the unformalized representation,
cycle-removal, parametrization, and polar-alignment consequences; it is not
verbatim Paolini–Stepanov 5.1 and has no exposure/pulse conclusion. -/
def EuclideanDirectedArcSuperposition : Prop :=
  ∀ (T : EuclideanNormalCurrentData) (source sink : ExposureEuclidean),
    source ≠ sink →
    T.boundaryPlus = Measure.dirac sink →
    T.boundaryMinus = Measure.dirac source →
    (∃ K : Set ExposureEuclidean, IsCompact K ∧
      T.vectorMeasure.variation Kᶜ = 0) →
    ∃ (A : Type) (mA : MeasurableSpace A)
      (D : @EuclideanCurrentArcData T source sink A mA),
      @EuclideanCurrentArcData.IsDirected T source sink A mA D

theorem exposureEuclidean_y0_ne_yPi :
    exposureEuclideanEquiv y0 ≠ exposureEuclideanEquiv yPi := by
  intro h
  have h' := exposureEuclideanEquiv.injective h
  have h0 := congrFun h' (0 : Fin 11)
  norm_num [y0, yPi] at h0

namespace EuclideanCurrentArcData

variable {F : EuclideanExposureFlow} {A : Type*} [MeasurableSpace A]

/-- Bridge a general-current decomposition to the exposure decomposition:
`mass_le` is now proved from the subcurrent total-mass condition. -/
def toExposureDecomposition
    (D : EuclideanCurrentArcData F.toNormalCurrentData
      (exposureEuclideanEquiv y0) (exposureEuclideanEquiv yPi) A) :
    ExposureMeasureDecomposition F A :=
  ExposureMeasureDecomposition.ofSubcurrent F D.retained D.subcurrent
    D.ensemble D.massDecomposition
    (fun a => (D.arc a).path 0)
    (fun a => (D.arc a).path (D.arc a).length)
    D.measurable_initial D.measurable_terminal D.initial_law D.terminal_law

/-- The same arcs realize the exposure decomposition; endpoint maps coincide
definitionally. -/
def toExposureArcRealization
    (D : EuclideanCurrentArcData F.toNormalCurrentData
      (exposureEuclideanEquiv y0) (exposureEuclideanEquiv yPi) A) :
    ExposureArcRealization D.toExposureDecomposition where
  arc := D.arc
  component_eq := D.component_eq
  initial_eq := Filter.Eventually.of_forall (fun _ => rfl)
  terminal_eq := Filter.Eventually.of_forall (fun _ => rfl)

end EuclideanCurrentArcData

theorem EuclideanArc.isDirectedBy_iff_polar (γ : EuclideanArc)
    (F : EuclideanExposureFlow) :
    γ.IsDirectedBy F ↔
      ∀ᵐ s ∂γ.parameterMeasure,
        HasDerivAt γ.path (F.polarDirection (γ.path s)) s := Iff.rfl

namespace EuclideanCurrentArcData

variable {F : EuclideanExposureFlow} {A : Type*} [MeasurableSpace A]

/-- Direction along the polar field of the parent current transports to
`IsDirectedBy` of the realized arcs (`direction` is definitionally
`F.polarDirection`). -/
theorem ae_isDirectedBy
    (D : EuclideanCurrentArcData F.toNormalCurrentData
      (exposureEuclideanEquiv y0) (exposureEuclideanEquiv yPi) A)
    (hD : D.IsDirected) :
    ∀ᵐ a ∂D.toExposureDecomposition.ensemble,
      (D.toExposureArcRealization.arc a).IsDirectedBy F :=
  hD.mono fun a ha =>
    (EuclideanArc.isDirectedBy_iff_polar (D.arc a) F).mpr ha

end EuclideanCurrentArcData

namespace EuclideanExposureFlow

/-- The full record-independent implication: any flow satisfying the
superposition hypothesis yields an exposure-time trajectory.  All chain
links are proved; the only unproved input is the hypothesis argument. -/
theorem exists_exposure_time_trajectory_of_superposition
    (F : EuclideanExposureFlow)
    (hSuperposition : EuclideanDirectedArcSuperposition) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ F.stateMeasure Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t := by
  obtain ⟨A, mA, D, hD⟩ := hSuperposition F.toNormalCurrentData
    (exposureEuclideanEquiv y0) (exposureEuclideanEquiv yPi)
    exposureEuclidean_y0_ne_yPi rfl rfl
    ⟨euclideanExposureDomain, isCompact_euclideanExposureDomain,
      F.variation_support⟩
  letI : MeasurableSpace A := mA
  exact D.toExposureArcRealization.exists_exposure_time_trajectory
    (D.ae_isDirectedBy hD)

end EuclideanExposureFlow

/-- Conditional record-to-trajectory implication: the full
averaging → current → arc data → cost selection → clock → ODE chain,
conditional on the generic Euclidean geometry hypothesis. -/
theorem exists_exposure_time_trajectory_of_record_of_superposition
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ ν Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t := by
  obtain ⟨F, _, hmass⟩ := exists_euclidean_exposure_flow ν hν
  simpa only [hmass] using
    F.exists_exposure_time_trajectory_of_superposition hSuperposition

end CZExposure
