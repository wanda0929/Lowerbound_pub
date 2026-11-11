module
public import RequestProject.AppendixE.ExcursionSelection
public import RequestProject.AppendixE.ExposureSuperposition

/-!
# Record-level finite excursion selection

One record-to-trajectory lift works for every cutoff pair `0 < α < β`:
for each pair the retained `FiniteExcursionSelection` gives the count
bound, a total physical exposure inside the record's mass budget, and a
total duration `≤ T/α`.  The conditional theorem takes the
superposition schema explicitly; the wrapper uses the single named
external axiom `External.euclideanDirectedArcSuperposition`.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

theorem exists_finite_excursion_selections_of_record_of_superposition
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ ν Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t) ∧
        ∀ α : ℝ, 0 < α → ∀ β : ℝ, α < β →
          ∃ S : FiniteExcursionSelection T α β y u,
            (S.count : ℝ) * ((4/3 : ℝ) *
              (costThreeHalves β - costThreeHalves α)) ≤ T ∧
            ENNReal.ofReal (∑ i, (S.segment i).physicalExposure) ≤
              ν Set.univ ∧
            (∑ i, (S.segment i).duration) ≤ T / α := by
  obtain ⟨T, hT0, hTm, y, u, hu, hub, ⟨K, hK⟩, hy0, hyT, hdom, hode⟩ :=
    exists_exposure_time_trajectory_of_record_of_superposition
      hSuperposition ν hν
  refine ⟨T, hT0, hTm, y, u, hu, hub, ⟨K, hK⟩, hy0, hyT, hdom, hode, ?_⟩
  intro α hα β hαβ
  obtain ⟨S, hcb, hexp, hdur⟩ := exists_finite_excursion_selection
    hT0.le hα hαβ hK hu hub hdom hode hy0 hyT
  refine ⟨S, hcb, ?_, hdur⟩
  exact (ENNReal.ofReal_le_ofReal
    (S.exposure_le hT0.le)).trans hTm

theorem exists_finite_excursion_selections_of_record
    (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ ν Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        (∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t) ∧
        ∀ α : ℝ, 0 < α → ∀ β : ℝ, α < β →
          ∃ S : FiniteExcursionSelection T α β y u,
            (S.count : ℝ) * ((4/3 : ℝ) *
              (costThreeHalves β - costThreeHalves α)) ≤ T ∧
            ENNReal.ofReal (∑ i, (S.segment i).physicalExposure) ≤
              ν Set.univ ∧
            (∑ i, (S.segment i).duration) ≤ T / α :=
  exists_finite_excursion_selections_of_record_of_superposition
    External.euclideanDirectedArcSuperposition ν hν

end CZExposure
