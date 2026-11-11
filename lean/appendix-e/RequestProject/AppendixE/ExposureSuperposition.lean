module
public import RequestProject.AppendixE.CurrentArcDecomposition

/-!
# External superposition corollary and final conditional trajectory theorems

This module isolates the SINGLE external geometric assumption
`External.euclideanDirectedArcSuperposition` — a combined Euclidean corollary
(current representation/metric identification, cycle removal, mass-preserving
arc decomposition with endpoint laws, measurable unit-speed representatives,
polar/tangent alignment) that is broader than literal PS Thm. 5.1 — and
applies it to obtain the exposure-time trajectory existences.  No physical
pulse or `Cstar ≤ pRelaxed` claim.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

namespace External

/-- External Euclidean directed-arc superposition corollary.
This packages current representation, cycle removal, mass-preserving arc
decomposition and endpoint laws, measurable unit-speed representatives,
and polar/tangent alignment.  It is NOT the verbatim PS5.1 statement;
see CurrentArcDecomposition and README for the precise assumed scope.
No physical-pulse or exposure-cost conclusion is assumed here. -/
axiom euclideanDirectedArcSuperposition : EuclideanDirectedArcSuperposition

end External

namespace EuclideanExposureFlow

theorem exists_exposure_time_trajectory (F : EuclideanExposureFlow) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ F.stateMeasure Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t :=
  F.exists_exposure_time_trajectory_of_superposition
    External.euclideanDirectedArcSuperposition

end EuclideanExposureFlow

theorem exists_exposure_time_trajectory_of_record
    (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ ν Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t :=
  exists_exposure_time_trajectory_of_record_of_superposition
    External.euclideanDirectedArcSuperposition ν hν

end CZExposure
