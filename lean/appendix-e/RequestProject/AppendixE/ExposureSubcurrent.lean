module
public import RequestProject.AppendixE.ExposureDecomposition
public import RequestProject.AppendixE.VectorSubcurrent

/-!
# Subcurrents of the exposure current (Appendix E support)

Applies the vector-measure subcurrent algebra of `VectorSubcurrent.lean` to
`F.vectorMeasure`: a vector measure `S` satisfying the PS Def. 3.1 condition
`M(T - S) + M(S) ≤ M(T)` has its variation dominated by `F`'s variation
(finite total variation makes the localization valid), inherits the
compact-domain support, and satisfies the same inverse-speed budget bound.
`ofSubcurrent` packages this as `ExposureMeasureDecomposition` data without
any separately supplied `mass_le` premise.  No cycle removal, acyclicity,
boundary preservation, tangent alignment, or normal-current correspondence
is asserted.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

namespace EuclideanExposureFlow

theorem subcurrent_variation_le (F : EuclideanExposureFlow)
    {S : VectorMeasure ExposureEuclidean ExposureEuclidean}
    (hS : IsVectorSubcurrent S F.vectorMeasure) :
    S.variation ≤ F.vectorMeasure.variation :=
  hS.variation_le F.variation_univ_lt_top

theorem subcurrent_variation_support (F : EuclideanExposureFlow)
    {S : VectorMeasure ExposureEuclidean ExposureEuclidean}
    (hS : IsVectorSubcurrent S F.vectorMeasure) :
    S.variation euclideanExposureDomainᶜ = 0 :=
  hS.variation_null F.variation_univ_lt_top F.variation_support

theorem weighted_subcurrent_le (F : EuclideanExposureFlow)
    {S : VectorMeasure ExposureEuclidean ExposureEuclidean}
    (hS : IsVectorSubcurrent S F.vectorMeasure) :
    (∫⁻ z, F.exposureTimeWeight z ∂S.variation) ≤ F.stateMeasure Set.univ :=
  F.weighted_submeasure_le (F.subcurrent_variation_le hS)

theorem weighted_subcurrent_lt_top (F : EuclideanExposureFlow)
    {S : VectorMeasure ExposureEuclidean ExposureEuclidean}
    (hS : IsVectorSubcurrent S F.vectorMeasure) :
    (∫⁻ z, F.exposureTimeWeight z ∂S.variation) < ⊤ :=
  F.weighted_submeasure_lt_top (F.subcurrent_variation_le hS)

end EuclideanExposureFlow

namespace ExposureMeasureDecomposition

variable {F : EuclideanExposureFlow} {A : Type*} [MeasurableSpace A]

/-- Decomposition data whose mass is the variation of an actual subcurrent:
`mass_le` is proved, not supplied.  Conditional data — no existence claim. -/
def ofSubcurrent (F : EuclideanExposureFlow)
    (S : VectorMeasure ExposureEuclidean ExposureEuclidean)
    (hS : IsVectorSubcurrent S F.vectorMeasure)
    (η : Measure A) (D : LocalizedMeasureDecomposition η S.variation)
    (initial terminal : A → ExposureEuclidean)
    (h_initial : Measurable initial) (h_terminal : Measurable terminal)
    (initial_law : Measure.map initial η = Measure.dirac (exposureEuclideanEquiv y0))
    (terminal_law : Measure.map terminal η = Measure.dirac (exposureEuclideanEquiv yPi)) :
    ExposureMeasureDecomposition F A where
  ensemble := η
  mass := S.variation
  mass_le := F.subcurrent_variation_le hS
  massDecomposition := D
  initial := initial
  terminal := terminal
  measurable_initial := h_initial
  measurable_terminal := h_terminal
  initial_law := initial_law
  terminal_law := terminal_law

end ExposureMeasureDecomposition

end CZExposure
