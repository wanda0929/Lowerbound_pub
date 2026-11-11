module
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Variation bounds for vector measures (Appendix E support)

Two generic comparison lemmas: a vector measure whose values are dominated in
`enorm` by a scalar measure `m` on every measurable set has `variation ≤ m`, and
a density-defined vector measure `μ.withDensityᵥ v` has variation dominated by
`μ.withDensity (‖v ·‖ₑ)`. These are upper bounds only; no equality of variation
with the norm density is asserted here.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- If a vector measure is pointwise dominated by a scalar measure in `enorm`,
its variation is dominated by that measure. -/
theorem vectorMeasure_variation_le_of_bound
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (T : MeasureTheory.VectorMeasure X E) (m : MeasureTheory.Measure X)
    (h : ∀ s, MeasurableSet s → ‖T s‖ₑ ≤ m s) :
    T.variation ≤ m := by
  rw [Measure.le_iff]
  intro s hs
  show (MeasureTheory.ennrealPreVariation (‖T ·‖ₑ) _ _).ennrealToMeasure s ≤ m s
  rw [VectorMeasure.ennrealToMeasure_apply hs]
  show MeasureTheory.preVariationFun (‖T ·‖ₑ) s ≤ m s
  rw [MeasureTheory.preVariationFun, dif_pos hs]
  refine iSup_le fun P => ?_
  have hdisj : Set.PairwiseDisjoint {p : Subtype MeasurableSet | p ∈ P.parts}
      (fun p : Subtype MeasurableSet => p.val) := by
    intro p hp q hq hpq
    simp only [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    have hd : Disjoint p q := by
      have h := P.supIndep (Finset.singleton_subset_iff.mpr hq) hp
        (Finset.notMem_singleton.mpr hpq)
      rwa [Finset.sup_singleton] at h
    simp only [disjoint_iff, Subtype.ext_iff] at hd
    exact hd
  have hmeas : ∀ p ∈ P.parts, MeasurableSet (p : Set X) := fun p _ => p.2
  have hunion : (⋃ p ∈ P.parts, (p : Set X)) = s := by
    have hsup := congrArg Subtype.val P.sup_parts
    rw [preVariation.Finset.sup_measurableSetSubtype_eq_biUnion id P.parts] at hsup
    exact hsup
  calc ∑ p ∈ P.parts, ‖T p‖ₑ
      ≤ ∑ p ∈ P.parts, m p := Finset.sum_le_sum fun p hp => h p p.2
    _ = m (⋃ p ∈ P.parts, (p : Set X)) := (measure_biUnion_finset hdisj hmeas).symm
    _ = m s := by rw [hunion]

/-- The variation of a density vector measure is dominated by the norm-density
measure. -/
theorem withDensity_vectorMeasure_variation_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : MeasureTheory.Measure X} {v : X → E} (hv : MeasureTheory.Integrable v μ) :
    (μ.withDensityᵥ v).variation ≤ μ.withDensity (fun x => ‖v x‖ₑ) := by
  refine vectorMeasure_variation_le_of_bound _ _ fun s hs => ?_
  rw [withDensityᵥ_apply hv hs]
  calc ‖∫ x in s, v x ∂μ‖ₑ
      ≤ ∫⁻ x in s, ‖v x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm (μ := μ.restrict s) v
    _ = μ.withDensity (fun x => ‖v x‖ₑ) s := (withDensity_apply _ hs).symm

end CZExposure
