module
public import RequestProject.AppendixE.BFieldRegularity
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compactness of feasible exposure records (Appendix E)

The set of exposure records with a prescribed nonnegative mass budget is compact in the
weak topology. Working on the compact subtype `ExposurePoint` of `Y × U` lets us use the
joint continuity of `B` proved in `BFieldRegularity` without asserting ambient
continuity. The bridge between the ambient feasible set `IsExposureRecord` and the
domain feasible set is the subtype pushforward/pullback equivalence.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set Topology Filter
open scoped ENNReal NNReal

/-- The ambient space `ℝ¹¹ × ℂ` of relaxed records. -/
abbrev ExposureAmbient := (Fin 11 → ℝ) × ℂ

/-- The compact state-control domain `Y × U`. -/
def exposureDomain : Set ExposureAmbient :=
  Yset ×ˢ Metric.closedBall (0 : ℂ) 1

/-- The domain viewed as a subtype, carrying the finite records in the budget. -/
abbrev ExposurePoint := ↥exposureDomain

/-- The domain is compact: it is the product of the compact `Y` and the closed unit disk. -/
theorem isCompact_exposureDomain : IsCompact exposureDomain :=
  isCompact_Yset.prod (isCompact_closedBall (0 : ℂ) 1)

instance instCompactSpaceExposurePoint : CompactSpace ExposurePoint :=
  isCompact_iff_compactSpace.mp isCompact_exposureDomain

/-- The scalar balance `p ↦ Dψ(p.1.1)(B(p.1.1,p.1.2))` is continuous on the domain, by
restricting `continuousOn_Bfield` to the subtype and composing with `fderiv ℝ ψ`. -/
def exposureBalance (ψ : (Fin 11 → ℝ) → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    C(ExposurePoint, ℝ) where
  toFun p := fderiv ℝ ψ p.1.1 (Bfield p.1.1 p.1.2)
  continuous_toFun := by
    have hB : Continuous fun p : ExposurePoint => Bfield p.1.1 p.1.2 := by
      refine continuous_iff_continuousAt.mpr fun p => ?_
      have hw := continuousOn_Bfield p.1 p.2
      have hc := hw.comp (continuous_subtype_val.continuousWithinAt (s := univ))
        (fun x _ => x.2)
      rwa [continuousWithinAt_univ] at hc
    have hfd : Continuous fun p : ExposurePoint => fderiv ℝ ψ p.1.1 :=
      (hψ.continuous_fderiv one_ne_zero).comp
        (continuous_fst.comp continuous_subtype_val)
    exact Continuous.clm_apply hfd hB

/-- The feasible records on the domain: the balance identity for all compactly
supported smooth test functions. -/
def IsDomainExposureRecord (μ : FiniteMeasure ExposurePoint) : Prop :=
  ∀ ψ : (Fin 11 → ℝ) → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ p : ExposurePoint, fderiv ℝ ψ p.1.1 (Bfield p.1.1 p.1.2)
        ∂μ.toMeasure = ψ yPi - ψ y0

/-- Feasible domain records with a prescribed mass budget. -/
def domainExposureRecordBudget (M : ℝ≥0) : Set (FiniteMeasure ExposurePoint) :=
  {μ | μ.mass ≤ M ∧ IsDomainExposureRecord μ}

/-- The subtype pushforward of a domain record to the ambient space. -/
def pushExposureMeasure (μ : FiniteMeasure ExposurePoint) : FiniteMeasure ExposureAmbient :=
  μ.map (Subtype.val : ExposurePoint → ExposureAmbient)

/-- Feasible ambient records with a prescribed mass budget. -/
def exposureRecordBudget (M : ℝ≥0) : Set (FiniteMeasure ExposureAmbient) :=
  {ν | ν.mass ≤ M ∧ IsExposureRecord ν.toMeasure}

private theorem contDiff_one_of_smooth {ψ : (Fin 11 → ℝ) → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) ψ) : ContDiff ℝ 1 ψ :=
  h.of_le (by norm_cast)

/-- The balance functional `μ ↦ ∫ B·∇ψ dμ` is continuous in the weak topology. -/
theorem continuous_balanceIntegral (ψ : (Fin 11 → ℝ) → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    Continuous (fun μ : FiniteMeasure ExposurePoint =>
      ∫ p : ExposurePoint, fderiv ℝ ψ p.1.1 (Bfield p.1.1 p.1.2)
        ∂μ.toMeasure) :=
  FiniteMeasure.continuous_integral_continuousMap (exposureBalance ψ hψ)

/-- The domain records form a closed set: each balance equality is closed. -/
theorem isClosed_domainExposureRecords :
    IsClosed {μ : FiniteMeasure ExposurePoint | IsDomainExposureRecord μ} := by
  simp only [IsDomainExposureRecord]
  rw [setOf_forall]
  apply isClosed_iInter
  intro ψ
  rw [setOf_forall]
  apply isClosed_iInter
  intro h1
  rw [setOf_forall]
  apply isClosed_iInter
  intro h2
  exact isClosed_eq (continuous_balanceIntegral ψ (contDiff_one_of_smooth h1))
    continuous_const

/-- The domain record budget is compact as the intersection of a compact mass ball
with a closed constraint set. -/
theorem isCompact_domainExposureRecordBudget (M : ℝ≥0) :
    IsCompact (domainExposureRecordBudget M) := by
  rw [domainExposureRecordBudget, setOf_and]
  exact (isCompact_setOf_finiteMeasure_le_of_compactSpace _ M).inter_right
    isClosed_domainExposureRecords

private theorem isClosedEmbedding_val :
    IsClosedEmbedding (Subtype.val : ExposurePoint → ExposureAmbient) :=
  IsClosedEmbedding.subtypeVal isCompact_exposureDomain.isClosed

/-- The subtype pushforward is supported inside `exposureDomain`. -/
theorem pushExposureMeasure_support (μ : FiniteMeasure ExposurePoint) :
    (pushExposureMeasure μ : Measure ExposureAmbient) exposureDomainᶜ = 0 := by
  have hempty : (Subtype.val : ExposurePoint → ExposureAmbient) ⁻¹' exposureDomainᶜ = ∅ := by
    ext p
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact not_not.mpr p.property
  rw [pushExposureMeasure]
  show ((μ.map Subtype.val).toMeasure : Measure ExposureAmbient) exposureDomainᶜ = 0
  rw [FiniteMeasure.toMeasure_map, Measure.map_apply measurable_subtype_coe
    isCompact_exposureDomain.isClosed.measurableSet.compl, hempty, measure_empty]

/-- Balance integrals transport through the subtype pushforward. -/
theorem pushExposureMeasure_record_iff (μ : FiniteMeasure ExposurePoint) :
    IsExposureRecord (pushExposureMeasure μ : Measure ExposureAmbient) ↔
      IsDomainExposureRecord μ := by
  have he : (μ.map (Subtype.val : ExposurePoint → ExposureAmbient)).toMeasure =
      Measure.map (Subtype.val : ExposurePoint → ExposureAmbient) μ.toMeasure := rfl
  constructor
  · rintro ⟨_, _, hbalance⟩ ψ h1 h2
    have key := hbalance ψ h1 h2
    rw [pushExposureMeasure, he] at key
    rw [isClosedEmbedding_val.measurableEmbedding.integral_map] at key
    exact key
  · intro hbalance
    refine ⟨inferInstance, pushExposureMeasure_support μ, fun ψ h1 h2 => ?_⟩
    rw [pushExposureMeasure, he]
    rw [isClosedEmbedding_val.measurableEmbedding.integral_map]
    exact hbalance ψ h1 h2

/-- An ambient record recovers as the pushforward of its domain pullback. -/
private theorem map_comap_val_eq {ν : FiniteMeasure ExposureAmbient}
    (hsupp : (ν : Measure ExposureAmbient) exposureDomainᶜ = 0) :
    pushExposureMeasure (ν.comap Subtype.val) = ν := by
  have hf := isClosedEmbedding_val
  rw [pushExposureMeasure]
  ext s hs
  rw [FiniteMeasure.toMeasure_map, Measure.map_apply measurable_subtype_coe hs,
    FiniteMeasure.toMeasure_comap,
    Measure.comap_apply _ Subtype.val_injective
      (fun t ht => hf.measurableEmbedding.measurableSet_image' ht) _
      (hf.continuous.measurable hs),
    image_preimage_eq_inter_range, Subtype.range_val]
  rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
  exact mem_ae_iff.mpr hsupp

/-- The ambient record budget is exactly the pushforward image of the domain budget. -/
theorem exposureRecordBudget_eq_image (M : ℝ≥0) :
    exposureRecordBudget M = pushExposureMeasure '' domainExposureRecordBudget M := by
  ext ν
  constructor
  · rintro ⟨hM, hν⟩
    have hpush := map_comap_val_eq hν.2.1
    refine ⟨ν.comap (Subtype.val : ExposurePoint → ExposureAmbient), ?_, hpush⟩
    refine ⟨(FiniteMeasure.mass_comap_le _ _).trans hM, ?_⟩
    apply (pushExposureMeasure_record_iff _).mp
    simpa only [hpush] using hν
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨hM, hrec⟩ := hμ
    refine ⟨?_, (pushExposureMeasure_record_iff μ).mpr hrec⟩
    exact (FiniteMeasure.mass_map_le _ _).trans hM

/-- The ambient record budget is compact: it is a continuous image of a compact set. -/
theorem isCompact_exposureRecordBudget (M : ℝ≥0) :
    IsCompact (exposureRecordBudget M) := by
  rw [exposureRecordBudget_eq_image]
  exact (isCompact_domainExposureRecordBudget M).image
    (FiniteMeasure.continuous_map continuous_subtype_val)

end CZExposure
