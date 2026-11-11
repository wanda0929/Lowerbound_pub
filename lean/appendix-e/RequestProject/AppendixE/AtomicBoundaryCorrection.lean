module
public import RequestProject.AppendixE.PolygonalRealization

/-! Explicit correction of paired finite atomic boundary errors by segments.
The mass estimate is a transport-cost bound, not an existence theorem for
small-cost pairings from weak convergence or flat-norm convergence. -/
@[expose] public section
noncomputable section
namespace CZExposure.AtomicBoundaryCorrection
open MeasureTheory Set
open scoped BigOperators

def arc (x y : ExposureEuclidean) (h : x ≠ y) : EuclideanArc :=
  (PolygonalPath.segment x y).toArc
    (norm_pos_iff.mpr (sub_ne_zero.mpr h.symm))
    (PolygonalPath.segment_injOn x y)

def segment (x y : ExposureEuclidean) :
    VectorMeasure ExposureEuclidean ExposureEuclidean :=
  if h : x = y then 0 else (arc x y h).vectorCurrent

def segmentAction (x y : ExposureEuclidean)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) : ℝ :=
  if h : x = y then 0 else (arc x y h).toNormalCurrentData.action ω

private theorem arc_univ (γ : EuclideanArc) :
    γ.vectorCurrent univ = γ.path γ.length - γ.path 0 := by
  apply (NormedSpace.eq_iff_forall_dual_eq ℝ).mpr
  intro L
  rw [γ.vectorCurrent_apply MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_univ, map_sub]
  rw [← L.integral_comp_comm γ.integrable_deriv]
  have hAC : AbsolutelyContinuousOnInterval (fun t => L (γ.path t)) 0 γ.length :=
    (L.lipschitz.comp γ.lipschitz).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : (fun t => deriv (fun s => L (γ.path s)) t) =ᵐ[γ.parameterMeasure]
      (fun t => L (deriv γ.path t)) := by
    filter_upwards [γ.unit_speed] with t ht
    obtain ⟨v, hv, _⟩ := ht
    rw [hv.deriv]
    exact (L.hasFDerivAt.comp_hasDerivAt t hv).deriv
  rw [← integral_congr_ae hd]
  have he := hAC.integral_deriv_eq_sub
  rw [intervalIntegral.integral_of_le γ.length_pos.le,
    ← integral_Icc_eq_integral_Ioc] at he
  exact he

/-- The orientation is from x to y, including the zero-length case. -/
theorem segment_univ (x y : ExposureEuclidean) : segment x y univ = y - x := by
  by_cases h : x = y
  · subst y
    simp [segment]
  · rw [segment, dif_neg h, arc_univ]
    change (PolygonalPath.segment x y).path (PolygonalPath.segment x y).duration -
      (PolygonalPath.segment x y).path 0 = y - x
    rw [PolygonalPath.segment_terminal, PolygonalPath.segment_initial]

theorem segment_mass (x y : ExposureEuclidean) :
    (segment x y).variation univ = ENNReal.ofReal ‖y - x‖ := by
  by_cases h : x = y
  · subst y
    simp [segment, vectorMeasure_variation_zero]
  · simp only [segment, dif_neg h, EuclideanArc.vectorCurrent_mass]
    rfl

theorem segment_compact_support (x y : ExposureEuclidean) :
    ∃ K : Set ExposureEuclidean, IsCompact K ∧ (segment x y).variation Kᶜ = 0 := by
  by_cases h : x = y
  · exact ⟨∅, isCompact_empty, by simp [segment, h, vectorMeasure_variation_zero]⟩
  · simpa only [segment, dif_neg h] using (arc x y h).vectorCurrent_compact_support

/-- The action and vector measure are compatible on every localized constant
one-form; the action is not an unrelated boundary functional. -/
theorem segmentAction_indicator (x y : ExposureEuclidean)
    (L : ExposureEuclidean →L[ℝ] ℝ) {s : Set ExposureEuclidean}
    (hs : MeasurableSet s) :
    segmentAction x y (s.indicator (fun _ => L)) = L (segment x y s) := by
  classical
  by_cases h : x = y
  · simp [segmentAction, segment, h]
  · simp only [segmentAction, segment, dif_neg h]
    change (∫ z, (s.indicator (fun _ => L)) z ((arc x y h).tangentField z)
      ∂(arc x y h).vectorCurrent.variation) = L ((arc x y h).vectorCurrent s)
    rw [EuclideanArc.vectorCurrent_variation]
    have he : (fun z => (s.indicator (fun _ => L)) z ((arc x y h).tangentField z)) =
        s.indicator (fun z => L ((arc x y h).tangentField z)) := by
      funext z
      by_cases hz : z ∈ s <;> simp [hz]
    rw [he, integral_indicator hs, EuclideanArc.vectorCurrent,
      withDensityᵥ_apply (arc x y h).integrable_tangentField hs]
    exact L.integral_comp_comm (arc x y h).integrable_tangentField.integrableOn

theorem segment_boundary (x y : ExposureEuclidean)
    (ψ : ExposureEuclidean → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    segmentAction x y (fderiv ℝ ψ) = ψ y - ψ x := by
  by_cases h : x = y
  · subst y
    simp [segmentAction]
  · rw [segmentAction, dif_neg h]
    change (∫ z, fderiv ℝ ψ z ((arc x y h).tangentField z)
      ∂(arc x y h).vectorCurrent.variation) = _
    rw [EuclideanArc.vectorCurrent_variation, ((arc x y h).boundary ψ hψ hs).2]
    change ψ ((PolygonalPath.segment x y).path (PolygonalPath.segment x y).duration) -
      ψ ((PolygonalPath.segment x y).path 0) = _
    rw [PolygonalPath.segment_terminal, PolygonalPath.segment_initial]

theorem variation_smul_le (a : ℝ)
    (T : VectorMeasure ExposureEuclidean ExposureEuclidean) :
    (a • T).variation ≤ ‖a‖ₑ • T.variation := by
  apply vectorMeasure_variation_le_of_bound
  intro s hs
  rw [VectorMeasure.smul_apply, enorm_smul, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (vectorMeasure_enorm_le_variation T hs) _

theorem variation_sum_le {ι : Type*} (s : Finset ι)
    (T : ι → VectorMeasure ExposureEuclidean ExposureEuclidean) :
    (∑ i ∈ s, T i).variation ≤ ∑ i ∈ s, (T i).variation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vectorMeasure_variation_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply (vectorMeasure_variation_add_le (T i) (∑ j ∈ s, T j)).trans
    exact add_le_add (le_refl (T i).variation) ih

variable {ι : Type*} [Fintype ι]

def correction (w : ι → ℝ) (x y : ι → ExposureEuclidean) :
    VectorMeasure ExposureEuclidean ExposureEuclidean :=
  ∑ i, w i • segment (x i) (y i)

def correctionAction (w : ι → ℝ) (x y : ι → ExposureEuclidean)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) : ℝ :=
  ∑ i, w i * segmentAction (x i) (y i) ω

theorem correction_apply (w : ι → ℝ) (x y : ι → ExposureEuclidean)
    (s : Set ExposureEuclidean) :
    correction w x y s = ∑ i, w i • segment (x i) (y i) s := by
  let ev : VectorMeasure ExposureEuclidean ExposureEuclidean →+ ExposureEuclidean :=
    { toFun := fun T => T s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev _ _

theorem correctionAction_indicator (w : ι → ℝ) (x y : ι → ExposureEuclidean)
    (L : ExposureEuclidean →L[ℝ] ℝ) {s : Set ExposureEuclidean}
    (hs : MeasurableSet s) :
    correctionAction w x y (s.indicator (fun _ => L)) = L (correction w x y s) := by
  simp only [correctionAction, segmentAction_indicator _ _ _ hs,
    correction_apply, map_sum, map_smul, smul_eq_mul]

theorem correction_boundary (w : ι → ℝ) (x y : ι → ExposureEuclidean)
    (ψ : ExposureEuclidean → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    correctionAction w x y (fderiv ℝ ψ) =
      (∑ i, w i * ψ (y i)) - ∑ i, w i * ψ (x i) := by
  simp only [correctionAction, segment_boundary _ _ _ hψ hs, mul_sub, Finset.sum_sub_distrib]

theorem correction_variation_le (w : ι → ℝ) (x y : ι → ExposureEuclidean) :
    (correction w x y).variation ≤ ∑ i, ‖w i‖ₑ • (segment (x i) (y i)).variation :=
  (variation_sum_le Finset.univ (fun i => w i • segment (x i) (y i))).trans
    (Finset.sum_le_sum fun i _ => variation_smul_le (w i) (segment (x i) (y i)))

theorem correction_mass_le (w : ι → ℝ) (x y : ι → ExposureEuclidean) :
    (correction w x y).variation univ ≤
      ∑ i, ‖w i‖ₑ * ENNReal.ofReal ‖y i - x i‖ := by
  have hu := Measure.le_iff.mp (correction_variation_le w x y) univ MeasurableSet.univ
  simpa only [correction, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    segment_mass] using hu

theorem correction_compact_support (w : ι → ℝ) (x y : ι → ExposureEuclidean) :
    ∃ K : Set ExposureEuclidean, IsCompact K ∧ (correction w x y).variation Kᶜ = 0 := by
  choose K hK hz using (fun i => segment_compact_support (x i) (y i))
  have hc : IsCompact (⋃ i, K i) := isCompact_iUnion hK
  refine ⟨⋃ i, K i, hc, le_antisymm ?_ (zero_le _)⟩
  have hz' (i : ι) : (segment (x i) (y i)).variation (⋃ j, K j)ᶜ = 0 := by
    apply le_antisymm _ (zero_le _)
    calc
      (segment (x i) (y i)).variation (⋃ j, K j)ᶜ
          ≤ (segment (x i) (y i)).variation (K i)ᶜ :=
        measure_mono (compl_subset_compl.mpr (subset_iUnion K i))
      _ = 0 := hz i
  have hu := Measure.le_iff.mp (correction_variation_le w x y) _ hc.isClosed.measurableSet.compl
  simpa only [Measure.finset_sum_apply, Measure.smul_apply, hz', smul_zero,
    Finset.sum_const_zero] using hu

instance correction_finite (w : ι → ℝ) (x y : ι → ExposureEuclidean) :
    IsFiniteMeasure (correction w x y).variation := by
  constructor
  apply lt_of_le_of_lt (correction_mass_le w x y)
  exact ENNReal.sum_lt_top.mpr fun i _ =>
    (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top).lt_top

/-- Moving finitely many weighted atoms by at most ε costs at most ε times
their total absolute weight. Signed weights and coincident endpoints are allowed. -/
theorem correction_mass_le_of_displacement (w : ι → ℝ)
    (x y : ι → ExposureEuclidean) (ε : ℝ) (M : ENNReal)
    (hmove : ∀ i, ‖y i - x i‖ ≤ ε) (hweight : ∑ i, ‖w i‖ₑ ≤ M) :
    (correction w x y).variation univ ≤ M * ENNReal.ofReal ε := by
  calc
    (correction w x y).variation univ
        ≤ ∑ i, ‖w i‖ₑ * ENNReal.ofReal ‖y i - x i‖ := correction_mass_le w x y
    _ ≤ ∑ i, ‖w i‖ₑ * ENNReal.ofReal ε := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_right (ENNReal.ofReal_le_ofReal (hmove i)) _
    _ = (∑ i, ‖w i‖ₑ) * ENNReal.ofReal ε := (Finset.sum_mul _ _ _).symm
    _ ≤ M * ENNReal.ofReal ε := mul_le_mul_left hweight _

/-- Small transport cost gives a small correction on every measurable region,
not just a scalar bound on its total mass. -/
theorem correction_apply_le (w : ι → ℝ) (x y : ι → ExposureEuclidean)
    {s : Set ExposureEuclidean} (hs : MeasurableSet s) :
    ‖correction w x y s‖ₑ ≤ ∑ i, ‖w i‖ₑ * ENNReal.ofReal ‖y i - x i‖ :=
  (vectorMeasure_enorm_le_variation _ hs).trans
    ((measure_mono (subset_univ s)).trans (correction_mass_le w x y))

/-- The number of atoms may grow with n. This requires a proved small-cost
pairing; it does not infer such a pairing from weak convergence. -/
theorem correction_mass_tendsto_zero {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (w : ∀ n, κ n → ℝ) (x y : ∀ n, κ n → ExposureEuclidean)
    (hcost : Filter.Tendsto
      (fun n => ∑ i, ‖w n i‖ₑ * ENNReal.ofReal ‖y n i - x n i‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (correction (w n) (x n) (y n)).variation univ)
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcost
    (fun _ => zero_le _) (fun n => correction_mass_le (w n) (x n) (y n))

end CZExposure.AtomicBoundaryCorrection
