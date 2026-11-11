module
public import RequestProject.AppendixE.CompactQuantization

/-! Realize finite vector coefficients as short oriented segment currents.
Weak action approximation alone does not control boundary total variation. -/
@[expose] public section
noncomputable section
namespace CZExposure.ShortSegmentApproximation
open MeasureTheory Set AtomicBoundaryCorrection
open scoped BigOperators NNReal ENNReal
local infixr:25 " →ₛ " => SimpleFunc

private theorem integrable_arc_action (γ : EuclideanArc)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)} (hω : Continuous ω) :
    Integrable (fun t => ω (γ.path t) (deriv γ.path t)) γ.parameterMeasure := by
  letI : IsFiniteMeasure γ.parameterMeasure := by
    dsimp [EuclideanArc.parameterMeasure]
    infer_instance
  obtain ⟨C, hC⟩ := (isCompact_Icc.image γ.lipschitz.continuous).exists_bound_of_continuousOn
    hω.continuousOn
  have hm : Measurable (fun t => ω (γ.path t) (deriv γ.path t)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hω.comp γ.lipschitz.continuous).measurable.prodMk (measurable_deriv γ.path))
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards [γ.unit_speed, ae_restrict_mem measurableSet_Icc] with t ht hmem
  obtain ⟨v, hv, hn⟩ := ht
  calc ‖ω (γ.path t) (deriv γ.path t)‖ ≤ ‖ω (γ.path t)‖ * ‖deriv γ.path t‖ :=
      (ω (γ.path t)).le_opNorm _
    _ = ‖ω (γ.path t)‖ := by rw [hv.deriv, hn, mul_one]
    _ ≤ C := hC _ ⟨t, hmem, rfl⟩

private theorem arc_action_eq (γ : EuclideanArc)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)} (hω : Continuous ω) :
    γ.toNormalCurrentData.action ω =
      ∫ t, ω (γ.path t) (deriv γ.path t) ∂γ.parameterMeasure := by
  apply γ.action_eq
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp
    (hω.measurable.prodMk γ.measurable_tangentField)

/-- A first-order quadrature estimate for an actual segment current. -/
theorem segment_action_error (x y : ExposureEuclidean)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)}
    {C : ℝ≥0} (hω : LipschitzWith C ω) :
    ‖segmentAction x y ω - ω x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hconst : segmentAction x y (fun _ => ω x) = ω x (y - x) := by
    simpa [segment_univ] using segmentAction_indicator x y (ω x) MeasurableSet.univ
  rw [← hconst]
  by_cases hxy : x = y
  · subst y
    simp [segmentAction]
  let γ := arc x y hxy
  letI : IsFiniteMeasure γ.parameterMeasure := by
    dsimp [EuclideanArc.parameterMeasure]
    infer_instance
  have h0 : γ.path 0 = x := PolygonalPath.segment_initial x y
  have hlen : γ.length = ‖y - x‖ := rfl
  simp only [segmentAction, dif_neg hxy]
  change ‖γ.toNormalCurrentData.action ω - γ.toNormalCurrentData.action (fun _ => ω x)‖ ≤ _
  rw [arc_action_eq γ hω.continuous, arc_action_eq γ continuous_const,
    ← integral_sub (integrable_arc_action γ hω.continuous)
      (integrable_arc_action γ continuous_const)]
  have hb : ∀ᵐ t ∂γ.parameterMeasure,
      ‖ω (γ.path t) (deriv γ.path t) - ω x (deriv γ.path t)‖ ≤ (C : ℝ) * γ.length := by
    filter_upwards [γ.unit_speed, ae_restrict_mem measurableSet_Icc] with t ht hm
    obtain ⟨v, hv, hn⟩ := ht
    have hd : dist (γ.path t) x ≤ γ.length := by
      rw [← h0]
      calc dist (γ.path t) (γ.path 0) ≤ dist t 0 := by simpa using γ.lipschitz.dist_le_mul t 0
        _ = t := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hm.1]
        _ ≤ γ.length := hm.2
    calc ‖ω (γ.path t) (deriv γ.path t) - ω x (deriv γ.path t)‖
        = ‖(ω (γ.path t) - ω x) (deriv γ.path t)‖ := rfl
      _ ≤ ‖ω (γ.path t) - ω x‖ * ‖deriv γ.path t‖ :=
        (ω (γ.path t) - ω x).le_opNorm _
      _ = dist (ω (γ.path t)) (ω x) := by rw [hv.deriv, hn, mul_one, dist_eq_norm]
      _ ≤ C * dist (γ.path t) x := hω.dist_le_mul _ _
      _ ≤ C * γ.length := mul_le_mul_of_nonneg_left hd C.coe_nonneg
  have he := norm_integral_le_of_norm_le_const hb
  have hm : γ.parameterMeasure.real univ = γ.length := by
    simp [EuclideanArc.parameterMeasure, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal γ.length_pos.le]
  rw [hm, hlen] at he
  nlinarith

variable {ι : Type*} [Fintype ι]

/-- Finite geometric realization; its boundary is not asserted to have bounded mass. -/
def realization (h : ℝ) (x v : ι → ExposureEuclidean) :=
  correction (fun _ => h⁻¹) x (fun i => x i + h • v i)

theorem realization_mass_le {h : ℝ} (hh : 0 < h) (x v : ι → ExposureEuclidean) :
    (realization h x v).variation univ ≤ ENNReal.ofReal (∑ i, ‖v i‖) := by
  apply (correction_mass_le (fun _ => h⁻¹) x (fun i => x i + h • v i)).trans
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg (v i))]
  apply Finset.sum_le_sum
  intro i _
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
    Real.enorm_eq_ofReal (inv_nonneg.mpr hh.le),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le), inv_mul_cancel_left₀ hh.ne']
  exact le_rfl

theorem realization_action_error {h : ℝ} (hh : 0 < h)
    (x v : ι → ExposureEuclidean)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)}
    {C : ℝ≥0} (hω : LipschitzWith C ω) :
    ‖correctionAction (fun _ => h⁻¹) x (fun i => x i + h • v i) ω -
      ∑ i, ω (x i) (v i)‖ ≤ (C : ℝ) * h * ∑ i, ‖v i‖ ^ 2 := by
  rw [correctionAction, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have he := segment_action_error (x i) (x i + h • v i) hω
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hh] at he
  have hid : h⁻¹ * segmentAction (x i) (x i + h • v i) ω - ω (x i) (v i) =
      h⁻¹ * (segmentAction (x i) (x i + h • v i) ω - h * ω (x i) (v i)) := by
    field_simp
  rw [hid, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  calc h⁻¹ * ‖segmentAction (x i) (x i + h • v i) ω - h * ω (x i) (v i)‖
      ≤ h⁻¹ * ((C : ℝ) * (h * ‖v i‖) ^ 2) :=
        mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hh.le)
    _ = (C : ℝ) * h * ‖v i‖ ^ 2 := by field_simp

/-- The estimate is uniform in the number of sampled cells. -/
theorem realization_action_error_of_mass {h M : ℝ} (hh : 0 < h)
    (x v : ι → ExposureEuclidean) (hM : ∑ i, ‖v i‖ ≤ M)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)}
    {C : ℝ≥0} (hω : LipschitzWith C ω) :
    ‖correctionAction (fun _ => h⁻¹) x (fun i => x i + h • v i) ω -
      ∑ i, ω (x i) (v i)‖ ≤ (C : ℝ) * h * M ^ 2 := by
  apply (realization_action_error hh x v hω).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg C.coe_nonneg hh.le)
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (v i))).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg (v i)) hM 2)

/-- Exact boundary of the realization, not a boundary-mass convergence claim. -/
theorem realization_boundary (h : ℝ) (x v : ι → ExposureEuclidean)
    (ψ : ExposureEuclidean → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    correctionAction (fun _ => h⁻¹) x (fun i => x i + h • v i) (fderiv ℝ ψ) =
      ∑ i, h⁻¹ * (ψ (x i + h • v i) - ψ (x i)) := by
  rw [correction_boundary _ _ _ ψ hψ hs]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- Actual finite segments approximate every Lipschitz one-form, with uniformly
bounded mass. No assertion about flat or boundary-mass convergence is made. -/
theorem exists_segment_sampling (T : EuclideanNormalCurrentData)
    {K : Set ExposureEuclidean} (hK : IsCompact K)
    (hs : T.vectorMeasure.variation Kᶜ = 0) :
    ∃ q : ℕ → (ExposureEuclidean →ₛ ExposureEuclidean),
      let x := fun n (z : (q n).range) => (z : ExposureEuclidean)
      let v := fun n (z : (q n).range) => T.vectorMeasure (q n ⁻¹' {z.val})
      (∀ n : ℕ, (realization (1 / ((n : ℝ) + 1)) (x n) (v n)).variation univ ≤
        T.vectorMeasure.variation univ) ∧
      ∀ (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) (C : ℝ≥0),
        LipschitzWith C ω → Filter.Tendsto
          (fun n : ℕ => correctionAction (fun _ => (1 / ((n : ℝ) + 1))⁻¹)
            (x n) (fun z => x n z + (1 / ((n : ℝ) + 1)) • v n z) ω)
          Filter.atTop (nhds (T.action ω)) := by
  classical
  letI := T.finite_variation
  obtain ⟨q, _, hmass, hconv⟩ := CompactQuantization.exists_current_sampling T hK hs
  refine ⟨q, ?_⟩
  dsimp only
  have hm (n : ℕ) :
      ∑ z : (q n).range, ‖T.vectorMeasure (q n ⁻¹' {z.val})‖ ≤
        (T.vectorMeasure.variation univ).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simp only [ofReal_norm_eq_enorm]
    rw [Finset.sum_coe_sort (q n).range (fun z => ‖T.vectorMeasure (q n ⁻¹' {z})‖ₑ)]
    exact hmass n
  constructor
  · intro n
    apply (realization_mass_le (by positivity) _ _).trans
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hm n)
  · intro ω C hω
    let a := fun n : ℕ => correctionAction (fun _ => (1 / ((n : ℝ) + 1))⁻¹)
      (fun z : (q n).range => z.val)
      (fun z : (q n).range => z.val + (1 / ((n : ℝ) + 1)) •
        T.vectorMeasure (q n ⁻¹' {z.val})) ω
    let b := fun n => ∑ z : (q n).range, ω z.val (T.vectorMeasure (q n ⁻¹' {z.val}))
    have hb : Filter.Tendsto b Filter.atTop (nhds (T.action ω)) := by
      have he (n : ℕ) : b n = ∑ z ∈ (q n).range,
          ω z (T.vectorMeasure (q n ⁻¹' {z})) :=
        Finset.sum_coe_sort (q n).range (fun z => ω z (T.vectorMeasure (q n ⁻¹' {z})))
      simp_rw [show b = _ from funext he]
      exact hconv ω hω.continuous
    have herr : Filter.Tendsto (fun n => ‖a n - b n‖) Filter.atTop (nhds 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
        realization_action_error_of_mass (by positivity) _ _ (hm n) hω)
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (C : ℝ)).mul_const
        ((T.vectorMeasure.variation univ).toReal ^ 2)
    have hz : Filter.Tendsto (fun n => a n - b n) Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr herr
    simpa only [sub_add_cancel, zero_add] using hz.add hb

end CZExposure.ShortSegmentApproximation
