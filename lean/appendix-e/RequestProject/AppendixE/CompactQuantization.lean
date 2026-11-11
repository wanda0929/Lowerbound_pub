module
public import RequestProject.AppendixE.AtomicBoundaryCorrection
public import Mathlib.MeasureTheory.Function.SimpleFunc

/-! Finite measurable spatial quantization on compact sets. This constructs
the quantizer, rather than assuming a finite pairing with small displacement.
It is a discretization tool, not a polyhedral approximation theorem for currents. -/
@[expose] public section
noncomputable section
namespace CZExposure.CompactQuantization
open MeasureTheory Set Metric
open scoped BigOperators NNReal
local infixr:25 " →ₛ " => SimpleFunc

private theorem finite_cover_quantizer (s : Finset ExposureEuclidean) (ε : ℝ) :
    ∃ q : ExposureEuclidean →ₛ ExposureEuclidean,
      ∀ x, (∃ y ∈ s, dist x y < ε) → q x ∈ s ∧ dist x (q x) < ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨SimpleFunc.const _ 0, by simp⟩
  | @insert y s hy ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨SimpleFunc.piecewise (ball y ε) isOpen_ball.measurableSet
      (SimpleFunc.const _ y) q, ?_⟩
    intro x hx
    by_cases hxy : x ∈ ball y ε
    · simp [SimpleFunc.piecewise_apply, hxy, Metric.mem_ball.mp hxy]
    · obtain ⟨z, hz, hxz⟩ := hx
      have hzs : z ∈ s := by
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact False.elim (hxy hxz)
        · exact hz
      obtain ⟨hm, hd⟩ := hq x ⟨z, hzs, hxz⟩
      simpa [SimpleFunc.piecewise_apply, hxy] using
        And.intro (Finset.mem_insert_of_mem hm) hd

/-- Every compact carrier admits a Borel finite-range quantizer with arbitrarily
small displacement and with centers in the carrier. Empty carriers are allowed. -/
theorem exists_quantizer {K : Set ExposureEuclidean} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ExposureEuclidean →ₛ ExposureEuclidean,
      ∀ x ∈ K, q x ∈ K ∧ dist x (q x) < ε := by
  classical
  obtain ⟨s, hsK, hs, hcover⟩ := hK.finite_cover_balls hε
  obtain ⟨q, hq⟩ := finite_cover_quantizer hs.toFinset ε
  refine ⟨q, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨hm, hd⟩ := hq x ⟨y, hs.mem_toFinset.mpr hy, hxy⟩
  exact ⟨hsK (hs.mem_toFinset.mp hm), hd⟩

/-- The graph transport of a quantizer has a uniform, proved cost bound. -/
theorem transport_cost_le (μ : Measure ExposureEuclidean)
    {K : Set ExposureEuclidean} (hs : μ Kᶜ = 0)
    (q : ExposureEuclidean →ₛ ExposureEuclidean) {ε : ℝ}
    (hq : ∀ x ∈ K, dist x (q x) ≤ ε) :
    (∫⁻ x, ENNReal.ofReal (dist x (q x)) ∂μ) ≤
      ENNReal.ofReal ε * μ univ := by
  calc
    (∫⁻ x, ENNReal.ofReal (dist x (q x)) ∂μ)
        ≤ ∫⁻ _, ENNReal.ofReal ε ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [show ∀ᵐ x ∂μ, x ∈ K from ae_iff.mpr hs] with x hx
      exact ENNReal.ofReal_le_ofReal (hq x hx)
    _ = _ := by simp

/-- The pushed measure is literally a finite sum of Dirac masses. -/
theorem map_eq_atoms (μ : Measure ExposureEuclidean)
    (q : ExposureEuclidean →ₛ ExposureEuclidean) :
    μ.map q = ∑ z ∈ q.range, μ (q ⁻¹' {z}) • Measure.dirac z := by
  apply (Measure.ae_mem_finset_iff_map_eq_sum_dirac q.aemeasurable).mp
  exact Filter.Eventually.of_forall fun x => q.mem_range_self x

theorem map_mass (μ : Measure ExposureEuclidean)
    (q : ExposureEuclidean →ₛ ExposureEuclidean) : (μ.map q) univ = μ univ := by
  rw [Measure.map_apply q.measurable MeasurableSet.univ, preimage_univ]

theorem map_carrier (μ : Measure ExposureEuclidean)
    {K : Set ExposureEuclidean} (hK : MeasurableSet K) (hs : μ Kᶜ = 0)
    (q : ExposureEuclidean →ₛ ExposureEuclidean) (hq : ∀ x ∈ K, q x ∈ K) :
    (μ.map q) Kᶜ = 0 := by
  rw [Measure.map_apply q.measurable hK.compl]
  apply le_antisymm _ (zero_le _)
  calc μ (q ⁻¹' Kᶜ) ≤ μ Kᶜ := measure_mono (by
      intro x hx hxK
      exact hx (hq x hxK))
    _ = 0 := hs

/-- A Lipschitz test has a quantitative error, not just weak convergence.
Its integrability follows from the finite-range approximation and the error
bound, so it is not an additional assumption. -/
theorem integral_error_le (μ : Measure ExposureEuclidean) [IsFiniteMeasure μ]
    {K : Set ExposureEuclidean} (hs : μ Kᶜ = 0)
    (q : ExposureEuclidean →ₛ ExposureEuclidean) {ε : ℝ}
    (hq : ∀ x ∈ K, dist x (q x) ≤ ε)
    {C : ℝ≥0} {f : ExposureEuclidean → ℝ} (hf : LipschitzWith C f) :
    ‖(∫ z, f z ∂μ.map q) - ∫ x, f x ∂μ‖ ≤
      (C : ℝ) * ε * μ.real univ := by
  have hcomp : Integrable (fun x => f (q x)) μ :=
    (q.map f).integrable_of_isFiniteMeasure
  have hb : ∀ᵐ x ∂μ, ‖f (q x) - f x‖ ≤ (C : ℝ) * ε := by
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ K from ae_iff.mpr hs] with x hx
    calc ‖f (q x) - f x‖ = dist (f (q x)) (f x) := (dist_eq_norm _ _).symm
      _ ≤ C * dist (q x) x := hf.dist_le_mul _ _
      _ ≤ C * ε := mul_le_mul_of_nonneg_left
        (by simpa [dist_comm] using hq x hx) C.coe_nonneg
  have hd : Integrable (fun x => f (q x) - f x) μ :=
    (integrable_const ((C : ℝ) * ε)).mono'
      ((hf.continuous.measurable.comp q.measurable).sub
        hf.continuous.measurable).aestronglyMeasurable hb
  have hfi : Integrable f μ := by
    apply (hcomp.sub hd).congr
    filter_upwards [] with x
    exact sub_sub_cancel (f (q x)) (f x)
  rw [integral_map q.aemeasurable hf.continuous.aestronglyMeasurable,
    ← integral_sub hcomp hfi]
  exact norm_integral_le_of_norm_le_const hb

/-- On a common compact carrier, spatial quantization converges against every
continuous real test, not only against Lipschitz tests. -/
theorem integral_tendsto (μ : Measure ExposureEuclidean) [IsFiniteMeasure μ]
    {K : Set ExposureEuclidean} (hK : IsCompact K) (hs : μ Kᶜ = 0)
    (q : ℕ → (ExposureEuclidean →ₛ ExposureEuclidean)) (ε : ℕ → ℝ)
    (hq : ∀ n x, x ∈ K → q n x ∈ K ∧ dist x (q n x) ≤ ε n)
    (hzero : Filter.Tendsto ε Filter.atTop (nhds 0))
    {f : ExposureEuclidean → ℝ} (hf : Continuous f) :
    Filter.Tendsto (fun n => ∫ z, f z ∂μ.map (q n)) Filter.atTop
      (nhds (∫ x, f x ∂μ)) := by
  simp_rw [integral_map (q _).aemeasurable hf.aestronglyMeasurable]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    exact (hf.measurable.comp (q n).measurable).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ K from ae_iff.mpr hs] with x hx
    exact hC (q n x) (hq n x hx).1
  · filter_upwards [show ∀ᵐ x ∂μ, x ∈ K from ae_iff.mpr hs] with x hx
    apply hf.continuousAt.tendsto.comp
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => by simpa [dist_comm] using (hq n x hx).2) hzero

/-- A single sequence of finite quantizers works for every finite measure
on the compact carrier; the graph-transport costs actually tend to zero. -/
theorem exists_quantizer_sequence {K : Set ExposureEuclidean} (hK : IsCompact K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hzero : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    ∃ q : ℕ → (ExposureEuclidean →ₛ ExposureEuclidean),
      (∀ n x, x ∈ K → q n x ∈ K ∧ dist x (q n x) < ε n) ∧
      ∀ (μ : Measure ExposureEuclidean) [IsFiniteMeasure μ], μ Kᶜ = 0 →
        Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (dist x (q n x)) ∂μ)
          Filter.atTop (nhds 0) := by
  choose q hq using fun n => exists_quantizer hK (hε n)
  refine ⟨q, hq, ?_⟩
  intro μ hfin hs
  have ht := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hzero)
    (Or.inr (measure_ne_top μ univ))
  simp only [ENNReal.ofReal_zero, zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) (fun n => transport_cost_le μ hs (q n)
      (fun x hx => (hq n x hx).2.le))

/-- Finite spatial sampling of an actual current is integrable for every
one-form, even if that form is not measurable away from the finite centers. -/
theorem integrable_sampled_action (T : EuclideanNormalCurrentData)
    (q : ExposureEuclidean →ₛ ExposureEuclidean)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) :
    Integrable (fun x => ω (q x) (T.direction x)) T.vectorMeasure.variation := by
  letI := T.finite_variation
  obtain ⟨C, hC⟩ := (q.map ω).finite_range.isCompact.exists_bound_of_continuousOn
    continuous_id.continuousOn
  have hm : Measurable (fun x => ω (q x) (T.direction x)) := by
    have hω := (q.map ω).measurable
    have hσ := T.measurable_direction
    exact (continuous_fst.clm_apply continuous_snd).measurable.comp (hω.prodMk hσ)
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards [T.direction_unit] with x hx
  calc ‖ω (q x) (T.direction x)‖ ≤ ‖ω (q x)‖ * ‖T.direction x‖ :=
      (ω (q x)).le_opNorm _
    _ = ‖ω (q x)‖ := by rw [hx, mul_one]
    _ ≤ C := hC _ ⟨x, rfl⟩

/-- The sampled action is a genuine finite sum with vector coefficients
equal to the original current's values on disjoint measurable cells. -/
theorem sampled_action_eq_sum (T : EuclideanNormalCurrentData)
    (q : ExposureEuclidean →ₛ ExposureEuclidean)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) :
    (∫ x, ω (q x) (T.direction x) ∂T.vectorMeasure.variation) =
      ∑ z ∈ q.range, ω z (T.vectorMeasure (q ⁻¹' {z})) := by
  classical
  have hdis : Set.PairwiseDisjoint (q.range : Set ExposureEuclidean)
      (fun z => q ⁻¹' {z}) := by
    intro z _ y _ hzy
    exact Set.disjoint_left.mpr fun x hx hy => hzy (hx.symm.trans hy)
  have hcover : (⋃ z ∈ q.range, q ⁻¹' {z}) = univ := by
    change (⋃ z ∈ (q.range : Set ExposureEuclidean), q ⁻¹' {z}) = univ
    rw [SimpleFunc.coe_range, Set.biUnion_range_preimage_singleton]
  have he := integral_biUnion_finset q.range
    (fun z _ => q.measurableSet_fiber z) hdis
    (fun _ _ => (integrable_sampled_action T q ω).integrableOn)
  rw [hcover, Measure.restrict_univ] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro z hz
  have hv : T.vectorMeasure (q ⁻¹' {z}) =
      ∫ x in q ⁻¹' {z}, T.direction x ∂T.vectorMeasure.variation := by
    calc T.vectorMeasure (q ⁻¹' {z}) =
        (T.vectorMeasure.variation.withDensityᵥ T.direction) (q ⁻¹' {z}) :=
          congrArg (fun V => V (q ⁻¹' {z})) T.represents
      _ = _ := withDensityᵥ_apply T.direction_integrable (q.measurableSet_fiber z)
  rw [hv, ← (ω z).integral_comp_comm T.direction_integrable.integrableOn]
  exact setIntegral_congr_fun (q.measurableSet_fiber z) fun x hx => by rw [show q x = z from hx]

/-- Discretizing current coefficients cannot increase their total variation. -/
theorem sampled_mass_le (T : EuclideanNormalCurrentData)
    (q : ExposureEuclidean →ₛ ExposureEuclidean) :
    ∑ z ∈ q.range, ‖T.vectorMeasure (q ⁻¹' {z})‖ₑ ≤
      T.vectorMeasure.variation univ := by
  classical
  have hdis : Set.PairwiseDisjoint (q.range : Set ExposureEuclidean)
      (fun z => q ⁻¹' {z}) := by
    intro z _ y _ hzy
    exact Set.disjoint_left.mpr fun x hx hy => hzy (hx.symm.trans hy)
  calc ∑ z ∈ q.range, ‖T.vectorMeasure (q ⁻¹' {z})‖ₑ
      ≤ ∑ z ∈ q.range, T.vectorMeasure.variation (q ⁻¹' {z}) :=
        Finset.sum_le_sum fun z _ => vectorMeasure_enorm_le_variation _ (q.measurableSet_fiber z)
    _ = T.vectorMeasure.variation (⋃ z ∈ q.range, q ⁻¹' {z}) :=
      (measure_biUnion_finset hdis (fun z _ => q.measurableSet_fiber z)).symm
    _ ≤ _ := measure_mono (subset_univ _)

/-- Finite vector coefficients approximate the action of any compactly
supported normal current on continuous one-forms. These are vector atoms,
not yet normal polyhedral one-currents with controlled boundaries. -/
theorem sampled_action_tendsto (T : EuclideanNormalCurrentData)
    {K : Set ExposureEuclidean} (hK : IsCompact K)
    (hs : T.vectorMeasure.variation Kᶜ = 0)
    (q : ℕ → (ExposureEuclidean →ₛ ExposureEuclidean)) (ε : ℕ → ℝ)
    (hq : ∀ n x, x ∈ K → q n x ∈ K ∧ dist x (q n x) ≤ ε n)
    (hzero : Filter.Tendsto ε Filter.atTop (nhds 0))
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)} (hω : Continuous ω) :
    Filter.Tendsto (fun n => ∑ z ∈ (q n).range,
      ω z (T.vectorMeasure (q n ⁻¹' {z}))) Filter.atTop (nhds (T.action ω)) := by
  letI := T.finite_variation
  simp_rw [← sampled_action_eq_sum]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hω.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · exact fun n => (integrable_sampled_action T (q n) ω).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    filter_upwards [show ∀ᵐ x ∂T.vectorMeasure.variation, x ∈ K from ae_iff.mpr hs,
      T.direction_unit] with x hx hunit
    calc ‖ω (q n x) (T.direction x)‖ ≤ ‖ω (q n x)‖ * ‖T.direction x‖ :=
        (ω (q n x)).le_opNorm _
      _ = ‖ω (q n x)‖ := by rw [hunit, mul_one]
      _ ≤ C := hC _ (hq n x hx).1
  · filter_upwards [show ∀ᵐ x ∂T.vectorMeasure.variation, x ∈ K from ae_iff.mpr hs] with x hx
    have ht : Filter.Tendsto (fun n => q n x) Filter.atTop (nhds x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _ => dist_nonneg)
        (fun n => by simpa [dist_comm] using (hq n x hx).2) hzero
    exact (hω.clm_apply continuous_const).continuousAt.tendsto.comp ht

/-- Construct the finite spatial sampling sequence from compact support alone.
Neither the quantizers nor their convergence are external inputs. -/
theorem exists_current_sampling (T : EuclideanNormalCurrentData)
    {K : Set ExposureEuclidean} (hK : IsCompact K)
    (hs : T.vectorMeasure.variation Kᶜ = 0) :
    ∃ q : ℕ → (ExposureEuclidean →ₛ ExposureEuclidean),
      (∀ n x, x ∈ K → q n x ∈ K ∧ dist x (q n x) < 1 / ((n : ℝ) + 1)) ∧
      (∀ n, ∑ z ∈ (q n).range, ‖T.vectorMeasure (q n ⁻¹' {z})‖ₑ ≤
        T.vectorMeasure.variation univ) ∧
      ∀ ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ), Continuous ω →
        Filter.Tendsto (fun n => ∑ z ∈ (q n).range,
          ω z (T.vectorMeasure (q n ⁻¹' {z}))) Filter.atTop (nhds (T.action ω)) := by
  obtain ⟨q, hq, _⟩ := exists_quantizer_sequence hK
    (fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨q, hq, (fun n => sampled_mass_le T (q n)), ?_⟩
  intro ω hω
  exact sampled_action_tendsto T hK hs q _
    (fun n x hx => ⟨(hq n x hx).1, (hq n x hx).2.le⟩)
    tendsto_one_div_add_atTop_nhds_zero_nat hω

/-- Quantizing the endpoints of a finite signed atomic boundary now yields
an actual small segment correction without a supplied pairing hypothesis. -/
theorem exists_atomic_correction {K : Set ExposureEuclidean} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (x : ι → ExposureEuclidean) (hx : ∀ i, x i ∈ K) :
    ∃ q : ExposureEuclidean →ₛ ExposureEuclidean,
      (∀ z ∈ K, q z ∈ K ∧ dist z (q z) < ε) ∧
      (AtomicBoundaryCorrection.correction w x (fun i => q (x i))).variation univ ≤
        (∑ i, ‖w i‖ₑ) * ENNReal.ofReal ε := by
  obtain ⟨q, hq⟩ := exists_quantizer hK hε
  refine ⟨q, hq, AtomicBoundaryCorrection.correction_mass_le_of_displacement
    w x (fun i => q (x i)) ε _ ?_ le_rfl⟩
  intro i
  simpa [dist_eq_norm, norm_sub_rev] using (hq (x i) (hx i)).2.le

/-- Even when the number of boundary atoms grows, uniform total absolute
weight and shrinking cells give an actual sequence of vanishing corrections. -/
theorem exists_atomic_correction_sequence {K : Set ExposureEuclidean} (hK : IsCompact K)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hzero : Filter.Tendsto ε Filter.atTop (nhds 0))
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (w : ∀ n, ι n → ℝ) (x : ∀ n, ι n → ExposureEuclidean)
    (hx : ∀ n i, x n i ∈ K) (M : ENNReal) (hM : M ≠ ⊤)
    (hw : ∀ n, ∑ i, ‖w n i‖ₑ ≤ M) :
    ∃ q : ℕ → (ExposureEuclidean →ₛ ExposureEuclidean),
      (∀ n z, z ∈ K → q n z ∈ K ∧ dist z (q n z) < ε n) ∧
      Filter.Tendsto (fun n =>
        (AtomicBoundaryCorrection.correction (w n) (x n)
          (fun i => q n (x n i))).variation univ) Filter.atTop (nhds 0) := by
  choose q hq using fun n => exists_quantizer hK (hε n)
  refine ⟨q, hq, ?_⟩
  have ht := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hzero) (Or.inr hM)
  simp only [ENNReal.ofReal_zero, mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _)
  intro n
  apply AtomicBoundaryCorrection.correction_mass_le_of_displacement
    (w n) (x n) (fun i => q n (x n i)) (ε n) M _ (hw n)
  intro i
  simpa [dist_eq_norm, norm_sub_rev] using (hq n (x n i) (hx n i)).2.le

end CZExposure.CompactQuantization
