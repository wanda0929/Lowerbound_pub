module
public import RequestProject.AppendixE.DiscardedProgress
public import RequestProject.AppendixE.PhaseTransport

/-!
# Phase transport across low-cost gaps

On `[a,b]` with `c ≤ β ≤ 1/12`, `|z| ≥ 1/2` so phase transport applies:
the real phase increment equals the angular-rate integral with magnitude
`≤ 8√β(b−a)`.  Supplied disjoint finite gap families give a product of
endpoint unit-phase ratios equal to `exp(i∑increments)`. The sum of
absolute increments is bounded by `8T√β`. A conditional corollary
identifies the signed sum with the selected discarded angular integral
when the gaps cover `D` a.e.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- The real phase increment on `[a,b]`: the angular-rate integral. -/
def exposurePhaseIncrement (y : ℝ → ExposureEuclidean) (u : ℝ → ℂ)
    (a b : ℝ) : ℝ := ∫ t in a..b, euclideanAngularRate (y t) (u t)

/-- Angular rate is interval-integrable on a low-cost interval. -/
private theorem intervalIntegrable_angularRate_low {T a b β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
    (hy : Continuous y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hβ : β ≤ 1/12)
    (hlow : ∀ t ∈ Set.Icc a b, euclideanExposureCost (y t) ≤ β) :
    IntervalIntegrable (fun t => euclideanAngularRate (y t) (u t))
      volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    (measurable_exposureAngularRate hy.measurable hu).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  exact abs_euclideanAngularRate_le
    (hdom t ⟨ha.trans ht.1, ht.2.trans hb⟩) (hub t) (hlow t ht) hβ

/-- `|z| ≥ 1/2` on a low-cost interval gives `z ≠ 0`. -/
private theorem progressPath_ne_zero_of_low {T a b β : ℝ}
    {y : ℝ → ExposureEuclidean}
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (ha : 0 ≤ a) (hb : b ≤ T)
    (hβ : β ≤ 1/12)
    (hlow : ∀ t ∈ Set.Icc a b, euclideanExposureCost (y t) ≤ β) :
    ∀ t ∈ Set.Icc a b, exposureProgressPath y t ≠ 0 := by
  intro t ht
  have h := norm_euclideanProgress_ge_half
    (hdom t ⟨ha.trans ht.1, ht.2.trans hb⟩) (hlow t ht) hβ
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h)

theorem low_cost_phase_lift {T a b β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hy : LipschitzWith K y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hβ : β ≤ 1/12)
    (hlow : ∀ t ∈ Set.Icc a b, euclideanExposureCost (y t) ≤ β) :
    AbsolutelyContinuousOnInterval
      (complexPhaseLift (exposureProgressPath y)
        (exposureProgressVelocity y u) a) a b ∧
    (∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      HasDerivAt
        (complexPhaseLift (exposureProgressPath y)
          (exposureProgressVelocity y u) a)
        (euclideanAngularRate (y t) (u t)) t) ∧
    (∀ t ∈ Set.Icc a b,
      phaseFactor (complexPhaseLift (exposureProgressPath y)
        (exposureProgressVelocity y u) a t) =
        complexUnitPhase (exposureProgressPath y t)) ∧
    complexPhaseLift (exposureProgressPath y)
        (exposureProgressVelocity y u) a b -
      complexPhaseLift (exposureProgressPath y)
        (exposureProgressVelocity y u) a a =
      exposurePhaseIncrement y u a b := by
  have hf := euclideanProgressCLM.lipschitz.comp hy
  have hne := progressPath_ne_zero_of_low hdom ha hb hβ hlow
  have hode' : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      HasDerivAt (exposureProgressPath y) (exposureProgressVelocity y u t) t :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc ha hb) (ae_hasDerivAt_exposureProgressPath hode)
  have hint := intervalIntegrable_angularRate_low
    hy.continuous hu hub hdom ha hab hb hβ hlow
  obtain ⟨_, hAC, hder, hph, hend⟩ :=
    complexPhaseLift_spec hab hf hne hode' hint
  exact ⟨hAC, hder, hph, hend⟩

theorem low_cost_phase_transport {T a b β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hy : LipschitzWith K y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hβ : β ≤ 1/12)
    (hlow : ∀ t ∈ Set.Icc a b, euclideanExposureCost (y t) ≤ β) :
    complexUnitPhase (exposureProgressPath y b) =
      phaseFactor (exposurePhaseIncrement y u a b) *
        complexUnitPhase (exposureProgressPath y a) ∧
    |exposurePhaseIncrement y u a b| ≤ 8 * Real.sqrt β * (b - a) := by
  have hf := euclideanProgressCLM.lipschitz.comp hy
  have hne := progressPath_ne_zero_of_low hdom ha hb hβ hlow
  have hode' : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      HasDerivAt (exposureProgressPath y) (exposureProgressVelocity y u t) t :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc ha hb) (ae_hasDerivAt_exposureProgressPath hode)
  have hint := intervalIntegrable_angularRate_low
    hy.continuous hu hub hdom ha hab hb hβ hlow
  refine ⟨complex_phase_transport hab hf hne hode' hint b ⟨hab, le_rfl⟩, ?_⟩
  have hbnd : ∀ t ∈ Set.uIoc a b,
      ‖euclideanAngularRate (y t) (u t)‖ ≤ 8 * Real.sqrt β := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [Real.norm_eq_abs]
    exact abs_euclideanAngularRate_le
      (hdom t ⟨ha.trans ht.1.le, ht.2.trans hb⟩) (hub t)
      (hlow t ⟨ht.1.le, ht.2⟩) hβ
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm

theorem low_cost_normalized_progress_increment_le {T a b β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hy : LipschitzWith K y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hβ : β ≤ 1/12)
    (hlow : ∀ t ∈ Set.Icc a b, euclideanExposureCost (y t) ≤ β) :
    ‖complexUnitPhase (exposureProgressPath y b) -
      complexUnitPhase (exposureProgressPath y a)‖ ≤
      8 * Real.sqrt β * (b - a) := by
  obtain ⟨htr, hE⟩ :=
    low_cost_phase_transport hy hu hub hdom hode ha hab hb hβ hlow
  have hne := progressPath_ne_zero_of_low hdom ha hb hβ hlow
  rw [htr]
  calc ‖phaseFactor (exposurePhaseIncrement y u a b) *
          complexUnitPhase (exposureProgressPath y a) -
        complexUnitPhase (exposureProgressPath y a)‖
      = ‖(phaseFactor (exposurePhaseIncrement y u a b) - 1) *
          complexUnitPhase (exposureProgressPath y a)‖ := by
        rw [sub_mul, one_mul]
    _ = ‖phaseFactor (exposurePhaseIncrement y u a b) - 1‖ := by
        rw [norm_mul, norm_complexUnitPhase
          (hne a ⟨le_rfl, hab⟩), mul_one]
    _ ≤ 8 * Real.sqrt β * (b - a) :=
        (norm_phaseFactor_sub_one_le _).trans hE

theorem finite_low_cost_phase_accounting {A : Type*}
    (I : Finset A) (l r : A → ℝ) {T β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hT : 0 ≤ T) (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hβ : β ≤ 1/12)
    (hvalid : ∀ i ∈ I, 0 ≤ l i ∧ l i ≤ r i ∧ r i ≤ T)
    (hdisj : (↑I : Set A).PairwiseDisjoint
      (fun i => Set.Ioo (l i) (r i)))
    (hlow : ∀ i ∈ I, ∀ t ∈ Set.Icc (l i) (r i),
      euclideanExposureCost (y t) ≤ β) :
    (∑ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)|) ≤
      8 * T * Real.sqrt β ∧
    |(∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i))| ≤
      8 * T * Real.sqrt β ∧
    (∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i)) =
      ∫ t in ⋃ i ∈ I, Set.Ioo (l i) (r i),
        euclideanAngularRate (y t) (u t) ∧
    (∏ i ∈ I, complexUnitPhase (exposureProgressPath y (r i)) /
        complexUnitPhase (exposureProgressPath y (l i))) =
      phaseFactor (∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i)) ∧
    ‖(∏ i ∈ I, complexUnitPhase (exposureProgressPath y (r i)) /
        complexUnitPhase (exposureProgressPath y (l i))) - 1‖ ≤
      8 * T * Real.sqrt β := by
  have hinc : ∀ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)| ≤
      8 * Real.sqrt β * (r i - l i) := fun i hi =>
    (low_cost_phase_transport hy hu hub hdom hode
      (hvalid i hi).1 (hvalid i hi).2.1 (hvalid i hi).2.2 hβ
      (hlow i hi)).2
  have hlen := sum_disjoint_interval_lengths_le I l r hT hvalid hdisj
  have hnonneg : 0 ≤ 8 * Real.sqrt β :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hsum : ∑ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)| ≤
      8 * Real.sqrt β * T := by
    calc ∑ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)|
        ≤ ∑ i ∈ I, 8 * Real.sqrt β * (r i - l i) := Finset.sum_le_sum hinc
      _ = 8 * Real.sqrt β * ∑ i ∈ I, (r i - l i) := by rw [← Finset.mul_sum]
      _ ≤ 8 * Real.sqrt β * T := mul_le_mul_of_nonneg_left hlen hnonneg
  have habs : |(∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i))| ≤
      8 * T * Real.sqrt β := by
    calc |(∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i))|
        ≤ ∑ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ 8 * T * Real.sqrt β := by
          calc ∑ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)|
              ≤ 8 * Real.sqrt β * T := hsum
            _ = 8 * T * Real.sqrt β := by ring
  have hunion : (∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i)) =
      ∫ t in ⋃ i ∈ I, Set.Ioo (l i) (r i),
        euclideanAngularRate (y t) (u t) := by
    have hint_i : ∀ i ∈ I, IntegrableOn
        (fun t => euclideanAngularRate (y t) (u t)) (Set.Ioo (l i) (r i)) := by
      intro i hi
      have h := intervalIntegrable_angularRate_low hy.continuous hu hub hdom
        (hvalid i hi).1 (hvalid i hi).2.1 (hvalid i hi).2.2 hβ (hlow i hi)
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
        (hvalid i hi).2.1).mp h).mono_set Set.Ioo_subset_Icc_self
    rw [integral_biUnion_finset I (fun i _ => measurableSet_Ioo) hdisj hint_i]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [exposurePhaseIncrement, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (hvalid i hi).2.1]
  have hprod : (∏ i ∈ I, complexUnitPhase (exposureProgressPath y (r i)) /
        complexUnitPhase (exposureProgressPath y (l i))) =
      phaseFactor (∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i)) := by
    have hfac : ∀ i ∈ I,
        complexUnitPhase (exposureProgressPath y (r i)) /
          complexUnitPhase (exposureProgressPath y (l i)) =
        phaseFactor (exposurePhaseIncrement y u (l i) (r i)) := by
      intro i hi
      have htr := (low_cost_phase_transport hy hu hub hdom hode
        (hvalid i hi).1 (hvalid i hi).2.1 (hvalid i hi).2.2 hβ
        (hlow i hi)).1
      have hz := progressPath_ne_zero_of_low hdom
        (hvalid i hi).1 (hvalid i hi).2.2 hβ (hlow i hi)
        (l i) ⟨le_rfl, (hvalid i hi).2.1⟩
      have hn : complexUnitPhase (exposureProgressPath y (l i)) ≠ 0 :=
        smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hz)) hz
      rw [htr]
      field_simp [hn]
    calc (∏ i ∈ I, complexUnitPhase (exposureProgressPath y (r i)) /
            complexUnitPhase (exposureProgressPath y (l i)))
        = ∏ i ∈ I, phaseFactor
            (exposurePhaseIncrement y u (l i) (r i)) :=
          Finset.prod_congr rfl hfac
      _ = phaseFactor (∑ i ∈ I,
            exposurePhaseIncrement y u (l i) (r i)) :=
          (phaseFactor_sum I _).symm
  refine ⟨?_, habs, hunion, hprod, ?_⟩
  · calc ∑ i ∈ I, |exposurePhaseIncrement y u (l i) (r i)|
        ≤ 8 * Real.sqrt β * T := hsum
      _ = 8 * T * Real.sqrt β := by ring
  · rw [hprod]
    calc ‖phaseFactor (∑ i ∈ I,
            exposurePhaseIncrement y u (l i) (r i)) - 1‖
        ≤ |(∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i))| :=
          norm_phaseFactor_sub_one_le _
      _ ≤ 8 * T * Real.sqrt β := habs

namespace FiniteExcursionSelection

variable {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
variable (S : FiniteExcursionSelection T α β y u)

theorem discarded_phase_product_of_gap_cover {A : Type*}
    (S : FiniteExcursionSelection T α β y u)
    (I : Finset A) (l r : A → ℝ) {K : NNReal}
    (hT : 0 ≤ T) (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hβ : β ≤ 1/12)
    (hvalid : ∀ i ∈ I, 0 ≤ l i ∧ l i ≤ r i ∧ r i ≤ T)
    (hdisj : (↑I : Set A).PairwiseDisjoint
      (fun i => Set.Ioo (l i) (r i)))
    (hgap : ∀ i ∈ I, Set.Icc (l i) (r i) ⊆ S.discardedTimes)
    (hcover : (⋃ i ∈ I, Set.Ioo (l i) (r i)) =ᵐ[volume] S.discardedTimes) :
    (∑ i ∈ I, exposurePhaseIncrement y u (l i) (r i)) =
      S.discardedAngularIntegral ∧
    (∏ i ∈ I, complexUnitPhase (exposureProgressPath y (r i)) /
        complexUnitPhase (exposureProgressPath y (l i))) =
      phaseFactor S.discardedAngularIntegral ∧
    |S.discardedAngularIntegral| ≤ 8 * T * Real.sqrt β ∧
    ‖(∏ i ∈ I, complexUnitPhase (exposureProgressPath y (r i)) /
        complexUnitPhase (exposureProgressPath y (l i))) - 1‖ ≤
      8 * T * Real.sqrt β := by
  have hlow : ∀ i ∈ I, ∀ t ∈ Set.Icc (l i) (r i),
      euclideanExposureCost (y t) ≤ β := by
    intro i hi t ht
    exact (S.cost_lt_on_discarded (hgap i hi ht)).le
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    finite_low_cost_phase_accounting I l r hT hy hu hub hdom hode hβ
      hvalid hdisj hlow
  have hInt : ∫ t in ⋃ i ∈ I, Set.Ioo (l i) (r i),
        euclideanAngularRate (y t) (u t) =
      S.discardedAngularIntegral := by
    rw [discardedAngularIntegral]
    exact setIntegral_congr_set hcover
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hInt]; exact h3
  · rw [← hInt]
    exact h4.trans (congrArg phaseFactor h3)
  · rw [← hInt, ← h3]; exact h2
  · rw [h4]
    exact (norm_phaseFactor_sub_one_le _).trans h2

end FiniteExcursionSelection

end CZExposure
