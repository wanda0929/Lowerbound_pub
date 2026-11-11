module
public import RequestProject.AppendixE.ExposureProgress

/-!
# Discarded-gap progress and angular-rate bounds

Any low-cost interval `[a,b]` with `c ≤ β` changes the progress
observable by at most `4√β(b−a)`; disjoint such intervals inside `[0,T]`
sum to at most `4T√β`.  For a `FiniteExcursionSelection`, the discarded
times are compact with `c < β`; progress speed integrates to at most
`4T√β`, and the signed angular-rate integral `∫Im(z'/z)` has magnitude
at most `8T√β` (for `β ≤ 1/12`, where `|z| ≥ 1/2`).
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

theorem low_cost_progress_increment_le {T a b β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hy : LipschitzWith K y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hlow : ∀ t ∈ Set.Icc a b, euclideanExposureCost (y t) ≤ β) :
    ‖exposureProgressPath y b - exposureProgressPath y a‖ ≤
      4 * Real.sqrt β * (b - a) := by
  rw [← integral_exposureProgressVelocity hy hu hub hdom hode ha hab hb]
  have hbnd : ∀ t ∈ Set.uIoc a b,
      ‖exposureProgressVelocity y u t‖ ≤ 4 * Real.sqrt β := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2⟩
    exact (norm_euclideanProgress_Bfield_le
      (hdom t ⟨ha.trans ht'.1, ht'.2.trans hb⟩) (hub t)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlow t ht'))
        (by norm_num))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm

theorem sum_low_cost_progress_increments_le {A : Type*}
    (I : Finset A) (l r : A → ℝ) {T β : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hT : 0 ≤ T) (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hvalid : ∀ i ∈ I, 0 ≤ l i ∧ l i ≤ r i ∧ r i ≤ T)
    (hdisj : (↑I : Set A).PairwiseDisjoint (fun i => Set.Ioo (l i) (r i)))
    (hlow : ∀ i ∈ I, ∀ t ∈ Set.Icc (l i) (r i),
      euclideanExposureCost (y t) ≤ β) :
    (∑ i ∈ I, ‖exposureProgressPath y (r i) -
      exposureProgressPath y (l i)‖) ≤ 4 * T * Real.sqrt β := by
  have hw : ∀ i ∈ I, ‖exposureProgressPath y (r i) -
        exposureProgressPath y (l i)‖ ≤
        4 * Real.sqrt β * (r i - l i) := fun i hi =>
    low_cost_progress_increment_le hy hu hub hdom hode
      (hvalid i hi).1 (hvalid i hi).2.1 (hvalid i hi).2.2 (hlow i hi)
  calc (∑ i ∈ I, ‖exposureProgressPath y (r i) -
        exposureProgressPath y (l i)‖)
      ≤ ∑ i ∈ I, 4 * Real.sqrt β * (r i - l i) := Finset.sum_le_sum hw
    _ = 4 * Real.sqrt β * ∑ i ∈ I, (r i - l i) := by
        rw [← Finset.mul_sum]
    _ ≤ 4 * Real.sqrt β * T :=
        mul_le_mul_of_nonneg_left
          (sum_disjoint_interval_lengths_le I l r hT hvalid hdisj)
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 4 * T * Real.sqrt β := by ring

namespace FiniteExcursionSelection

variable {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
variable (S : FiniteExcursionSelection T α β y u)

/-- Times not inside any retained interval. -/
def discardedTimes : Set ℝ := Set.Icc 0 T \
  ⋃ i : Fin S.count, Set.Ioo (S.segment i).a (S.segment i).b

/-- Total progress speed over the discarded times. -/
def discardedProgressSpeed : ℝ :=
  ∫ t in S.discardedTimes, ‖exposureProgressVelocity y u t‖

/-- Signed angular-rate integral `∫ Im(z'/z)` over discarded times. -/
def discardedAngularIntegral : ℝ :=
  ∫ t in S.discardedTimes, euclideanAngularRate (y t) (u t)

theorem mem_discardedTimes_iff {t : ℝ} :
    t ∈ S.discardedTimes ↔ t ∈ Set.Icc 0 T ∧
      ∀ i, t ∉ Set.Ioo (S.segment i).a (S.segment i).b := by
  simp [discardedTimes]

theorem isCompact_discardedTimes : IsCompact S.discardedTimes := by
  rw [discardedTimes, Set.diff_eq]
  exact isCompact_Icc.inter_right
    (isOpen_iUnion fun _ => isOpen_Ioo).isClosed_compl

theorem cost_lt_on_discarded {t : ℝ} (ht : t ∈ S.discardedTimes) :
    euclideanExposureCost (y t) < β :=
  S.cost_lt_outside (S.mem_discardedTimes_iff.mp ht).1
    (S.mem_discardedTimes_iff.mp ht).2

theorem volume_real_discardedTimes_le (hT : 0 ≤ T) :
    volume.real S.discardedTimes ≤ T := by
  have hle := ENNReal.toReal_mono
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono (Set.diff_subset : S.discardedTimes ⊆ Set.Icc 0 T))
  rwa [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hT),
    sub_zero] at hle

theorem discarded_progress_bounds {K : NNReal}
    (hT : 0 ≤ T) (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hβ : β ≤ 1/12) :
    IntegrableOn (exposureProgressVelocity y u) S.discardedTimes ∧
    IntegrableOn (fun t => euclideanAngularRate (y t) (u t))
      S.discardedTimes ∧
    (∀ᵐ t ∂(volume.restrict S.discardedTimes),
      HasDerivAt (exposureProgressPath y)
        (exposureProgressVelocity y u t) t) ∧
    (0 ≤ S.discardedProgressSpeed ∧
      S.discardedProgressSpeed ≤ 4 * T * Real.sqrt β) ∧
    |S.discardedAngularIntegral| ≤ 8 * T * Real.sqrt β := by
  have hDsub : S.discardedTimes ⊆ Set.Icc 0 T := Set.diff_subset
  have hVint : IntegrableOn (exposureProgressVelocity y u)
      S.discardedTimes :=
    (integrableOn_exposureProgressVelocity hy.continuous hu hub hdom).mono_set
      hDsub
  have hVbound : ∀ t ∈ S.discardedTimes,
      ‖exposureProgressVelocity y u t‖ ≤ 4 * Real.sqrt β := fun t ht =>
    (norm_euclideanProgress_Bfield_le (hdom t (hDsub ht)) (hub t)).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (S.cost_lt_on_discarded ht).le) (by norm_num))
  have hAbound : ∀ t ∈ S.discardedTimes,
      |euclideanAngularRate (y t) (u t)| ≤ 8 * Real.sqrt β := fun t ht =>
    abs_euclideanAngularRate_le (hdom t (hDsub ht)) (hub t)
      (S.cost_lt_on_discarded ht).le hβ
  have hAint : IntegrableOn (fun t => euclideanAngularRate (y t) (u t))
      S.discardedTimes := by
    apply Measure.integrableOn_of_bounded
      (S.isCompact_discardedTimes.measure_lt_top (μ := volume)).ne
      (measurable_exposureAngularRate hy.continuous.measurable
        hu).aestronglyMeasurable
    filter_upwards [ae_restrict_mem
      S.isCompact_discardedTimes.measurableSet] with t ht
    exact hAbound t ht
  have hODE : ∀ᵐ t ∂(volume.restrict S.discardedTimes),
      HasDerivAt (exposureProgressPath y) (exposureProgressVelocity y u t) t :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hDsub
      (ae_hasDerivAt_exposureProgressPath hode)
  refine ⟨hVint, hAint, hODE, ?_, ?_⟩
  · constructor
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => norm_nonneg _)
    · have hnorm := norm_setIntegral_le_of_norm_le_const
        (S.isCompact_discardedTimes.measure_lt_top (μ := volume))
        (fun t ht => by
          rw [Real.norm_eq_abs, abs_of_nonneg
            (norm_nonneg (exposureProgressVelocity y u t))]
          exact hVbound t ht)
      have hpos : 0 ≤ S.discardedProgressSpeed :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => norm_nonneg _)
      calc S.discardedProgressSpeed
          = ‖∫ t in S.discardedTimes, ‖exposureProgressVelocity y u t‖‖ := by
            rw [discardedProgressSpeed,
              Real.norm_of_nonneg (integral_nonneg_of_ae (Filter.Eventually.of_forall fun t => norm_nonneg _))]
        _ ≤ (4 * Real.sqrt β) * volume.real S.discardedTimes := hnorm
        _ ≤ (4 * Real.sqrt β) * T :=
          mul_le_mul_of_nonneg_left (S.volume_real_discardedTimes_le hT)
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        _ = 4 * T * Real.sqrt β := by ring
  · have hnorm : ‖∫ t in S.discardedTimes,
        euclideanAngularRate (y t) (u t)‖ ≤
        (8 * Real.sqrt β) * volume.real S.discardedTimes :=
      norm_setIntegral_le_of_norm_le_const
        (S.isCompact_discardedTimes.measure_lt_top (μ := volume))
        (fun t ht => hAbound t ht)
    rw [discardedAngularIntegral]
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in S.discardedTimes, euclideanAngularRate (y t) (u t)‖
        ≤ (8 * Real.sqrt β) * volume.real S.discardedTimes := hnorm
      _ ≤ (8 * Real.sqrt β) * T :=
        mul_le_mul_of_nonneg_left (S.volume_real_discardedTimes_le hT)
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      _ = 8 * T * Real.sqrt β := by ring

end FiniteExcursionSelection

end CZExposure
