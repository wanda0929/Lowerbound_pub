module
public import RequestProject.AppendixE.ExposureStateLift

/-!
# Positive-cost segments and the physical clock

A `PositiveExposureSegment` is a retained interval `[a,b]` on which the
running cost `√(y 2) ≥ δ > 0`; it stores the Lipschitz constant of `y`
(the ODE gives only a.e. dynamics, not the required regularity).  On it the
lifted state `x(t)` is Lipschitz (local `C¹` inverse + compactness), obeys
`x' = f_u(x)/c(x)` a.e., and the physical clock `σ(t) = ∫_a^t 1/c` is
absolutely continuous with increments `t-s ≤ σ(t)-σ(s) ≤ (t-s)/δ`.  No
clock inversion, excursion selection, or Pulse claim here.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set
open scoped Topology

structure PositiveExposureSegment where
  a : ℝ
  b : ℝ
  a_lt_b : a < b
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  y : ℝ → ExposureEuclidean
  lipConst : NNReal
  y_lipschitz : LipschitzWith lipConst y
  u : ℝ → ℂ
  u_measurable : Measurable u
  u_bound : ∀ t, ‖u t‖ ≤ 1
  y_mem : ∀ t ∈ Set.Icc a b, y t ∈ euclideanExposureDomain
  cost_ge : ∀ t ∈ Set.Icc a b, cutoff ≤ euclideanExposureCost (y t)
  ode : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
    HasDerivAt y (euclideanBfield (y t) (u t)) t

namespace PositiveExposureSegment

variable (S : PositiveExposureSegment)

def liftedState (t : ℝ) : State := euclideanStateLift (S.y t)
def clockRate (t : ℝ) : ℝ := (euclideanExposureCost (S.y t))⁻¹
def clock (t : ℝ) : ℝ := ∫ r in S.a..t, S.clockRate r
def duration : ℝ := S.clock S.b

/-- Build a segment from a retained subinterval of a trajectory.  The
cutoff interval is supplied; see `ExcursionSelection` for construction of
retained intervals. -/
def ofTrajectory {T a b δ : ℝ} {y : ℝ → ExposureEuclidean}
    {u : ℝ → ℂ} {K : NNReal}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) (hδ : 0 < δ)
    (hy : LipschitzWith K y) (hu : Measurable u) (hu_bound : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hcutoff : ∀ t ∈ Set.Icc a b, δ ≤ euclideanExposureCost (y t)) :
    PositiveExposureSegment where
  a := a
  b := b
  a_lt_b := hab
  cutoff := δ
  cutoff_pos := hδ
  y := y
  lipConst := K
  y_lipschitz := hy
  u := u
  u_measurable := hu
  u_bound := hu_bound
  y_mem := fun t ht => hdom t ⟨ha.trans ht.1, ht.2.trans hb⟩
  cost_ge := hcutoff
  ode := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
    (Set.Icc_subset_Icc ha hb) hode

theorem cost_pos {t : ℝ} (ht : t ∈ Set.Icc S.a S.b) :
    0 < euclideanExposureCost (S.y t) :=
  S.cutoff_pos.trans_le (S.cost_ge t ht)

theorem liftedState_mem {t : ℝ} (ht : t ∈ Set.Icc S.a S.b) :
    S.liftedState t ∈ Xset :=
  (euclideanStateLift_spec (S.y_mem t ht) (S.cost_pos ht)).1

theorem cost_liftedState {t : ℝ} (ht : t ∈ Set.Icc S.a S.b) :
    cost (S.liftedState t) = euclideanExposureCost (S.y t) :=
  (euclideanStateLift_spec (S.y_mem t ht) (S.cost_pos ht)).2.2

theorem exists_lipschitzOnWith_liftedState :
    ∃ K : NNReal, LipschitzOnWith K S.liftedState (Set.Icc S.a S.b) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro t ht
  obtain ⟨K, U, hU, hLip⟩ :=
    (contDiffAt_euclideanStateLift (S.cost_pos ht)).exists_lipschitzOnWith
  have hpre : S.y ⁻¹' U ∈ 𝓝 t :=
    S.y_lipschitz.continuous.continuousAt.preimage_mem_nhds hU
  refine ⟨K * S.lipConst, S.y ⁻¹' U, nhdsWithin_le_nhds hpre, ?_⟩
  exact hLip.comp S.y_lipschitz.lipschitzOnWith (fun r hr => hr)

theorem continuousOn_liftedState : ContinuousOn S.liftedState (Set.Icc S.a S.b) :=
  let ⟨_, hK⟩ := S.exists_lipschitzOnWith_liftedState
  hK.continuousOn

theorem ae_hasDerivAt_liftedState :
    ∀ᵐ t ∂(volume.restrict (Set.Icc S.a S.b)),
      HasDerivAt S.liftedState
        ((cost (S.liftedState t))⁻¹ • vf (S.liftedState t) (S.u t)) t := by
  filter_upwards [S.ode, ae_restrict_mem measurableSet_Icc] with t hode htmem
  exact hasDerivAt_lifted_exposure_path (S.u t) (S.y_mem t htmem)
    (S.cost_pos htmem) hode

theorem continuousOn_clockRate : ContinuousOn S.clockRate (Set.Icc S.a S.b) := by
  have hc : Continuous fun t => euclideanExposureCost (S.y t) :=
    continuous_euclideanExposureCost.comp S.y_lipschitz.continuous
  exact hc.continuousOn.inv₀ fun t ht => (S.cost_pos ht).ne'

theorem measurable_clockRate : Measurable S.clockRate :=
  (continuous_euclideanExposureCost.comp
    S.y_lipschitz.continuous).measurable.inv

theorem intervalIntegrable_clockRate :
    IntervalIntegrable S.clockRate volume S.a S.b :=
  S.continuousOn_clockRate.intervalIntegrable_of_Icc S.a_lt_b.le

theorem clock_at_start : S.clock S.a = 0 := by
  simp [clock, intervalIntegral.integral_same]

theorem clockRate_bounds {t : ℝ} (ht : t ∈ Set.Icc S.a S.b) :
    1 ≤ S.clockRate t ∧ S.clockRate t ≤ S.cutoff⁻¹ := by
  have h1 : euclideanExposureCost (S.y t) ≤ 1 := by
    rw [← S.cost_liftedState ht]; exact cost_le_one (S.liftedState_mem ht)
  constructor
  · rw [← inv_one]
    exact inv_anti₀ (S.cost_pos ht) h1
  · exact inv_anti₀ S.cutoff_pos (S.cost_ge t ht)

theorem clock_increment_bounds {s t : ℝ}
    (hs : s ∈ Set.Icc S.a S.b) (ht : t ∈ Set.Icc S.a S.b) (hst : s ≤ t) :
    t - s ≤ S.clock t - S.clock s ∧
      S.clock t - S.clock s ≤ (t - s) / S.cutoff := by
  have h_as : IntervalIntegrable S.clockRate volume S.a s :=
    (S.continuousOn_clockRate.mono
      (Set.Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
  have h_at : IntervalIntegrable S.clockRate volume S.a t :=
    (S.continuousOn_clockRate.mono
      (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have h_st : IntervalIntegrable S.clockRate volume s t :=
    (S.continuousOn_clockRate.mono
      (Set.Icc_subset_Icc hs.1 ht.2)).intervalIntegrable_of_Icc hst
  have hdiff : S.clock t - S.clock s = ∫ r in s..t, S.clockRate r :=
    intervalIntegral.integral_interval_sub_left h_at h_as
  have hmem : ∀ r ∈ Set.Icc s t, r ∈ Set.Icc S.a S.b := fun r hr =>
    ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
  constructor
  · rw [hdiff]
    calc t - s = ∫ r in s..t, (1:ℝ) := by
          simp [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ r in s..t, S.clockRate r :=
        intervalIntegral.integral_mono_on hst intervalIntegrable_const h_st
          fun r hr => (S.clockRate_bounds (hmem r hr)).1
  · rw [hdiff]
    calc (∫ r in s..t, S.clockRate r) ≤ ∫ r in s..t, S.cutoff⁻¹ :=
        intervalIntegral.integral_mono_on hst h_st intervalIntegrable_const
          fun r hr => (S.clockRate_bounds (hmem r hr)).2
      _ = (t - s) / S.cutoff := by
        simp [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

theorem strictMonoOn_clock : StrictMonoOn S.clock (Set.Icc S.a S.b) := by
  intro s hs t ht hst
  have h := (S.clock_increment_bounds hs ht hst.le).1
  linarith

theorem duration_bounds : 0 < S.duration ∧ S.duration ≤ (S.b - S.a) / S.cutoff := by
  have hb : S.b ∈ Set.Icc S.a S.b := ⟨S.a_lt_b.le, le_rfl⟩
  have ha : S.a ∈ Set.Icc S.a S.b := ⟨le_rfl, S.a_lt_b.le⟩
  have h := S.clock_increment_bounds ha hb S.a_lt_b.le
  rw [S.clock_at_start, sub_zero] at h
  show 0 < S.clock S.b ∧ S.clock S.b ≤ (S.b - S.a) / S.cutoff
  constructor
  · have := h.1; have := S.a_lt_b; linarith
  · exact h.2

theorem hasDerivAt_clock {t : ℝ} (ht : t ∈ Set.Icc S.a S.b) :
    HasDerivAt S.clock (S.clockRate t) t := by
  have hint : IntervalIntegrable S.clockRate volume S.a t :=
    (S.continuousOn_clockRate.mono
      (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hc' : Continuous fun t => euclideanExposureCost (S.y t) :=
    continuous_euclideanExposureCost.comp S.y_lipschitz.continuous
  have hcont : ContinuousAt S.clockRate t :=
    hc'.continuousAt.inv₀ (S.cost_pos ht).ne'
  exact intervalIntegral.integral_hasDerivAt_right hint
    S.measurable_clockRate.stronglyMeasurable.stronglyMeasurableAtFilter
    hcont

theorem absolutelyContinuous_clock :
    AbsolutelyContinuousOnInterval S.clock S.a S.b :=
  S.intervalIntegrable_clockRate.absolutelyContinuousOnInterval_intervalIntegral
    Set.left_mem_uIcc

/-- Exposure-parameter accounting identity: `c·σ' = 1` integrates to the
interval length.  Clock inversion/substitution remains unproved. -/
theorem integral_cost_mul_clockRate :
    (∫ t in S.a..S.b, cost (S.liftedState t) * S.clockRate t) = S.b - S.a := by
  have hcong : ∀ t ∈ Set.uIcc S.a S.b,
      cost (S.liftedState t) * S.clockRate t = 1 := fun t ht => by
    have ht' : t ∈ Set.Icc S.a S.b := Set.uIcc_of_le S.a_lt_b.le ▸ ht
    show cost (S.liftedState t) * S.clockRate t = 1
    rw [S.cost_liftedState ht']
    exact mul_inv_cancel₀ (S.cost_pos ht').ne'
  rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const]
  simp [smul_eq_mul]

end PositiveExposureSegment

end CZExposure
