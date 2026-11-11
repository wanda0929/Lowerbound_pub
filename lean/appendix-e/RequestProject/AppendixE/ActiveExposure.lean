module
public import RequestProject.AppendixE.ActiveClock
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Active-time exposure reduction

The exact cost identity `∫₀ˢ c(Y(s)) ds = ∫₀ᴰ c(x(t)) ‖u(t)‖ dt` for
every `PhysicalSegment`, hence `≤ P.exposure`.  The proof composes a
globally `1`-Lipschitz cost primitive `Φ(s) = ∫₀ˢ c(Y)` with the
original clock `A` and applies the absolutely-continuous FTC; it does
not assume a continuous inverse or a change-of-variables theorem for
the possibly discontinuous selector.  Clock plateaux, `D = 0`, and
`S = 0` are handled uniformly.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PhysicalSegment

open MeasureTheory Set
open scoped NNReal ENNReal

variable (P : PhysicalSegment)

/-- The exposure carried by the active-time path. -/
def activeExposure : ℝ :=
  ∫ s in (0:ℝ)..P.activeDuration, cost (P.activePath s)

/-- The elapsed-time weighted exposure `∫ c(x)‖u‖`. -/
def weightedExposure : ℝ :=
  ∫ t in (0:ℝ)..P.duration, cost (P.path t) * ‖P.control t‖

theorem continuous_cost_activePath :
    Continuous (fun s => cost (P.activePath s)) :=
  contDiff_cost.continuous.comp P.lipschitz_activePath.continuous

theorem intervalIntegrable_cost_activePath (a b : ℝ) :
    IntervalIntegrable (fun s => cost (P.activePath s)) volume a b :=
  P.continuous_cost_activePath.intervalIntegrable a b

theorem intervalIntegrable_weightedCost :
    IntervalIntegrable (fun t => cost (P.path t) * ‖P.control t‖)
      volume 0 P.duration := by
  have hc : ContinuousOn (fun t => cost (P.path t))
      (Set.uIcc 0 P.duration) := by
    rw [Set.uIcc_of_le P.duration_nonneg]
    exact contDiff_cost.continuous.continuousOn.comp P.continuousOn_path
      (Set.mapsTo_univ _ _)
  exact P.intervalIntegrable_controlNorm.continuousOn_mul hc

/-- The cost primitive `Φ(s) = ∫₀ˢ c(Y)`, globally defined. -/
def activeCostPrimitive (s : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..s, cost (P.activePath r)

@[simp] theorem activeCostPrimitive_zero : P.activeCostPrimitive 0 = 0 := by
  simp [activeCostPrimitive]

theorem hasDerivAt_activeCostPrimitive (s : ℝ) :
    HasDerivAt P.activeCostPrimitive (cost (P.activePath s)) s :=
  intervalIntegral.integral_hasDerivAt_right
    (P.intervalIntegrable_cost_activePath 0 s)
    (P.continuous_cost_activePath.stronglyMeasurableAtFilter volume
      (nhds s))
    P.continuous_cost_activePath.continuousAt

theorem lipschitz_activeCostPrimitive :
    LipschitzWith 1 P.activeCostPrimitive := by
  intro s t
  rw [edist_dist, Real.dist_eq, ENNReal.coe_one, one_mul, edist_dist,
    Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  have hsplit : P.activeCostPrimitive s - P.activeCostPrimitive t =
      ∫ r in t..s, cost (P.activePath r) :=
    intervalIntegral.integral_interval_sub_left
      (P.intervalIntegrable_cost_activePath 0 s)
      (P.intervalIntegrable_cost_activePath 0 t)
  rw [hsplit]
  rcases le_total s t with hst | hst
  · rw [intervalIntegral.integral_symm, abs_neg, abs_sub_comm s t,
      abs_of_nonneg (sub_nonneg.mpr hst)]
    calc |∫ r in s..t, cost (P.activePath r)|
        ≤ ∫ r in s..t, |cost (P.activePath r)| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm hst
              (f := fun r => cost (P.activePath r)) (μ := volume))
      _ ≤ ∫ r in s..t, (1:ℝ) := by
          apply intervalIntegral.integral_mono_on hst
            ((P.intervalIntegrable_cost_activePath s t).norm)
            (continuous_const.intervalIntegrable s t :
              IntervalIntegrable (fun _ => (1:ℝ)) volume s t)
          intro r _
          rw [Real.norm_eq_abs, abs_of_nonneg (cost_nonneg _)]
          exact cost_le_one (P.activePath_mem r)
      _ = t - s := by simp
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    calc |∫ r in t..s, cost (P.activePath r)|
        ≤ ∫ r in t..s, |cost (P.activePath r)| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm hst
              (f := fun r => cost (P.activePath r)) (μ := volume))
      _ ≤ ∫ r in t..s, (1:ℝ) := by
          apply intervalIntegral.integral_mono_on hst
            ((P.intervalIntegrable_cost_activePath t s).norm)
            (continuous_const.intervalIntegrable t s :
              IntervalIntegrable (fun _ => (1:ℝ)) volume t s)
          intro r _
          rw [Real.norm_eq_abs, abs_of_nonneg (cost_nonneg _)]
          exact cost_le_one (P.activePath_mem r)
      _ = s - t := by simp

theorem ae_hasDerivAt_activeClock :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 P.duration →
      HasDerivAt P.activeClock ‖P.control t‖ t := by
  have h := P.intervalIntegrable_controlNorm.ae_hasDerivAt_integral
  filter_upwards [h] with t ht htI
  exact ht
    (by
      rw [Set.uIoc_of_le P.duration_nonneg] at htI
      rw [Set.uIcc_of_le P.duration_nonneg]
      exact Set.Ioc_subset_Icc_self htI)
    0 (Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, P.duration_nonneg⟩))

/-- The central identity: exposure along the active-time path equals
the elapsed-time cost weighted by the control amplitude.  Proved by
composing the `1`-Lipschitz primitive `Φ` with the `1`-Lipschitz
clock `A` and applying the absolutely-continuous FTC — no inverse
theorem for the selector is used. -/
theorem activeExposure_eq_weightedExposure :
    P.activeExposure = P.weightedExposure := by
  set H := fun t => P.activeCostPrimitive (P.activeClock t) with hH
  have hLipH : LipschitzOnWith 1 H (Set.Icc 0 P.duration) := by
    intro s hs t ht
    calc edist (H s) (H t)
        ≤ 1 * edist (P.activeClock s) (P.activeClock t) :=
          P.lipschitz_activeCostPrimitive _ _
      _ ≤ 1 * (1 * edist s t) :=
          mul_le_mul' le_rfl (P.lipschitzOn_activeClock hs ht)
      _ = 1 * edist s t := by rw [one_mul]
  have hAC : AbsolutelyContinuousOnInterval H 0 P.duration :=
    ((Set.uIcc_of_le P.duration_nonneg).symm ▸
      hLipH).absolutelyContinuousOnInterval
  have hderiv : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 P.duration →
      HasDerivAt H (cost (P.path t) * ‖P.control t‖) t := by
    filter_upwards [P.ae_hasDerivAt_activeClock] with t ht htI
    have htmem : t ∈ Set.Icc 0 P.duration := by
      rw [Set.uIoc_of_le P.duration_nonneg] at htI
      exact Set.Ioc_subset_Icc_self htI
    have hc := (P.hasDerivAt_activeCostPrimitive
      (P.activeClock t)).comp t (ht htI)
    rwa [P.activePath_activeClock htmem] at hc
  have hEq : deriv H =ᵐ[volume.restrict (Set.uIoc 0 P.duration)]
      (fun t => cost (P.path t) * ‖P.control t‖) := by
    rw [Set.uIoc_of_le P.duration_nonneg] at hderiv ⊢
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mpr hderiv]
      with t ht
    exact ht.deriv
  have key := (intervalIntegral.integral_congr_ae_restrict hEq).symm.trans
      hAC.integral_deriv_eq_sub
  have hHD : H P.duration = P.activeExposure := rfl
  have hH0 : H 0 = 0 := by
    show P.activeCostPrimitive (P.activeClock 0) = 0
    rw [activeClock_zero, activeCostPrimitive_zero]
  have key2 : P.weightedExposure = P.activeExposure := by
    unfold weightedExposure
    rw [key, hHD, hH0, sub_zero]
  exact key2.symm

theorem activeExposure_nonneg : 0 ≤ P.activeExposure :=
  intervalIntegral.integral_nonneg P.activeDuration_bounds.1
    (fun _ _ => cost_nonneg _)

theorem activeExposure_le_exposure :
    P.activeExposure ≤ P.exposure := by
  rw [P.activeExposure_eq_weightedExposure]
  show (∫ t in (0:ℝ)..P.duration,
      cost (P.path t) * ‖P.control t‖) ≤ P.exposure
  have h := intervalIntegral.integral_mono_on P.duration_nonneg
    P.intervalIntegrable_weightedCost P.cost_intervalIntegrable
    (fun t ht => (mul_le_mul_of_nonneg_left
      (P.control_bound t ht) (cost_nonneg _)).trans_eq (mul_one _))
  exact h

end CZExposure.PhysicalSegment
