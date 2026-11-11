import RequestProject.AppendixE.ActiveExposure
import RequestProject.AppendixE.FaceBlockAssembly
import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Audit: active-time clock and exposure reduction

Aggregate-import axiom audit of `ActiveClock.lean` and
`ActiveExposure.lean`, composed with `FaceBlockAssembly`,
`StateGeometry`, and `RelaxedSubsolution`.  Expected axioms are only
`[propext, Classical.choice, Quot.sound]`.

The active-time path and normalized control candidate carry no
positive-amplitude assumptions: the selector domain is the whole
`[0, S]` including `S = 0`, and `activeControl` is not asserted to
drive `activePath`.
-/

open CZExposure MeasureTheory
open scoped NNReal ENNReal

namespace CZExposure

/-! ## Unit direction -/

#check @PhysicalSegment.controlDirection
#print axioms PhysicalSegment.controlDirection
#check @PhysicalSegment.measurable_controlDirection
#print axioms PhysicalSegment.measurable_controlDirection
#check @PhysicalSegment.norm_controlDirection
#print axioms PhysicalSegment.norm_controlDirection
#check @PhysicalSegment.norm_smul_controlDirection
#print axioms PhysicalSegment.norm_smul_controlDirection
#check @PhysicalSegment.vf_real_smul_control
#print axioms PhysicalSegment.vf_real_smul_control
#check @PhysicalSegment.vf_controlDirection
#print axioms PhysicalSegment.vf_controlDirection
#check @PhysicalSegment.norm_vf_le_norm_control
#print axioms PhysicalSegment.norm_vf_le_norm_control

/-! ## Active clock -/

#check @PhysicalSegment.intervalIntegrable_controlNorm
#print axioms PhysicalSegment.intervalIntegrable_controlNorm
#check @PhysicalSegment.intervalIntegrable_controlNorm_subinterval
#print axioms PhysicalSegment.intervalIntegrable_controlNorm_subinterval
#check @PhysicalSegment.activeClock
#print axioms PhysicalSegment.activeClock
#check @PhysicalSegment.activeDuration
#print axioms PhysicalSegment.activeDuration
#check @PhysicalSegment.activeClock_zero
#print axioms PhysicalSegment.activeClock_zero
#check @PhysicalSegment.activeClock_increment
#print axioms PhysicalSegment.activeClock_increment
#check @PhysicalSegment.activeClock_increment_bounds
#print axioms PhysicalSegment.activeClock_increment_bounds
#check @PhysicalSegment.monotoneOn_activeClock
#print axioms PhysicalSegment.monotoneOn_activeClock
#check @PhysicalSegment.lipschitzOn_activeClock
#print axioms PhysicalSegment.lipschitzOn_activeClock
#check @PhysicalSegment.activeDuration_bounds
#print axioms PhysicalSegment.activeDuration_bounds
#check @PhysicalSegment.activeClock_image_interval
#print axioms PhysicalSegment.activeClock_image_interval
#check @PhysicalSegment.activeClock_mem
#print axioms PhysicalSegment.activeClock_mem
#check @PhysicalSegment.path_increment_le_activeClock
#print axioms PhysicalSegment.path_increment_le_activeClock
#check @PhysicalSegment.path_dist_le_activeClock
#print axioms PhysicalSegment.path_dist_le_activeClock
#check @PhysicalSegment.path_eq_of_activeClock_eq
#print axioms PhysicalSegment.path_eq_of_activeClock_eq
#check @PhysicalSegment.path_eq_initial_of_activeDuration_zero
#print axioms PhysicalSegment.path_eq_initial_of_activeDuration_zero

/-! ## Section, selector, active path and control -/

#check @PhysicalSegment.exists_activeClock_preimage
#print axioms PhysicalSegment.exists_activeClock_preimage
#check @PhysicalSegment.activeClockSection
#print axioms PhysicalSegment.activeClockSection
#check @PhysicalSegment.activeClockSection_spec
#print axioms PhysicalSegment.activeClockSection_spec
#check @PhysicalSegment.strictMono_activeClockSection
#print axioms PhysicalSegment.strictMono_activeClockSection
#check @PhysicalSegment.activeTimeSelector
#print axioms PhysicalSegment.activeTimeSelector
#check @PhysicalSegment.activeTimeSelector_mem
#print axioms PhysicalSegment.activeTimeSelector_mem
#check @PhysicalSegment.monotone_activeTimeSelector
#print axioms PhysicalSegment.monotone_activeTimeSelector
#check @PhysicalSegment.measurable_activeTimeSelector
#print axioms PhysicalSegment.measurable_activeTimeSelector
#check @PhysicalSegment.activeClock_activeTimeSelector
#print axioms PhysicalSegment.activeClock_activeTimeSelector
#check @PhysicalSegment.activeClock_activeTimeSelector_of_mem
#print axioms PhysicalSegment.activeClock_activeTimeSelector_of_mem
#check @PhysicalSegment.activePath
#print axioms PhysicalSegment.activePath
#check @PhysicalSegment.activePath_mem
#print axioms PhysicalSegment.activePath_mem
#check @PhysicalSegment.activePath_activeClock
#print axioms PhysicalSegment.activePath_activeClock
#check @PhysicalSegment.lipschitz_activePath
#print axioms PhysicalSegment.lipschitz_activePath
#check @PhysicalSegment.activePath_zero
#print axioms PhysicalSegment.activePath_zero
#check @PhysicalSegment.activePath_terminal
#print axioms PhysicalSegment.activePath_terminal
#check @PhysicalSegment.activePath_image_interval
#print axioms PhysicalSegment.activePath_image_interval
#check @PhysicalSegment.activeControl
#print axioms PhysicalSegment.activeControl
#check @PhysicalSegment.measurable_activeControl
#print axioms PhysicalSegment.measurable_activeControl
#check @PhysicalSegment.norm_activeControl
#print axioms PhysicalSegment.norm_activeControl

/-! ## Active exposure -/

#check @PhysicalSegment.activeExposure
#print axioms PhysicalSegment.activeExposure
#check @PhysicalSegment.weightedExposure
#print axioms PhysicalSegment.weightedExposure
#check @PhysicalSegment.continuous_cost_activePath
#print axioms PhysicalSegment.continuous_cost_activePath
#check @PhysicalSegment.intervalIntegrable_cost_activePath
#print axioms PhysicalSegment.intervalIntegrable_cost_activePath
#check @PhysicalSegment.intervalIntegrable_weightedCost
#print axioms PhysicalSegment.intervalIntegrable_weightedCost
#check @PhysicalSegment.activeCostPrimitive
#print axioms PhysicalSegment.activeCostPrimitive
#check @PhysicalSegment.activeCostPrimitive_zero
#print axioms PhysicalSegment.activeCostPrimitive_zero
#check @PhysicalSegment.hasDerivAt_activeCostPrimitive
#print axioms PhysicalSegment.hasDerivAt_activeCostPrimitive
#check @PhysicalSegment.lipschitz_activeCostPrimitive
#print axioms PhysicalSegment.lipschitz_activeCostPrimitive
#check @PhysicalSegment.ae_hasDerivAt_activeClock
#print axioms PhysicalSegment.ae_hasDerivAt_activeClock
#check @PhysicalSegment.activeExposure_eq_weightedExposure
#print axioms PhysicalSegment.activeExposure_eq_weightedExposure
#check @PhysicalSegment.activeExposure_nonneg
#print axioms PhysicalSegment.activeExposure_nonneg
#check @PhysicalSegment.activeExposure_le_exposure
#print axioms PhysicalSegment.activeExposure_le_exposure

/-! ## Edge examples -/

namespace Edge

/-! The domain of the selector is the full `[0, S]` — no positivity
hypothesis anywhere in the API. -/
#check @PhysicalSegment.activeTimeSelector
#check @PhysicalSegment.activeDuration_bounds
/-! The active path preserves the original image and endpoints. -/
#check @PhysicalSegment.activePath_image_interval
/-! The exact exposure reduction. -/
#check @PhysicalSegment.activeExposure_eq_weightedExposure
#check @PhysicalSegment.activeExposure_le_exposure

/-! (a) `unitZero` at `x0`: `S = 0`, same endpoints, zero active
exposure. -/
example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).activeDuration
      = 0 := by
  simp [PhysicalSegment.activeDuration, PhysicalSegment.activeClock]

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).activePath 0
      = (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).path 0 :=
  PhysicalSegment.activePath_zero _

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).activePath
        ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).activeDuration)
      = (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).path
          ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).duration) :=
  PhysicalSegment.activePath_terminal _

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).activeExposure
      = 0 := by
  simp [PhysicalSegment.activeExposure, PhysicalSegment.activeDuration,
    PhysicalSegment.activeClock]

/-! (b) Zero active duration forces the original path to be constant. -/
example (P : PhysicalSegment) (h : P.activeDuration = 0) {t : ℝ}
    (ht : t ∈ Set.Icc 0 P.duration) : P.path t = P.path 0 :=
  P.path_eq_initial_of_activeDuration_zero h ht

/-! (c) The candidate control has unit modulus even where the original
control vanishes under the selector. -/
example (P : PhysicalSegment) (s : ℝ) : ‖P.activeControl s‖ = 1 :=
  P.norm_activeControl s

/-! (d) Positive duration with identically zero control: the clock
removes all exposure. -/
private theorem idleExample_vf_zero :
    vf (mkState 0 1 0 1) (0 : ℂ) = 0 := by
  funext i
  fin_cases i <;> simp [vf, fC]

private def idleExample : PhysicalSegment where
  duration := 1
  duration_nonneg := by norm_num
  path := fun _ => mkState 0 1 0 1
  control := fun _ => 0
  control_measurable := measurable_const
  control_bound := fun s _ => by simp
  path_mem := fun s _ => by
    show mkState 0 1 0 1 ∈ Xset
    refine ⟨?_, ?_⟩ <;> simp
  velocity_integrable := by
    simp only [idleExample_vf_zero]
    exact (continuous_const.intervalIntegrable 0 1 :
      IntervalIntegrable (fun _ : ℝ => (0 : State)) volume 0 1)
  integralEquation := by
    intro s hs
    simp only [idleExample_vf_zero]
    simp

example : idleExample.activeDuration = 0 := by
  simp [PhysicalSegment.activeDuration, PhysicalSegment.activeClock,
    idleExample]

example : idleExample.exposure = (3 : ℝ) / 4 := by
  simp [PhysicalSegment.exposure, idleExample, cost]
  norm_num

example : idleExample.activeExposure = 0 := by
  simp [PhysicalSegment.activeExposure, PhysicalSegment.activeDuration,
    PhysicalSegment.activeClock, idleExample]

end Edge

end CZExposure
