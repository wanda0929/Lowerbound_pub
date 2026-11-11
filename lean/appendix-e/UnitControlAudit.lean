import RequestProject.AppendixE.UnitControlRealization
import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Audit: complete disk-to-unit control conversion

Aggregate-import axiom audit of `ActiveDynamics.lean` and
`UnitControlRealization.lean`, composed with `StateGeometry` and
`RelaxedSubsolution`.  Expected axioms are only
`[propext, Classical.choice, Quot.sound]`.

`P.toUnit` is a `PhysicalSegment` construction with NO hypotheses —
no unit control, no amplitude positivity, no inverse regularity.
-/

open CZExposure MeasureTheory
open scoped NNReal ENNReal

namespace CZExposure

/-! ## Null-set transport and clock derivative -/

#check @PhysicalSegment.activeClock_image_null
#print axioms PhysicalSegment.activeClock_image_null
#check @PhysicalSegment.activeTimeSelector_ae_transfer
#print axioms PhysicalSegment.activeTimeSelector_ae_transfer
#check @PhysicalSegment.ae_hasDerivAt_activeClock_onInterval
#print axioms PhysicalSegment.ae_hasDerivAt_activeClock_onInterval
#check @PhysicalSegment.activeClock_zero_control_image_null
#print axioms PhysicalSegment.activeClock_zero_control_image_null
#check @PhysicalSegment.ae_selected_control_ne_zero
#print axioms PhysicalSegment.ae_selected_control_ne_zero
#check @PhysicalSegment.ae_selected_time_mem_interior
#print axioms PhysicalSegment.ae_selected_time_mem_interior

/-! ## Active-time dynamics -/

#check @PhysicalSegment.ae_hasDerivAt_path
#print axioms PhysicalSegment.ae_hasDerivAt_path
#check @PhysicalSegment.ae_hasDerivAt_activePath
#print axioms PhysicalSegment.ae_hasDerivAt_activePath
#check @PhysicalSegment.intervalIntegrable_activeVelocity_coord
#print axioms PhysicalSegment.intervalIntegrable_activeVelocity_coord
#check @PhysicalSegment.intervalIntegrable_activeVelocity
#print axioms PhysicalSegment.intervalIntegrable_activeVelocity
#check @PhysicalSegment.activePath_integralEquation_coord
#print axioms PhysicalSegment.activePath_integralEquation_coord
#check @PhysicalSegment.activePath_integralEquation
#print axioms PhysicalSegment.activePath_integralEquation

/-! ## Unit realization -/

#check @PhysicalSegment.toUnit
#print axioms PhysicalSegment.toUnit
#check @PhysicalSegment.toUnit_duration
#print axioms PhysicalSegment.toUnit_duration
#check @PhysicalSegment.toUnit_duration_le
#print axioms PhysicalSegment.toUnit_duration_le
#check @PhysicalSegment.toUnit_initial
#print axioms PhysicalSegment.toUnit_initial
#check @PhysicalSegment.toUnit_terminal
#print axioms PhysicalSegment.toUnit_terminal
#check @PhysicalSegment.toUnit_unit
#print axioms PhysicalSegment.toUnit_unit
#check @PhysicalSegment.toUnit_exposure
#print axioms PhysicalSegment.toUnit_exposure
#check @PhysicalSegment.toUnit_exposure_le
#print axioms PhysicalSegment.toUnit_exposure_le
#check @PhysicalSegment.toUnit_image_interval
#print axioms PhysicalSegment.toUnit_image_interval
#check @PhysicalSegment.toUnitPulse
#print axioms PhysicalSegment.toUnitPulse
#check @PhysicalSegment.toUnitPulse_exposure_le
#print axioms PhysicalSegment.toUnitPulse_exposure_le
#check @PhysicalSegment.toUnitPulse_duration_le
#print axioms PhysicalSegment.toUnitPulse_duration_le

/-! ## Disk-pulse assembler -/

/-! `toUnit` is a `PhysicalSegment`-valued map with no premises; the
two assemblers are displayed side by side — the disk assembler needs
only the block list and the phase product, while the original
`assemblePulse` still takes the unit hypothesis explicitly. -/

#check @PhysicalSegment.toUnit
#check @PhysicalSegment.toUnitPulse
#check @FaceBlock.assembleDiskPulse
#print axioms FaceBlock.assembleDiskPulse
#check @FaceBlock.assembleDiskPulse_exposure_le
#print axioms FaceBlock.assembleDiskPulse_exposure_le
#check @FaceBlock.assembleDiskPulse_duration_le
#print axioms FaceBlock.assembleDiskPulse_duration_le
#check @FaceBlock.assemblePulse

/-! ## Edge examples -/

namespace Edge

/-! (a) `unitZero` at `x0` converts: `S = 0`, unit norm at time `0`,
same endpoints, zero exposure. -/

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).toUnit.duration
      = 0 := by
  simp [PhysicalSegment.activeDuration, PhysicalSegment.activeClock]

example :
    ‖(PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).toUnit.control
        0‖ = 1 :=
  (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).norm_activeControl 0

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).toUnit.path 0
      = x0 := by
  simp [PhysicalSegment.unitZero]

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).toUnit.path
        ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).toUnit.duration)
      = x0 := by
  rw [PhysicalSegment.toUnit_terminal]
  simp

example :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).toUnit.exposure
      = 0 := by
  simp [PhysicalSegment.activeExposure, PhysicalSegment.activeDuration,
    PhysicalSegment.activeClock]

/-! (b) Positive duration with identically zero control converts to a
zero-duration unit segment with zero exposure, while the original
exposure is `3/4`. -/

private theorem idle_vf_zero :
    vf (mkState 0 1 0 1) (0 : ℂ) = 0 := by
  funext i
  fin_cases i <;> simp [vf, fC]

private def idleSegment : PhysicalSegment where
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
    simp only [idle_vf_zero]
    exact (continuous_const.intervalIntegrable 0 1 :
      IntervalIntegrable (fun _ : ℝ => (0 : State)) volume 0 1)
  integralEquation := by
    intro s hs
    simp only [idle_vf_zero]
    simp

example : idleSegment.activeDuration = 0 := by
  simp [PhysicalSegment.activeDuration, PhysicalSegment.activeClock,
    idleSegment]

example : idleSegment.exposure = (3 : ℝ) / 4 := by
  simp [PhysicalSegment.exposure, idleSegment, cost]
  norm_num

example : idleSegment.toUnit.duration = 0 := by
  simp [PhysicalSegment.activeDuration, PhysicalSegment.activeClock,
    idleSegment]

example : idleSegment.toUnit.exposure = 0 := by
  simp [PhysicalSegment.activeExposure, PhysicalSegment.activeDuration,
    PhysicalSegment.activeClock, idleSegment]

example : idleSegment.toUnit.UnitControl := idleSegment.toUnit_unit

/-! Its all-time integral equation is inherited — here at `s = 0`. -/
example : idleSegment.toUnit.path 0 = idleSegment.toUnit.path 0 +
    ∫ r in (0:ℝ)..0,
      vf (idleSegment.toUnit.path r) (idleSegment.toUnit.control r) :=
  idleSegment.toUnit.integralEquation 0
    ⟨le_rfl, idleSegment.toUnit.duration_nonneg⟩

/-! (c) General join/all-times integral equation is inherited,
including through control jumps: `toUnit` is a `PhysicalSegment`, so
concatenation applies without further proof. -/
example (P : PhysicalSegment) {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.toUnit.duration) :
    P.toUnit.path s = P.toUnit.path 0 +
      ∫ r in (0:ℝ)..s, vf (P.toUnit.path r) (P.toUnit.control r) :=
  P.toUnit.integralEquation s hs

end Edge

end CZExposure
