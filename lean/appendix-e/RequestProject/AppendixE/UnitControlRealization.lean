module
public import RequestProject.AppendixE.ActiveDynamics
public import RequestProject.AppendixE.FaceBlockAssembly

/-!
# Unit-control realization

Every disk-control `PhysicalSegment` is converted, with no extra
hypotheses, into a unit-modulus `PhysicalSegment` of duration
`S = A(D)`: the active-time path is used as the trajectory, and the
normalized selected control drives it by the a.e.-ODE and scalar
absolutely-continuous FTC proved in `ActiveDynamics`.

The empty-assembly `unitZero` segment already has unit control.
`FaceBlock.assembleDiskPulse` removes the unit hypothesis from the
pulse assembler: assemble arbitrary disk-control face blocks, then
normalize once.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PhysicalSegment

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

variable (P : PhysicalSegment)

/-- Complete active-time conversion; no extra hypotheses. -/
def toUnit : PhysicalSegment where
  duration := P.activeDuration
  duration_nonneg := P.activeDuration_bounds.1
  path := P.activePath
  control := P.activeControl
  control_measurable := P.measurable_activeControl
  control_bound := fun s _ => (P.norm_activeControl s).le
  path_mem := fun s _ => P.activePath_mem s
  velocity_integrable := P.intervalIntegrable_activeVelocity
  integralEquation := fun s hs => P.activePath_integralEquation hs

@[simp] theorem toUnit_duration : P.toUnit.duration = P.activeDuration := rfl

theorem toUnit_duration_le : P.toUnit.duration ≤ P.duration :=
  P.activeDuration_bounds.2

@[simp] theorem toUnit_initial : P.toUnit.path 0 = P.path 0 :=
  P.activePath_zero

@[simp] theorem toUnit_terminal :
    P.toUnit.path P.toUnit.duration = P.path P.duration :=
  P.activePath_terminal

theorem toUnit_unit : P.toUnit.UnitControl :=
  fun s _ => P.norm_activeControl s

@[simp] theorem toUnit_exposure : P.toUnit.exposure = P.activeExposure := rfl

theorem toUnit_exposure_le : P.toUnit.exposure ≤ P.exposure :=
  P.activeExposure_le_exposure

theorem toUnit_image_interval :
    P.toUnit.path '' Set.Icc 0 P.toUnit.duration =
      P.path '' Set.Icc 0 P.duration :=
  P.activePath_image_interval

/-- Any disk-control exact-CZ segment becomes a `Pulse`. -/
def toUnitPulse (hstart : P.path 0 = x0) (hend : P.path P.duration ∈ XCZ) :
    Pulse :=
  P.toUnit.toPulse P.toUnit_unit (P.toUnit_initial.trans hstart)
    (by rw [P.toUnit_terminal]; exact hend)

theorem toUnitPulse_exposure_le (hstart : P.path 0 = x0)
    (hend : P.path P.duration ∈ XCZ) :
    (P.toUnitPulse hstart hend).exposure ≤ P.exposure := by
  have h := P.toUnit_exposure_le
  have h' := P.toUnit.toPulse_exposure P.toUnit_unit
    (P.toUnit_initial.trans hstart) (by rw [P.toUnit_terminal]; exact hend)
  rw [← h'] at h
  exact h

theorem toUnitPulse_duration_le (hstart : P.path 0 = x0)
    (hend : P.path P.duration ∈ XCZ) :
    (P.toUnitPulse hstart hend).S ≤ P.duration := P.toUnit_duration_le

end CZExposure.PhysicalSegment

namespace CZExposure.FaceBlock

open PhysicalSegment

/-- Assemble disk-control blocks, then normalize the assembled segment
once: no unit-modulus hypothesis on the supplied blocks. -/
def assembleDiskPulse (blocks : List FaceBlock)
    (hphase : (blocks.map phaseRatio).prod = -1) : Pulse :=
  (assemble x0 x0_mem_Fface blocks).segment.toUnitPulse
    (assemble_initial x0 x0_mem_Fface blocks)
    (assemble_terminal_mem_XCZ blocks hphase)

theorem assembleDiskPulse_exposure_le (blocks : List FaceBlock)
    (hphase : (blocks.map phaseRatio).prod = -1) :
    (assembleDiskPulse blocks hphase).exposure ≤
      (blocks.map (fun B => B.segment.exposure)).sum :=
  (PhysicalSegment.toUnitPulse_exposure_le _ _ _).trans
    (le_of_eq (assemble_exposure x0 x0_mem_Fface blocks))

theorem assembleDiskPulse_duration_le (blocks : List FaceBlock)
    (hphase : (blocks.map phaseRatio).prod = -1) :
    (assembleDiskPulse blocks hphase).S ≤
      (blocks.map (fun B => B.segment.duration)).sum :=
  (PhysicalSegment.toUnitPulse_duration_le _ _ _).trans
    (le_of_eq (assemble_duration x0 x0_mem_Fface blocks))

end CZExposure.FaceBlock
