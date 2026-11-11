import RequestProject.AppendixE.FaceBlockAssembly
import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Audit: physical concatenation and face-block assembly

Aggregate-import axiom audit of `PhysicalConcatenation.lean` and
`FaceBlockAssembly.lean`, composed with `StateGeometry` and
`RelaxedSubsolution` to check namespace compatibility.  Expected
axioms are only `[propext, Classical.choice, Quot.sound]`.

The assembly is conditional on supplied `FaceBlock`s: nothing here
produces the face-to-face blocks, and `assemblePulse` keeps the
unit-control and phase-product hypotheses explicit.
-/

open CZExposure
open scoped NNReal ENNReal

namespace CZExposure

/-! ## Physical concatenation -/

#check @PhysicalSegment.Concatenation.splice
#print axioms PhysicalSegment.Concatenation.splice
#check @PhysicalSegment.Concatenation.intervalIntegrable_splice
#print axioms PhysicalSegment.Concatenation.intervalIntegrable_splice
#check @PhysicalSegment.Concatenation.integral_splice
#print axioms PhysicalSegment.Concatenation.integral_splice
#check @PhysicalSegment.UnitControl
#check @PhysicalSegment.unitZero
#print axioms PhysicalSegment.unitZero
#check @PhysicalSegment.unitZero_duration
#print axioms PhysicalSegment.unitZero_duration
#check @PhysicalSegment.unitZero_path
#print axioms PhysicalSegment.unitZero_path
#check @PhysicalSegment.unitZero_exposure
#print axioms PhysicalSegment.unitZero_exposure
#check @PhysicalSegment.unitZero_unit
#print axioms PhysicalSegment.unitZero_unit
#check @PhysicalSegment.concat
#print axioms PhysicalSegment.concat
#check @PhysicalSegment.concat_duration
#print axioms PhysicalSegment.concat_duration
#check @PhysicalSegment.concat_initial
#print axioms PhysicalSegment.concat_initial
#check @PhysicalSegment.concat_terminal
#print axioms PhysicalSegment.concat_terminal
#check @PhysicalSegment.concat_path_left
#print axioms PhysicalSegment.concat_path_left
#check @PhysicalSegment.concat_path_right
#print axioms PhysicalSegment.concat_path_right
#check @PhysicalSegment.concat_control_left
#print axioms PhysicalSegment.concat_control_left
#check @PhysicalSegment.concat_control_right
#print axioms PhysicalSegment.concat_control_right
#check @PhysicalSegment.concat_exposure
#print axioms PhysicalSegment.concat_exposure
#check @PhysicalSegment.concat_unit
#print axioms PhysicalSegment.concat_unit

/-! ## Face blocks and alignment -/

#check @FaceBlock
#check @FaceBlock.mk
#check @FaceBlock.initial
#print axioms FaceBlock.initial
#check @FaceBlock.terminal
#print axioms FaceBlock.terminal
#check @FaceBlock.phaseRatio
#print axioms FaceBlock.phaseRatio
#check @FaceBlock.unitZero
#print axioms FaceBlock.unitZero
#check @FaceBlock.unitZero_initial
#print axioms FaceBlock.unitZero_initial
#check @FaceBlock.unitZero_terminal
#print axioms FaceBlock.unitZero_terminal
#check @FaceBlock.unitZero_duration
#print axioms FaceBlock.unitZero_duration
#check @FaceBlock.unitZero_exposure
#print axioms FaceBlock.unitZero_exposure
#check @FaceBlock.unitZero_phaseRatio
#print axioms FaceBlock.unitZero_phaseRatio
#check @FaceBlock.unitZero_unit
#print axioms FaceBlock.unitZero_unit
#check @FaceBlock.align
#print axioms FaceBlock.align
#check @FaceBlock.align_initial
#print axioms FaceBlock.align_initial
#check @FaceBlock.align_terminal
#print axioms FaceBlock.align_terminal
#check @FaceBlock.align_duration
#print axioms FaceBlock.align_duration
#check @FaceBlock.align_exposure
#print axioms FaceBlock.align_exposure
#check @FaceBlock.align_phaseRatio
#print axioms FaceBlock.align_phaseRatio
#check @FaceBlock.align_unit
#print axioms FaceBlock.align_unit
#check @FaceBlock.concat
#print axioms FaceBlock.concat
#check @FaceBlock.concat_initial
#print axioms FaceBlock.concat_initial
#check @FaceBlock.concat_terminal
#print axioms FaceBlock.concat_terminal
#check @FaceBlock.concat_duration
#print axioms FaceBlock.concat_duration
#check @FaceBlock.concat_exposure
#print axioms FaceBlock.concat_exposure
#check @FaceBlock.concat_phaseRatio
#print axioms FaceBlock.concat_phaseRatio
#check @FaceBlock.concat_unit
#print axioms FaceBlock.concat_unit

/-! ## Automatic assembly -/

#check @FaceBlock.appendAligned
#print axioms FaceBlock.appendAligned
#check @FaceBlock.appendAligned_initial
#print axioms FaceBlock.appendAligned_initial
#check @FaceBlock.appendAligned_duration
#print axioms FaceBlock.appendAligned_duration
#check @FaceBlock.appendAligned_exposure
#print axioms FaceBlock.appendAligned_exposure
#check @FaceBlock.appendAligned_phaseRatio
#print axioms FaceBlock.appendAligned_phaseRatio
#check @FaceBlock.appendAligned_unit
#print axioms FaceBlock.appendAligned_unit
#check @FaceBlock.chainFrom
#print axioms FaceBlock.chainFrom
#check @FaceBlock.chainFrom_initial
#print axioms FaceBlock.chainFrom_initial
#check @FaceBlock.chainFrom_duration
#print axioms FaceBlock.chainFrom_duration
#check @FaceBlock.chainFrom_exposure
#print axioms FaceBlock.chainFrom_exposure
#check @FaceBlock.chainFrom_phaseRatio
#print axioms FaceBlock.chainFrom_phaseRatio
#check @FaceBlock.chainFrom_unit
#print axioms FaceBlock.chainFrom_unit
#check @FaceBlock.assemble
#print axioms FaceBlock.assemble
#check @FaceBlock.assemble_initial
#print axioms FaceBlock.assemble_initial
#check @FaceBlock.assemble_duration
#print axioms FaceBlock.assemble_duration
#check @FaceBlock.assemble_exposure
#print axioms FaceBlock.assemble_exposure
#check @FaceBlock.assemble_phaseRatio
#print axioms FaceBlock.assemble_phaseRatio
#check @FaceBlock.assemble_unit
#print axioms FaceBlock.assemble_unit
#check @FaceBlock.x0_mem_Fface
#print axioms FaceBlock.x0_mem_Fface
#check @FaceBlock.assemble_terminal_mem_XCZ
#print axioms FaceBlock.assemble_terminal_mem_XCZ
#check @FaceBlock.assemblePulse
#print axioms FaceBlock.assemblePulse
#check @FaceBlock.assemblePulse_exposure
#print axioms FaceBlock.assemblePulse_exposure

/-! ## Edge examples -/

namespace Edge

/-- Two zero-duration unit segments at the same state concatenate:
the result has duration `0`, initial path `x0`, exposure `0`, and
unit control on its singleton interval. -/
example : ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).concat
      (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1)
      rfl).duration = 0 := by
  simp

example : ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).concat
      (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1)
      rfl).path 0 = x0 := by
  simp

example : ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).concat
      (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1)
      rfl).exposure = 0 := by
  simp [PhysicalSegment.exposure]

example : ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).concat
      (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1)
      rfl).UnitControl :=
  PhysicalSegment.concat_unit _ _ rfl
    (PhysicalSegment.unitZero_unit _ _)
    (PhysicalSegment.unitZero_unit _ _)

/-- At a generic join the path takes the first segment's value (which
equals `Q.path 0` by `hmatch`) and the control takes the first
segment's value — no control agreement is required. -/
example (P Q : PhysicalSegment) (h : P.path P.duration = Q.path 0) :
    (P.concat Q h).path P.duration = Q.path 0 := by
  rw [PhysicalSegment.concat_path_left P Q h (le_refl P.duration)]
  exact h

example (P Q : PhysicalSegment) (h : P.path P.duration = Q.path 0) :
    (P.concat Q h).control P.duration = P.control P.duration :=
  PhysicalSegment.concat_control_left P Q h (le_refl P.duration)

/-- The empty assembly at `p`: duration `0`, exposure `0`, both
endpoints `p`, phase ratio `1`, and unit control from the empty
hypothesis. -/
example (p : State) (hp : p ∈ Fface) :
    (FaceBlock.assemble p hp []).initial = p :=
  FaceBlock.assemble_initial p hp []

example (p : State) (hp : p ∈ Fface) :
    (FaceBlock.assemble p hp []).terminal = p :=
  FaceBlock.unitZero_terminal p hp

example (p : State) (hp : p ∈ Fface) :
    (FaceBlock.assemble p hp []).segment.duration = 0 :=
  FaceBlock.unitZero_duration p hp

example (p : State) (hp : p ∈ Fface) :
    (FaceBlock.assemble p hp []).segment.exposure = 0 :=
  FaceBlock.unitZero_exposure p hp

example (p : State) (hp : p ∈ Fface) :
    (FaceBlock.assemble p hp []).phaseRatio = 1 :=
  FaceBlock.unitZero_phaseRatio p hp

example (p : State) (hp : p ∈ Fface) :
    (FaceBlock.assemble p hp []).segment.UnitControl :=
  FaceBlock.assemble_unit p hp []
    (fun B hB => (List.not_mem_nil hB).elim)

/-- Unit-control preservation is uniform in the supplied list. -/
example (p : State) (hp : p ∈ Fface) (blocks : List FaceBlock)
    (hus : ∀ B ∈ blocks, B.segment.UnitControl) :
    (FaceBlock.assemble p hp blocks).segment.UnitControl :=
  FaceBlock.assemble_unit p hp blocks hus

end Edge

end CZExposure
