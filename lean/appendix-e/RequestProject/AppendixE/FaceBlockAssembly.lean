module
public import RequestProject.AppendixE.PhysicalConcatenation

/-!
# Finite face-block assembly

A `FaceBlock` is a supplied physical segment whose two endpoints lie
on the zero-cost face `F`.  Constant sector phases align a block's
initial endpoint to a prescribed face state without changing its
control, duration, exposure, or conditional-phase ratio
(`zObs terminal / zObs initial`).  Concatenating aligned blocks gives
an automatic finite assembly: duration and exposure are the exact
sums and the endpoint phase ratio is the exact product of the input
ratios, by the `zObs` telescope (all intermediate `zObs` are nonzero
on `F`, no supplied nonzero hypotheses).

The empty list uses a new zero-duration segment with control `1`
(`PhysicalSegment.unitZero`), which is required for unit-modulus
control at its singleton interval.

If all supplied blocks have unit-modulus controls and their phase
ratios multiply to `−1`, assembly from `x0` yields a `Pulse` with
exact CZ closure and exposure equal to the sum.  These hypotheses
stay explicit: nothing here produces the face-to-face blocks from
the retained excursions.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A supplied physical segment with both endpoints on the face `F`. -/
structure FaceBlock where
  segment : PhysicalSegment
  initial_face : segment.path 0 ∈ Fface
  terminal_face : segment.path segment.duration ∈ Fface

namespace FaceBlock

/-- The initial endpoint of a face block. -/
def initial (B : FaceBlock) : State := B.segment.path 0

/-- The terminal endpoint of a face block. -/
def terminal (B : FaceBlock) : State := B.segment.path B.segment.duration

/-- The conditional-phase ratio `zObs(terminal) / zObs(initial)`. -/
def phaseRatio (B : FaceBlock) : ℂ := zObs B.terminal / zObs B.initial

/-! ## The empty (zero-duration) block -/

/-- The zero-duration face block at `p`, with unit control. -/
def unitZero (p : State) (hp : p ∈ Fface) : FaceBlock where
  segment := PhysicalSegment.unitZero p hp.1
  initial_face := hp
  terminal_face := hp

@[simp] theorem unitZero_initial (p : State) (hp : p ∈ Fface) :
    (unitZero p hp).initial = p := rfl

@[simp] theorem unitZero_terminal (p : State) (hp : p ∈ Fface) :
    (unitZero p hp).terminal = p := rfl

@[simp] theorem unitZero_duration (p : State) (hp : p ∈ Fface) :
    (unitZero p hp).segment.duration = 0 := rfl

@[simp] theorem unitZero_exposure (p : State) (hp : p ∈ Fface) :
    (unitZero p hp).segment.exposure = 0 :=
  PhysicalSegment.unitZero_exposure p hp.1

theorem unitZero_phaseRatio (p : State) (hp : p ∈ Fface) :
    (unitZero p hp).phaseRatio = 1 := by
  show zObs (unitZero p hp).terminal / zObs (unitZero p hp).initial = 1
  rw [unitZero_terminal, unitZero_initial]
  exact div_self (norm_ne_zero_iff.mp (by
    rw [norm_zObs_of_mem_Fface hp]; norm_num))

theorem unitZero_unit (p : State) (hp : p ∈ Fface) :
    (unitZero p hp).segment.UnitControl :=
  PhysicalSegment.unitZero_unit p hp.1

/-! ## Alignment by constant sector phases -/

/-- Realign a block so that its initial endpoint is the prescribed
face state `p`; the sector phase comes from `faceAlign`. -/
def align (B : FaceBlock) (p : State) (hp : p ∈ Fface) : FaceBlock where
  segment := B.segment.rephase (g1 p / g1 B.initial) (g2 p / g2 B.initial)
    (faceAlign_unit B.initial_face hp).1 (faceAlign_unit B.initial_face hp).2
  initial_face := by
    show faceAlign (B.segment.path 0) p (B.segment.path 0) ∈ Fface
    rw [faceAlign_source B.initial_face hp]
    exact hp
  terminal_face := by
    show (B.segment.rephase _ _ _ _).path
        (B.segment.rephase _ _ _ _).duration ∈ Fface
    rw [PhysicalSegment.rephase_duration, PhysicalSegment.rephase_path]
    exact sectorPhase_mem_Fface
      (faceAlign_unit B.initial_face hp).1
      (faceAlign_unit B.initial_face hp).2 B.terminal_face

@[simp] theorem align_initial (B : FaceBlock) (p : State) (hp : p ∈ Fface) :
    (B.align p hp).initial = p :=
  faceAlign_source B.initial_face hp

@[simp] theorem align_terminal (B : FaceBlock) (p : State) (hp : p ∈ Fface) :
    (B.align p hp).terminal = faceAlign B.initial p B.terminal := rfl

@[simp] theorem align_duration (B : FaceBlock) (p : State) (hp : p ∈ Fface) :
    (B.align p hp).segment.duration = B.segment.duration := rfl

@[simp] theorem align_exposure (B : FaceBlock) (p : State) (hp : p ∈ Fface) :
    (B.align p hp).segment.exposure = B.segment.exposure :=
  PhysicalSegment.rephase_exposure B.segment
    (g1 p / g1 B.initial) (g2 p / g2 B.initial)
    (faceAlign_unit B.initial_face hp).1 (faceAlign_unit B.initial_face hp).2

@[simp] theorem align_phaseRatio (B : FaceBlock) (p : State) (hp : p ∈ Fface) :
    (B.align p hp).phaseRatio = B.phaseRatio := by
  show zObs (B.align p hp).terminal / zObs (B.align p hp).initial = _
  rw [align_terminal, align_initial]
  exact faceAlign_zObs_ratio B.initial_face hp B.terminal

theorem align_unit (B : FaceBlock) (p : State) (hp : p ∈ Fface)
    (hu : B.segment.UnitControl) : (B.align p hp).segment.UnitControl := by
  intro s hs
  rw [align_duration] at hs
  have e : (B.align p hp).segment.control = B.segment.control := rfl
  rw [e]
  exact hu s hs

/-! ## Concatenation of face blocks -/

/-- Concatenation of two face blocks whose endpoints match. -/
def concat (P Q : FaceBlock) (hmatch : P.terminal = Q.initial) : FaceBlock where
  segment := P.segment.concat Q.segment hmatch
  initial_face := by
    show (P.segment.concat Q.segment hmatch).path 0 ∈ Fface
    rw [PhysicalSegment.concat_initial]
    exact P.initial_face
  terminal_face := by
    show (P.segment.concat Q.segment hmatch).path
        (P.segment.concat Q.segment hmatch).duration ∈ Fface
    rw [PhysicalSegment.concat_duration, PhysicalSegment.concat_terminal]
    exact Q.terminal_face

@[simp] theorem concat_initial (P Q : FaceBlock)
    (hmatch : P.terminal = Q.initial) :
    (P.concat Q hmatch).initial = P.initial :=
  PhysicalSegment.concat_initial P.segment Q.segment hmatch

@[simp] theorem concat_terminal (P Q : FaceBlock)
    (hmatch : P.terminal = Q.initial) :
    (P.concat Q hmatch).terminal = Q.terminal := by
  show (P.segment.concat Q.segment hmatch).path
      (P.segment.concat Q.segment hmatch).duration = Q.terminal
  rw [PhysicalSegment.concat_duration]
  exact PhysicalSegment.concat_terminal P.segment Q.segment hmatch

@[simp] theorem concat_duration (P Q : FaceBlock)
    (hmatch : P.terminal = Q.initial) :
    (P.concat Q hmatch).segment.duration =
      P.segment.duration + Q.segment.duration := rfl

@[simp] theorem concat_exposure (P Q : FaceBlock)
    (hmatch : P.terminal = Q.initial) :
    (P.concat Q hmatch).segment.exposure =
      P.segment.exposure + Q.segment.exposure :=
  PhysicalSegment.concat_exposure P.segment Q.segment hmatch

/-- The phase ratios telescope: the middle `zObs` is nonzero on `F`. -/
@[simp] theorem concat_phaseRatio (P Q : FaceBlock)
    (hmatch : P.terminal = Q.initial) :
    (P.concat Q hmatch).phaseRatio = P.phaseRatio * Q.phaseRatio := by
  show zObs (P.concat Q hmatch).terminal /
      zObs (P.concat Q hmatch).initial = _
  rw [concat_terminal, concat_initial]
  show zObs Q.terminal / zObs P.initial =
    (zObs P.terminal / zObs P.initial) *
      (zObs Q.terminal / zObs Q.initial)
  rw [← hmatch]
  have hzT : zObs P.terminal ≠ 0 := norm_ne_zero_iff.mp (by
    show ‖zObs (P.segment.path P.segment.duration)‖ ≠ 0
    rw [norm_zObs_of_mem_Fface P.terminal_face]; norm_num)
  have hzI : zObs P.initial ≠ 0 := norm_ne_zero_iff.mp (by
    show ‖zObs (P.segment.path 0)‖ ≠ 0
    rw [norm_zObs_of_mem_Fface P.initial_face]; norm_num)
  field_simp

theorem concat_unit (P Q : FaceBlock) (hmatch : P.terminal = Q.initial)
    (huP : P.segment.UnitControl) (huQ : Q.segment.UnitControl) :
    (P.concat Q hmatch).segment.UnitControl :=
  PhysicalSegment.concat_unit P.segment Q.segment hmatch huP huQ

/-! ## Automatic aligned concatenation -/

/-- Concatenate after aligning `Q` to `P`'s terminal state. -/
def appendAligned (P Q : FaceBlock) : FaceBlock :=
  P.concat (Q.align P.terminal P.terminal_face)
    (align_initial Q P.terminal P.terminal_face).symm

@[simp] theorem appendAligned_initial (P Q : FaceBlock) :
    (P.appendAligned Q).initial = P.initial :=
  concat_initial P _ _

@[simp] theorem appendAligned_duration (P Q : FaceBlock) :
    (P.appendAligned Q).segment.duration =
      P.segment.duration + Q.segment.duration := by
  show (P.concat (Q.align P.terminal P.terminal_face) _).segment.duration = _
  rw [concat_duration, align_duration]

@[simp] theorem appendAligned_exposure (P Q : FaceBlock) :
    (P.appendAligned Q).segment.exposure =
      P.segment.exposure + Q.segment.exposure := by
  show (P.concat (Q.align P.terminal P.terminal_face) _).segment.exposure = _
  rw [concat_exposure, align_exposure]

@[simp] theorem appendAligned_phaseRatio (P Q : FaceBlock) :
    (P.appendAligned Q).phaseRatio = P.phaseRatio * Q.phaseRatio := by
  show (P.concat (Q.align P.terminal P.terminal_face) _).phaseRatio = _
  rw [concat_phaseRatio, align_phaseRatio]

theorem appendAligned_unit (P Q : FaceBlock) (huP : P.segment.UnitControl)
    (huQ : Q.segment.UnitControl) :
    (P.appendAligned Q).segment.UnitControl :=
  concat_unit P _ _ huP (align_unit Q P.terminal P.terminal_face huQ)

/-! ## Finite assembly -/

/-- Left-folded aligned concatenation of a list of face blocks. -/
def chainFrom : FaceBlock → List FaceBlock → FaceBlock
  | P, [] => P
  | P, Q :: Qs => chainFrom (P.appendAligned Q) Qs

theorem chainFrom_initial (P : FaceBlock) (blocks : List FaceBlock) :
    (chainFrom P blocks).initial = P.initial := by
  induction blocks generalizing P with
  | nil => rfl
  | cons Q Qs ih =>
      show (chainFrom (P.appendAligned Q) Qs).initial = P.initial
      rw [ih (P.appendAligned Q), appendAligned_initial]

theorem chainFrom_duration (P : FaceBlock) (blocks : List FaceBlock) :
    (chainFrom P blocks).segment.duration =
      P.segment.duration +
        (blocks.map (fun B => B.segment.duration)).sum := by
  induction blocks generalizing P with
  | nil => simp [chainFrom]
  | cons Q Qs ih =>
      show (chainFrom (P.appendAligned Q) Qs).segment.duration = _
      rw [ih (P.appendAligned Q), appendAligned_duration,
        List.map_cons, List.sum_cons, add_assoc]

theorem chainFrom_exposure (P : FaceBlock) (blocks : List FaceBlock) :
    (chainFrom P blocks).segment.exposure =
      P.segment.exposure +
        (blocks.map (fun B => B.segment.exposure)).sum := by
  induction blocks generalizing P with
  | nil => simp [chainFrom]
  | cons Q Qs ih =>
      show (chainFrom (P.appendAligned Q) Qs).segment.exposure = _
      rw [ih (P.appendAligned Q), appendAligned_exposure,
        List.map_cons, List.sum_cons, add_assoc]

theorem chainFrom_phaseRatio (P : FaceBlock) (blocks : List FaceBlock) :
    (chainFrom P blocks).phaseRatio =
      P.phaseRatio * (blocks.map phaseRatio).prod := by
  induction blocks generalizing P with
  | nil => simp [chainFrom]
  | cons Q Qs ih =>
      show (chainFrom (P.appendAligned Q) Qs).phaseRatio = _
      rw [ih (P.appendAligned Q), appendAligned_phaseRatio,
        List.map_cons, List.prod_cons, mul_assoc]

theorem chainFrom_unit (P : FaceBlock) (blocks : List FaceBlock)
    (huP : P.segment.UnitControl)
    (hus : ∀ B ∈ blocks, B.segment.UnitControl) :
    (chainFrom P blocks).segment.UnitControl := by
  induction blocks generalizing P with
  | nil => exact huP
  | cons Q Qs ih =>
      show (chainFrom (P.appendAligned Q) Qs).segment.UnitControl
      exact ih (P.appendAligned Q)
        (appendAligned_unit P Q huP (hus Q List.mem_cons_self))
        (fun B hB => hus B (List.mem_cons_of_mem Q hB))

/-- Assembly of `blocks` starting from the prescribed face state `p`
via the zero-duration unit block. -/
def assemble (p : State) (hp : p ∈ Fface) (blocks : List FaceBlock) :
    FaceBlock :=
  chainFrom (unitZero p hp) blocks

@[simp] theorem assemble_initial (p : State) (hp : p ∈ Fface)
    (blocks : List FaceBlock) : (assemble p hp blocks).initial = p := by
  show (chainFrom (unitZero p hp) blocks).initial = p
  rw [chainFrom_initial, unitZero_initial]

theorem assemble_duration (p : State) (hp : p ∈ Fface)
    (blocks : List FaceBlock) :
    (assemble p hp blocks).segment.duration =
      (blocks.map (fun B => B.segment.duration)).sum := by
  show (chainFrom (unitZero p hp) blocks).segment.duration = _
  rw [chainFrom_duration, unitZero_duration, zero_add]

theorem assemble_exposure (p : State) (hp : p ∈ Fface)
    (blocks : List FaceBlock) :
    (assemble p hp blocks).segment.exposure =
      (blocks.map (fun B => B.segment.exposure)).sum := by
  show (chainFrom (unitZero p hp) blocks).segment.exposure = _
  rw [chainFrom_exposure, unitZero_exposure, zero_add]

theorem assemble_phaseRatio (p : State) (hp : p ∈ Fface)
    (blocks : List FaceBlock) :
    (assemble p hp blocks).phaseRatio = (blocks.map phaseRatio).prod := by
  show (chainFrom (unitZero p hp) blocks).phaseRatio = _
  rw [chainFrom_phaseRatio, unitZero_phaseRatio, one_mul]

theorem assemble_unit (p : State) (hp : p ∈ Fface)
    (blocks : List FaceBlock)
    (hus : ∀ B ∈ blocks, B.segment.UnitControl) :
    (assemble p hp blocks).segment.UnitControl := by
  show (chainFrom (unitZero p hp) blocks).segment.UnitControl
  exact chainFrom_unit (unitZero p hp) blocks (unitZero_unit p hp) hus

/-! ## Conditional pulse wrapper -/

/-- The initial state lies on the face `F`. -/
theorem x0_mem_Fface : x0 ∈ Fface := by
  have hmk : x0 = mkState 1 0 1 0 := rfl
  rw [hmk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp

/-- If the supplied phase ratios multiply to `−1`, the assembled
terminal state lies on the exact-CZ orbit `XCZ`. -/
theorem assemble_terminal_mem_XCZ (blocks : List FaceBlock)
    (hphase : (blocks.map phaseRatio).prod = -1) :
    (assemble x0 x0_mem_Fface blocks).terminal ∈ XCZ := by
  have hT : (assemble x0 x0_mem_Fface blocks).terminal ∈ Fface :=
    (assemble x0 x0_mem_Fface blocks).terminal_face
  rw [mem_XCZ_iff_zObs_eq_neg_one hT]
  have hr := assemble_phaseRatio x0 x0_mem_Fface blocks
  rw [hphase] at hr
  have hz0 : zObs (assemble x0 x0_mem_Fface blocks).initial = 1 := by
    rw [assemble_initial]
    have e : x0 = mkState 1 0 1 0 := rfl
    rw [e]
    simp [zObs]
  have hph : (assemble x0 x0_mem_Fface blocks).phaseRatio =
      zObs (assemble x0 x0_mem_Fface blocks).terminal := by
    show zObs _ / zObs _ = zObs _
    rw [hz0, div_one]
  rw [hph] at hr
  exact hr

/-- The assembled `Pulse`, conditional on unit controls and phase
product `−1`; neither hypothesis is asserted here. -/
def assemblePulse (blocks : List FaceBlock)
    (hus : ∀ B ∈ blocks, B.segment.UnitControl)
    (hphase : (blocks.map phaseRatio).prod = -1) : Pulse :=
  (assemble x0 x0_mem_Fface blocks).segment.toPulse
    (assemble_unit x0 x0_mem_Fface blocks hus)
    (assemble_initial x0 x0_mem_Fface blocks)
    (assemble_terminal_mem_XCZ blocks hphase)

theorem assemblePulse_exposure (blocks : List FaceBlock)
    (hus : ∀ B ∈ blocks, B.segment.UnitControl)
    (hphase : (blocks.map phaseRatio).prod = -1) :
    (assemblePulse blocks hus hphase).exposure =
      (blocks.map (fun B => B.segment.exposure)).sum := by
  show ((assemble x0 x0_mem_Fface blocks).segment.toPulse _ _ _).exposure = _
  rw [PhysicalSegment.toPulse_exposure]
  exact assemble_exposure x0 x0_mem_Fface blocks

end FaceBlock

end CZExposure
