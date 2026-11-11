module
public import RequestProject.AppendixE.ShortPulse

/-! Chronological pulse words in ±X and ±Y. Every word is realized as
a unit-control integral trajectory, with exact endpoints and duration.
The six fixed words below are not yet a quantitative steering theorem. -/
@[expose] public section
noncomputable section
namespace CZExposure.PulseWords
open ControlTranslation PhysicalSegment

/-- First bit: Y instead of X. Second bit: negative signed time. -/
abbrev Letter := Bool × Bool
abbrev Word := List Letter

def phase (l : Letter) : ℂ := if l.1 then Complex.I else 1
def time (l : Letter) (t : ℝ) : ℝ := if l.2 then -t else t
def flip (l : Letter) : Letter := (l.1, !l.2)
def inv (w : Word) : Word := w.reverse.map flip

theorem phase_unit (l : Letter) : ‖phase l‖ = 1 := by
  simp only [phase]; split <;> simp

def step (l : Letter) (t : ℝ) (x : State) (hx : x ∈ Xset) : PhysicalSegment :=
  segment x hx (ShortPulse.signed (phase l) (phase_unit l) (time l t))

@[simp] theorem step_initial (l : Letter) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (step l t x hx).path 0 = x := by
  simp [step, ControlTranslation.segment]

@[simp] theorem step_terminal (l : Letter) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (step l t x hx).path (step l t x hx).duration =
      translate x (ShortPulse.orbit (phase l) (time l t)) := by
  change translate x ((ShortPulse.signed (phase l) (phase_unit l) (time l t)).path
    (ShortPulse.signed (phase l) (phase_unit l) (time l t)).duration) = _
  rw [ShortPulse.signed_terminal]

@[simp] theorem step_duration (l : Letter) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (step l t x hx).duration = |t| := by
  simp only [step, segment_duration, ShortPulse.signed_duration, time]
  split <;> simp

theorem step_unit (l : Letter) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (step l t x hx).UnitControl := ShortPulse.signed_unit _ _ _

/-- Explicit endpoint calculation, with letters read in physical time order. -/
def endpoint : Word → ℝ → State → State
  | [], _, x => x
  | l :: w, t, x => endpoint w t (translate x (ShortPulse.orbit (phase l) (time l t)))

/-- Finite concatenation at the level of physical integral paths.
The subtype records the initial endpoint needed at each join. -/
def run : (w : Word) → (t : ℝ) → (x : State) → x ∈ Xset →
    {P : PhysicalSegment // P.path 0 = x}
  | [], _, x, hx => ⟨unitZero x hx, rfl⟩
  | l :: w, t, x, hx =>
    let P := step l t x hx
    let Q := run w t (P.path P.duration)
      (P.path_mem _ (Set.right_mem_Icc.mpr P.duration_nonneg))
    ⟨P.concat Q.val Q.property.symm, by simp [P]⟩

theorem run_terminal (w : Word) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (run w t x hx).val.path (run w t x hx).val.duration = endpoint w t x := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    simp only [run, concat_duration, concat_terminal, ih, step_terminal, endpoint]

theorem run_duration (w : Word) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (run w t x hx).val.duration = w.length * |t| := by
  induction w generalizing x with
  | nil => simp [run]
  | cons l w ih =>
    simp only [run, concat_duration, step_duration, ih, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    ring

theorem run_unit (w : Word) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (run w t x hx).val.UnitControl := by
  induction w generalizing x with
  | nil => exact unitZero_unit x hx
  | cons l w ih =>
    unfold run
    apply concat_unit
    · exact (run w t _ _).property.symm
    · exact step_unit l t x hx
    · exact ih _ _

theorem endpoint_append (u v : Word) (t : ℝ) (x : State) :
    endpoint (u ++ v) t x = endpoint v t (endpoint u t x) := by
  induction u generalizing x with
  | nil => rfl
  | cons l u ih => exact ih _

theorem flip_cancel (l : Letter) (t : ℝ) (x : State) :
    endpoint [flip l] t (endpoint [l] t x) = x := by
  have ht : time (flip l) t = -time l t := by
    rcases l with ⟨a, b⟩
    cases b <;> simp [flip, time]
  simp only [endpoint, show phase (flip l) = phase l from rfl, ht,
    ShortPulse.orbit_inverse]
  exact left_inverse_cancel (ShortPulse.orbit_mem (phase_unit l) _) x

theorem inv_cons (l : Letter) (w : Word) : inv (l :: w) = inv w ++ [flip l] := by
  simp [inv]

/-- Reversing the list and negating every signed pulse is an exact inverse,
not just cancellation to leading order near zero. -/
theorem endpoint_inv (w : Word) (t : ℝ) (x : State) :
    endpoint (inv w) t (endpoint w t x) = x := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    rw [inv_cons, endpoint_append]
    change endpoint [flip l] t
      (endpoint (inv w) t (endpoint w t (endpoint [l] t x))) = x
    rw [ih, flip_cancel]

theorem run_round_trip (w : Word) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (run (w ++ inv w) t x hx).val.path (run (w ++ inv w) t x hx).val.duration = x := by
  rw [run_terminal, endpoint_append, endpoint_inv]

theorem endpoint_zero (w : Word) (x : State) : endpoint w 0 x = x := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    have ht : time l 0 = 0 := by simp only [time]; split <;> simp
    simp only [endpoint, ht, ShortPulse.orbit_zero, translate_origin, ih]

/-- Chronological U,V,U⁻¹,V⁻¹ yields the operator product V⁻¹U⁻¹VU. -/
def commutator (u v : Word) : Word := u ++ v ++ inv u ++ inv v

theorem commutator_endpoint (u v : Word) (t : ℝ) (x : State) :
    endpoint (commutator u v) t x =
      endpoint (inv v) t (endpoint (inv u) t (endpoint v t (endpoint u t x))) := by
  simp only [commutator, endpoint_append]

def X : Word := [(false, false)]
def Y : Word := [(true, false)]
def W2 : Word := commutator X Y
def W3X : Word := commutator Y W2
def W3Y : Word := commutator W2 X
def W4 : Word := commutator X W3Y

/-- Same ordering as `ControlLie.bracketFields`; `PulseExpansion` proves
the orders and the leading-field identities for these actual words. -/
def six : Fin 6 → Word := ![X, Y, W2, W3X, W3Y, W4]

theorem six_lengths : (fun i => (six i).length) = ![1, 1, 4, 10, 10, 22] := by
  decide

theorem six_duration (i : Fin 6) (t : ℝ) (x : State) (hx : x ∈ Xset) :
    (run (six i) t x hx).val.duration =
      (![1, 1, 4, 10, 10, 22] i : ℝ) * |t| := by
  rw [run_duration, congrFun six_lengths i]
  fin_cases i <;> norm_num

end CZExposure.PulseWords
