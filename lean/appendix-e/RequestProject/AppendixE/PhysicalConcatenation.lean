module
public import RequestProject.AppendixE.PhysicalSegment

/-!
# Physical concatenation

Concatenation of supplied physical segments with matching endpoints.
The spliced trajectory uses the first segment on `t ≤ P.duration` and
the second, shifted, afterwards.  Matching endpoint states give a
segment satisfying the integral equation at *every* time, including
the join itself and duration zero; the control may jump at the join
(the first segment's control is used there) and no equality of
endpoint controls is assumed.

Durations and exposures add exactly.  A `UnitControl` predicate
records unit-modulus control on the closed interval, and `unitZero`
supplies a zero-duration unit segment (the existing `zero` segment
has control `0` and cannot serve).  Concatenation preserves
`UnitControl` when both inputs have it.

All statements are conditional on supplied segments: nothing here
constructs endpoint steering.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PhysicalSegment

open MeasureTheory Set
open scoped NNReal ENNReal

/-! ## The generic splice and its integrals -/

namespace Concatenation

/-- Time splice: `f` up to time `a` (inclusive), then `g` shifted. -/
def splice {E : Type*} (a : ℝ) (f g : ℝ → E) (t : ℝ) : E :=
  if t ≤ a then f t else g (t - a)

private theorem intervalIntegrable_splice_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ} (ha : 0 ≤ a)
    {f g : ℝ → E} (hf : IntervalIntegrable f volume 0 a) :
    IntervalIntegrable (splice a f g) volume 0 a := by
  refine (intervalIntegrable_congr ?_).mpr hf
  intro t ht
  rw [Set.uIoc_of_le ha] at ht
  exact if_pos ht.2

private theorem intervalIntegrable_splice_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hb : 0 ≤ b)
    {f g : ℝ → E} (hg : IntervalIntegrable g volume 0 b) :
    IntervalIntegrable (splice a f g) volume a (a + b) := by
  have hg' : IntervalIntegrable (fun t => g (t - a)) volume a (a + b) := by
    have h := hg.comp_sub_right a
    rwa [zero_add, add_comm b a] at h
  refine (intervalIntegrable_congr ?_).mpr hg'
  intro t ht
  rw [Set.uIoc_of_le (by linarith : a ≤ a + b)] at ht
  exact if_neg (not_le.mpr ht.1)

/-- The splice of interval-integrable functions is integrable on the
whole joined interval. -/
theorem intervalIntegrable_splice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {f g : ℝ → E}
    (hf : IntervalIntegrable f volume 0 a)
    (hg : IntervalIntegrable g volume 0 b) :
    IntervalIntegrable (splice a f g) volume 0 (a + b) :=
  (intervalIntegrable_splice_left (f := f) (g := g) ha hf).trans
    (intervalIntegrable_splice_right (a := a) (f := f) (g := g) hb hg)

/-- The integral of a splice is the sum of the two pieces.  On the
right piece the seam point is excluded (`uIoc`), so no endpoint
matching of `f` and `g` is needed. -/
theorem integral_splice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {f g : ℝ → E}
    (hf : IntervalIntegrable f volume 0 a)
    (hg : IntervalIntegrable g volume 0 b) :
    (∫ t in (0:ℝ)..(a+b), splice a f g t) =
      (∫ t in (0:ℝ)..a, f t) + ∫ t in (0:ℝ)..b, g t := by
  have h0a := intervalIntegrable_splice_left (f := f) (g := g) ha hf
  have hab := intervalIntegrable_splice_right (a := a) (f := f) (g := g) hb hg
  rw [← intervalIntegral.integral_add_adjacent_intervals h0a hab]
  congr 1
  · exact intervalIntegral.integral_congr
      (fun t ht => if_pos ((Set.uIcc_of_le ha ▸ ht).2))
  · show (∫ t in a..(a+b), (if t ≤ a then f t else g (t - a))) =
        ∫ t in (0:ℝ)..b, g t
    rw [intervalIntegral.integral_congr_ae
        (Filter.Eventually.of_forall fun t ht =>
          if_neg (not_le.mpr ((Set.uIoc_of_le
            (by linarith : a ≤ a + b) ▸ ht).1))),
      intervalIntegral.integral_comp_sub_right, sub_self]
    rw [show a + b - a = b from by ring]

end Concatenation

/-! ## Unit control and the unit zero segment -/

/-- The control has unit modulus on the whole closed interval. -/
def UnitControl (P : PhysicalSegment) : Prop :=
  ∀ s ∈ Set.Icc 0 P.duration, ‖P.control s‖ = 1

/-- The zero-duration segment with control `1`, used as the empty
assembly.  Unlike `PhysicalSegment.zero` it satisfies
`UnitControl` on its (singleton) interval. -/
def unitZero (x : State) (hx : x ∈ Xset) : PhysicalSegment where
  duration := 0
  duration_nonneg := le_rfl
  path := fun _ => x
  control := fun _ => 1
  control_measurable := measurable_const
  control_bound := fun _ _ => le_of_eq norm_one
  path_mem := fun _ _ => hx
  velocity_integrable := IntervalIntegrable.refl
  integralEquation := fun s hs => by
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    simp

@[simp] theorem unitZero_duration (x : State) (hx : x ∈ Xset) :
    (unitZero x hx).duration = 0 := rfl

@[simp] theorem unitZero_path (x : State) (hx : x ∈ Xset) (s : ℝ) :
    (unitZero x hx).path s = x := rfl

@[simp] theorem unitZero_exposure (x : State) (hx : x ∈ Xset) :
    (unitZero x hx).exposure = 0 := by
  simp [PhysicalSegment.exposure]

theorem unitZero_unit (x : State) (hx : x ∈ Xset) :
    (unitZero x hx).UnitControl := fun _ _ => norm_one

/-! ## Concatenation of matching segments -/

/-- Concatenation of two segments whose endpoints match:
`P` on `t ≤ P.duration`, then `Q` shifted. -/
def concat (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) : PhysicalSegment where
  duration := P.duration + Q.duration
  duration_nonneg := add_nonneg P.duration_nonneg Q.duration_nonneg
  path := Concatenation.splice P.duration P.path Q.path
  control := Concatenation.splice P.duration P.control Q.control
  control_measurable := by
    show Measurable fun t =>
      if t ≤ P.duration then P.control t else Q.control (t - P.duration)
    exact Measurable.ite measurableSet_Iic P.control_measurable
      (Q.control_measurable.comp (measurable_id.sub measurable_const))
  control_bound := fun s hs => by
    by_cases hsP : s ≤ P.duration
    · rw [show Concatenation.splice P.duration P.control Q.control s =
          P.control s from if_pos hsP]
      exact P.control_bound s ⟨hs.1, hsP⟩
    · push_neg at hsP
      rw [show Concatenation.splice P.duration P.control Q.control s =
          Q.control (s - P.duration) from if_neg (not_le.mpr hsP)]
      exact Q.control_bound _
        ⟨sub_nonneg.mpr hsP.le, by linarith [hs.2]⟩
  path_mem := fun s hs => by
    by_cases hsP : s ≤ P.duration
    · rw [show Concatenation.splice P.duration P.path Q.path s =
          P.path s from if_pos hsP]
      exact P.path_mem s ⟨hs.1, hsP⟩
    · push_neg at hsP
      rw [show Concatenation.splice P.duration P.path Q.path s =
          Q.path (s - P.duration) from if_neg (not_le.mpr hsP)]
      exact Q.path_mem _
        ⟨sub_nonneg.mpr hsP.le, by linarith [hs.2]⟩
  velocity_integrable := by
    have heq : (fun s => vf (Concatenation.splice P.duration P.path
          Q.path s) (Concatenation.splice P.duration P.control
          Q.control s)) =
        Concatenation.splice P.duration
          (fun s => vf (P.path s) (P.control s))
          (fun s => vf (Q.path s) (Q.control s)) := by
      funext s
      show vf (if s ≤ P.duration then P.path s
          else Q.path (s - P.duration))
        (if s ≤ P.duration then P.control s
          else Q.control (s - P.duration)) =
        if s ≤ P.duration then vf (P.path s) (P.control s)
          else vf (Q.path (s - P.duration)) (Q.control (s - P.duration))
      split_ifs <;> rfl
    rw [heq]
    exact Concatenation.intervalIntegrable_splice P.duration_nonneg
      Q.duration_nonneg P.velocity_integrable Q.velocity_integrable
  integralEquation := by
    intro s hs
    by_cases hsP : s ≤ P.duration
    · have h0 : Concatenation.splice P.duration P.path Q.path 0 =
          P.path 0 := if_pos P.duration_nonneg
      have hsr : Concatenation.splice P.duration P.path Q.path s =
          P.path s := if_pos hsP
      rw [hsr, h0]
      have hcong : (∫ r in (0:ℝ)..s,
            vf (Concatenation.splice P.duration P.path Q.path r)
              (Concatenation.splice P.duration P.control Q.control r)) =
          ∫ r in (0:ℝ)..s, vf (P.path r) (P.control r) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hs.1] at ht
        show vf (if t ≤ P.duration then P.path t
            else Q.path (t - P.duration))
          (if t ≤ P.duration then P.control t
            else Q.control (t - P.duration)) =
          vf (P.path t) (P.control t)
        rw [if_pos (le_trans ht.2 hsP), if_pos (le_trans ht.2 hsP)]
      rw [hcong]
      exact P.integralEquation s ⟨hs.1, hsP⟩
    · push_neg at hsP
      have hts : s - P.duration ∈ Set.Icc 0 Q.duration :=
        ⟨sub_nonneg.mpr hsP.le, by linarith [hs.2]⟩
      have h0 : Concatenation.splice P.duration P.path Q.path 0 =
          P.path 0 := if_pos P.duration_nonneg
      have hsr : Concatenation.splice P.duration P.path Q.path s =
          Q.path (s - P.duration) := if_neg (not_le.mpr hsP)
      rw [hsr, h0]
      have heq : (fun r => vf (Concatenation.splice P.duration P.path
            Q.path r) (Concatenation.splice P.duration P.control
            Q.control r)) =
          Concatenation.splice P.duration
            (fun r => vf (P.path r) (P.control r))
            (fun r => vf (Q.path r) (Q.control r)) := by
        funext r
        show vf (if r ≤ P.duration then P.path r
            else Q.path (r - P.duration))
          (if r ≤ P.duration then P.control r
            else Q.control (r - P.duration)) =
          if r ≤ P.duration then vf (P.path r) (P.control r)
            else vf (Q.path (r - P.duration)) (Q.control (r - P.duration))
        split_ifs <;> rfl
      rw [heq]
      have hInt := Concatenation.integral_splice P.duration_nonneg
        (sub_nonneg.mpr hsP.le) P.velocity_integrable
        (Q.velocity_integrable_subinterval
          (Set.left_mem_Icc.mpr Q.duration_nonneg) hts)
      rw [show P.duration + (s - P.duration) = s from by ring] at hInt
      rw [hInt, Q.integralEquation (s - P.duration) hts, ← hmatch,
        P.integralEquation P.duration
          (Set.right_mem_Icc.mpr P.duration_nonneg)]
      abel

@[simp] theorem concat_duration (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) :
    (P.concat Q hmatch).duration = P.duration + Q.duration := rfl

@[simp] theorem concat_initial (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) :
    (P.concat Q hmatch).path 0 = P.path 0 := if_pos P.duration_nonneg

@[simp] theorem concat_terminal (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) :
    (P.concat Q hmatch).path (P.duration + Q.duration) =
      Q.path Q.duration := by
  by_cases hQ : Q.duration ≤ 0
  · have hQ0 : Q.duration = 0 := le_antisymm hQ Q.duration_nonneg
    rw [hQ0, add_zero]
    show Concatenation.splice P.duration P.path Q.path P.duration =
      Q.path 0
    rw [show Concatenation.splice P.duration P.path Q.path P.duration =
        P.path P.duration from if_pos le_rfl, hmatch]
  · push_neg at hQ
    have e : (P.concat Q hmatch).path (P.duration + Q.duration) =
        Q.path (P.duration + Q.duration - P.duration) :=
      if_neg (not_le.mpr (by linarith))
    rw [e, add_sub_cancel_left]

theorem concat_path_left (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) {s : ℝ}
    (hs : s ≤ P.duration) :
    (P.concat Q hmatch).path s = P.path s := if_pos hs

theorem concat_path_right (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) {s : ℝ}
    (hs : P.duration ≤ s) :
    (P.concat Q hmatch).path s = Q.path (s - P.duration) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    show Concatenation.splice P.duration P.path Q.path P.duration =
      Q.path (P.duration - P.duration)
    rw [show Concatenation.splice P.duration P.path Q.path P.duration =
        P.path P.duration from if_pos le_rfl, sub_self]
    exact hmatch
  · exact if_neg (not_le.mpr h)

theorem concat_control_left (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) {s : ℝ}
    (hs : s ≤ P.duration) :
    (P.concat Q hmatch).control s = P.control s := if_pos hs

theorem concat_control_right (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) {s : ℝ}
    (hs : P.duration < s) :
    (P.concat Q hmatch).control s = Q.control (s - P.duration) :=
  if_neg (not_le.mpr hs)

@[simp] theorem concat_exposure (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0) :
    (P.concat Q hmatch).exposure = P.exposure + Q.exposure := by
  show (∫ s in (0:ℝ)..(P.duration + Q.duration),
      cost (Concatenation.splice P.duration P.path Q.path s)) =
    (∫ s in (0:ℝ)..P.duration, cost (P.path s)) +
      ∫ s in (0:ℝ)..Q.duration, cost (Q.path s)
  have heq : (fun s => cost (Concatenation.splice P.duration P.path
        Q.path s)) =
      Concatenation.splice P.duration (fun s => cost (P.path s))
        (fun s => cost (Q.path s)) := by
    funext s
    show cost (if s ≤ P.duration then P.path s
        else Q.path (s - P.duration)) =
      if s ≤ P.duration then cost (P.path s)
        else cost (Q.path (s - P.duration))
    split_ifs <;> rfl
  rw [heq]
  exact Concatenation.integral_splice P.duration_nonneg Q.duration_nonneg
    P.cost_intervalIntegrable Q.cost_intervalIntegrable

theorem concat_unit (P Q : PhysicalSegment)
    (hmatch : P.path P.duration = Q.path 0)
    (hP : P.UnitControl) (hQ : Q.UnitControl) :
    (P.concat Q hmatch).UnitControl := by
  intro s hs
  rw [concat_duration] at hs
  by_cases hsP : s ≤ P.duration
  · rw [concat_control_left P Q hmatch hsP]
    exact hP s ⟨hs.1, hsP⟩
  · push_neg at hsP
    rw [concat_control_right P Q hmatch hsP]
    exact hQ (s - P.duration)
      ⟨sub_nonneg.mpr hsP.le, by linarith [hs.2]⟩

end CZExposure.PhysicalSegment
