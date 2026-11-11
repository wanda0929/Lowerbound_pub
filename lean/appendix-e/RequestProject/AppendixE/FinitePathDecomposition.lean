module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Logic.Relation
public import Mathlib.Tactic

/-! Finite path routing on a directed acyclic graph. The finite combinatorial
statement is separate from approximation of Euclidean normal currents. -/
@[expose] public section
noncomputable section
namespace CZExposure.FiniteRouting
open scoped BigOperators

variable {V : Type*} [Fintype V]

inductive Walk (V : Type*) where
  | stop : V → Walk V
  | step : V → Walk V → Walk V

namespace Walk
def first : Walk V → V
  | .stop v => v
  | .step v _ => v
def last : Walk V → V
  | .stop v => v
  | .step _ γ => γ.last
def reward (g : V → ℝ) (c : V → V → ℝ) : Walk V → ℝ
  | .stop v => g v
  | .step v γ => c v γ.first + γ.reward g c
def Allowed (p : V → V → ℝ) : Walk V → Prop
  | .stop _ => True
  | .step v γ => 0 < p v γ.first ∧ γ.Allowed p
end Walk

/-- Finite weighted paths, retaining zero terms to avoid arbitrary choices. -/
def paths (p : V → V → ℝ) (q : V → ℝ) : ℕ → V → List (ℝ × Walk V)
  | 0, v => [(1, .stop v)]
  | n + 1, v => (q v, .stop v) ::
      (Finset.univ.toList.flatMap fun w =>
        (paths p q n w).map fun a => (p v w * a.1, .step v a.2))

def total (P : List (ℝ × Walk V)) (F : Walk V → ℝ) : ℝ :=
  (P.map fun a => a.1 * F a.2).sum

theorem total_succ (p : V → V → ℝ) (q : V → ℝ) (n : ℕ) (v : V)
    (F : Walk V → ℝ) :
    total (paths p q (n+1) v) F = q v * F (.stop v) +
      ∑ w, p v w * total (paths p q n w) (fun γ => F (.step v γ)) := by
  simp [paths, total, List.flatMap_def, List.sum_flatten,
    List.map_map, List.sum_map_mul_left, mul_assoc, Function.comp_def]

omit [Fintype V] in
theorem total_add (P : List (ℝ × Walk V)) (F G : Walk V → ℝ) :
    total P (fun γ => F γ + G γ) = total P F + total P G := by
  induction P with
  | nil => simp [total]
  | cons a P ih => simp only [total, List.map_cons, List.sum_cons] at *; rw [ih]; ring

omit [Fintype V] in
theorem total_const (P : List (ℝ × Walk V)) (a : ℝ) :
    total P (fun _ => a) = a * total P (fun _ => 1) := by
  simp [total, mul_comm, List.sum_map_mul_left]

theorem first_of_mem {p : V → V → ℝ} {q : V → ℝ} {n : ℕ} {v : V}
    {a : ℝ × Walk V} (ha : a ∈ paths p q n v) : a.2.first = v := by
  cases n with
  | zero => simp only [paths, List.mem_singleton] at ha; subst a; rfl
  | succ n =>
    simp only [paths, List.mem_cons, List.mem_flatMap, List.mem_map] at ha
    rcases ha with rfl | ⟨w, _, b, _, rfl⟩ <;> rfl

theorem mass (p : V → V → ℝ) (q : V → ℝ)
    (hs : ∀ v, q v + ∑ w, p v w = 1) (n : ℕ) (v : V) :
    total (paths p q n v) (fun _ => 1) = 1 := by
  induction n generalizing v with
  | zero => simp [paths, total]
  | succ n ih => simpa [total_succ, ih] using hs v

def value (p : V → V → ℝ) (q g : V → ℝ) (c : V → V → ℝ) (n : ℕ) (v : V) :=
  total (paths p q n v) (Walk.reward g c)

theorem value_succ (p : V → V → ℝ) (q g : V → ℝ) (c : V → V → ℝ)
    (hs : ∀ v, q v + ∑ w, p v w = 1) (n : ℕ) (v : V) :
    value p q g c (n+1) v = q v * g v +
      ∑ w, p v w * (c v w + value p q g c n w) := by
  rw [value, total_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  have he : total (paths p q n w) (fun γ => (Walk.step v γ).reward g c) =
      total (paths p q n w) (fun γ => c v w + γ.reward g c) := by
    unfold total
    congr 1
    apply List.map_congr_left
    intro a ha
    simp [Walk.reward, first_of_mem ha]
  rw [he, total_add, total_const, mass p q hs, mul_one]
  rfl

theorem value_stable (p : V → V → ℝ) (q g : V → ℝ) (c : V → V → ℝ)
    (hs : ∀ v, q v + ∑ w, p v w = 1)
    (height : V → ℕ) (hd : ∀ v w, p v w ≠ 0 → height w < height v)
    (n : ℕ) (v : V) (hv : height v ≤ n) :
    value p q g c (n+1) v = value p q g c n v := by
  induction n generalizing v with
  | zero =>
    have hp (w : V) : p v w = 0 := by
      by_contra h
      have := hd v w h
      omega
    have hq : q v = 1 := by simpa [hp] using hs v
    rw [value_succ p q g c hs]
    simp [hp, hq, value, paths, total, Walk.reward]
  | succ n ih =>
    rw [value_succ p q g c hs, value_succ p q g c hs]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    by_cases hp : p v w = 0
    · simp [hp]
    · rw [ih w (by have := hd v w hp; omega)]

/-- Exact finite path ledger: terminal rewards and every additive edge
observable are preserved. Choosing indicator rewards recovers individual
terminal masses and individual edge flows, not just their totals. -/
theorem ledger (p : V → V → ℝ) (q b m g : V → ℝ) (c : V → V → ℝ)
    (hs : ∀ v, q v + ∑ w, p v w = 1)
    (hb : ∀ v, m v = b v + ∑ u, m u * p u v)
    (height : V → ℕ) (hd : ∀ v w, p v w ≠ 0 → height w < height v)
    (N : ℕ) (hN : ∀ v, height v ≤ N) :
    (∑ v, b v * value p q g c N v) =
      (∑ v, m v * q v * g v) + ∑ v, ∑ w, m v * p v w * c v w := by
  have hval (v : V) : value p q g c N v = q v * g v +
      ∑ w, p v w * (c v w + value p q g c N w) := by
    rw [← value_stable p q g c hs height hd N v (hN v)]
    exact value_succ p q g c hs N v
  have hsum := congrArg (fun f : V → ℝ => ∑ v, m v * f v) (funext hval)
  have hin : (∑ v, m v * value p q g c N v) =
      (∑ v, b v * value p q g c N v) +
      ∑ u, ∑ v, m u * p u v * value p q g c N v := by
    conv_lhs => arg 2; ext v; rw [hb v, add_mul, Finset.sum_mul]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← mul_assoc] at hsum
  rw [hin] at hsum
  linarith

theorem paths_nonneg (p : V → V → ℝ) (q : V → ℝ)
    (hp : ∀ v w, 0 ≤ p v w) (hq : ∀ v, 0 ≤ q v)
    (n : ℕ) (v : V) (a : ℝ × Walk V) (ha : a ∈ paths p q n v) : 0 ≤ a.1 := by
  induction n generalizing v a with
  | zero => simp only [paths, List.mem_singleton] at ha; subst a; norm_num
  | succ n ih =>
    simp only [paths, List.mem_cons, List.mem_flatMap, List.mem_map] at ha
    rcases ha with rfl | ⟨w, _, a, ha, rfl⟩
    · exact hq v
    · exact mul_nonneg (hp v w) (ih w a ha)

theorem paths_allowed (p : V → V → ℝ) (q : V → ℝ)
    (hp : ∀ v w, 0 ≤ p v w) (hq : ∀ v, 0 ≤ q v)
    (n : ℕ) (v : V) (a : ℝ × Walk V) (ha : a ∈ paths p q n v)
    (ha0 : 0 < a.1) : a.2.Allowed p := by
  induction n generalizing v a with
  | zero => simp only [paths, List.mem_singleton] at ha; subst a; trivial
  | succ n ih =>
    simp only [paths, List.mem_cons, List.mem_flatMap, List.mem_map] at ha
    rcases ha with rfl | ⟨w, _, a, ha, rfl⟩
    · trivial
    · have hpos : 0 < p v w ∧ 0 < a.1 :=
        ⟨pos_of_mul_pos_left ha0 (paths_nonneg p q hp hq n w a ha),
          pos_of_mul_pos_right ha0 (hp v w)⟩
      exact ⟨by simpa [first_of_mem ha] using hpos.1, ih w a ha hpos.2⟩

theorem paths_terminal (p : V → V → ℝ) (q : V → ℝ)
    (hp : ∀ v w, 0 ≤ p v w) (hq : ∀ v, 0 ≤ q v)
    (hs : ∀ v, q v + ∑ w, p v w = 1)
    (height : V → ℕ) (hd : ∀ v w, p v w ≠ 0 → height w < height v)
    (n : ℕ) (v : V) (hv : height v ≤ n)
    (a : ℝ × Walk V) (ha : a ∈ paths p q n v) (ha0 : 0 < a.1) :
    0 < q a.2.last := by
  induction n generalizing v a with
  | zero =>
    simp only [paths, List.mem_singleton] at ha
    subst a
    have hz (w : V) : p v w = 0 := by
      by_contra h
      have := hd v w h
      omega
    have he : q v = 1 := by simpa [hz] using hs v
    simp [Walk.last, he]
  | succ n ih =>
    simp only [paths, List.mem_cons, List.mem_flatMap, List.mem_map] at ha
    rcases ha with rfl | ⟨w, _, a, ha, rfl⟩
    · exact ha0
    · have hpos : 0 < p v w ∧ 0 < a.1 :=
        ⟨pos_of_mul_pos_left ha0 (paths_nonneg p q hp hq n w a ha),
          pos_of_mul_pos_right ha0 (hp v w)⟩
      exact ih w (by have := hd v w hpos.1.ne'; omega) a ha hpos.2

def Walk.vertices : Walk V → List V
  | .stop v => [v]
  | .step v γ => v :: γ.vertices

omit [Fintype V] in
theorem Walk.height_le (γ : Walk V) (p : V → V → ℝ) (h : γ.Allowed p)
    (height : V → ℕ) (hd : ∀ v w, p v w ≠ 0 → height w < height v)
    (w : V) (hw : w ∈ γ.vertices) : height w ≤ height γ.first := by
  induction γ with
  | stop v => simp only [Walk.vertices, List.mem_singleton] at hw; subst w; exact le_rfl
  | step v γ ih =>
    simp only [Walk.vertices, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact le_rfl
    · exact (ih h.2 hw).trans (hd v γ.first h.1.ne').le

omit [Fintype V] in
theorem Walk.nodup (γ : Walk V) (p : V → V → ℝ) (h : γ.Allowed p)
    (height : V → ℕ) (hd : ∀ v w, p v w ≠ 0 → height w < height v) :
    γ.vertices.Nodup := by
  induction γ with
  | stop v => simp [Walk.vertices]
  | step v γ ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih h.2⟩
    intro hv
    have := γ.height_le p h.2 height hd v hv
    have := hd v γ.first h.1.ne'
    omega

/-- Raw nonnegative edge flows with a topological height certificate. -/
structure Flow (V : Type*) [Fintype V] where
  edge : V → V → ℝ
  nonneg : ∀ v w, 0 ≤ edge v w
  height : V → ℕ
  decreases : ∀ v w, edge v w ≠ 0 → height w < height v

namespace Flow
variable (f : Flow V)
def incoming (v : V) : ℝ := ∑ u, f.edge u v
def outgoing (v : V) : ℝ := ∑ w, f.edge v w
def throughput (v : V) : ℝ := max (f.incoming v) (f.outgoing v)
def source (v : V) : ℝ := f.throughput v - f.incoming v
def sink (v : V) : ℝ := f.throughput v - f.outgoing v
def transition (v w : V) : ℝ := f.edge v w / f.throughput v
def stopping (v : V) : ℝ := if f.throughput v = 0 then 1 else f.sink v / f.throughput v

theorem incoming_nonneg (v : V) : 0 ≤ f.incoming v := Finset.sum_nonneg fun u _ => f.nonneg u v
theorem outgoing_nonneg (v : V) : 0 ≤ f.outgoing v := Finset.sum_nonneg fun w _ => f.nonneg v w
theorem throughput_nonneg (v : V) : 0 ≤ f.throughput v :=
  (f.incoming_nonneg v).trans (le_max_left _ _)
theorem source_nonneg (v : V) : 0 ≤ f.source v := sub_nonneg.mpr (le_max_left _ _)
theorem sink_nonneg (v : V) : 0 ≤ f.sink v := sub_nonneg.mpr (le_max_right _ _)
theorem transition_nonneg (v w : V) : 0 ≤ f.transition v w :=
  div_nonneg (f.nonneg v w) (f.throughput_nonneg v)
theorem stopping_nonneg (v : V) : 0 ≤ f.stopping v := by
  unfold stopping
  split
  · norm_num
  · exact div_nonneg (f.sink_nonneg v) (f.throughput_nonneg v)

theorem edge_zero (v w : V) (h : f.throughput v = 0) : f.edge v w = 0 := by
  have he : f.edge v w ≤ f.outgoing v := Finset.single_le_sum (fun x _ => f.nonneg v x) (Finset.mem_univ w)
  have ho : f.outgoing v ≤ f.throughput v := le_max_right _ _
  have := f.nonneg v w
  linarith

theorem throughput_transition (v w : V) : f.throughput v * f.transition v w = f.edge v w := by
  by_cases h : f.throughput v = 0
  · simp [transition, h, f.edge_zero v w h]
  · exact mul_div_cancel₀ _ h

theorem throughput_stopping (v : V) : f.throughput v * f.stopping v = f.sink v := by
  by_cases h : f.throughput v = 0
  · have ho : f.outgoing v = 0 := by
      have := f.outgoing_nonneg v
      have : f.outgoing v ≤ f.throughput v := le_max_right _ _
      linarith
    simp [stopping, sink, h, ho]
  · simp only [stopping, if_neg h]
    exact mul_div_cancel₀ _ h

theorem normalized (v : V) : f.stopping v + ∑ w, f.transition v w = 1 := by
  by_cases h : f.throughput v = 0
  · simp [stopping, transition, h]
  · simp only [stopping, if_neg h, transition, ← Finset.sum_div, ← add_div]
    rw [show f.sink v + ∑ w, f.edge v w = f.throughput v by unfold sink outgoing; ring]
    exact div_self h

theorem balance (v : V) : f.throughput v = f.source v + ∑ u, f.throughput u * f.transition u v := by
  simp only [f.throughput_transition]
  unfold source incoming
  ring

theorem transition_decreases (v w : V) (h : f.transition v w ≠ 0) : f.height w < f.height v :=
  f.decreases v w (fun he => h (by simp [transition, he]))

/-- Explicit finite ensemble, not an assumed decomposition oracle. -/
def decomposition : List (ℝ × Walk V) :=
  Finset.univ.toList.flatMap fun v =>
    (paths f.transition f.stopping (Finset.univ.sup f.height) v).map fun a =>
      (f.source v * a.1, a.2)

theorem decomposition_total (F : Walk V → ℝ) :
    total f.decomposition F = ∑ v, f.source v *
      total (paths f.transition f.stopping (Finset.univ.sup f.height) v) F := by
  simp [decomposition, total, List.flatMap_def, List.sum_flatten,
    List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]

theorem decomposition_ledger (g : V → ℝ) (c : V → V → ℝ) :
    total f.decomposition (Walk.reward g c) =
      (∑ v, f.sink v * g v) + ∑ v, ∑ w, f.edge v w * c v w := by
  rw [f.decomposition_total]
  have h := ledger f.transition f.stopping f.source f.throughput g c
    f.normalized f.balance f.height f.transition_decreases (Finset.univ.sup f.height)
    (fun v => Finset.le_sup (f := f.height) (Finset.mem_univ v))
  simpa only [value, f.throughput_transition, f.throughput_stopping] using h

theorem decomposition_nonneg (a : ℝ × Walk V) (ha : a ∈ f.decomposition) : 0 ≤ a.1 := by
  simp only [decomposition, List.mem_flatMap, List.mem_map] at ha
  obtain ⟨v, _, a, ha, rfl⟩ := ha
  exact mul_nonneg (f.source_nonneg v)
    (paths_nonneg _ _ f.transition_nonneg f.stopping_nonneg _ v a ha)

theorem decomposition_initial (g : V → ℝ) :
    total f.decomposition (fun γ => g γ.first) = ∑ v, f.source v * g v := by
  rw [f.decomposition_total]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  have he : total (paths f.transition f.stopping (Finset.univ.sup f.height) v)
      (fun γ => g γ.first) =
      total (paths f.transition f.stopping (Finset.univ.sup f.height) v) (fun _ => g v) := by
    unfold total
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [first_of_mem ha]
  rw [he, total_const, mass _ _ f.normalized, mul_one]

private theorem last_throughput (γ : Walk V) (h : γ.Allowed f.transition)
    (h0 : 0 < f.throughput γ.first) : 0 < f.throughput γ.last := by
  induction γ with
  | stop v => exact h0
  | step v γ ih =>
    apply ih h.2
    have he : 0 < f.edge v γ.first := by
      rw [← f.throughput_transition]
      exact mul_pos h0 h.1
    have hi : f.edge v γ.first ≤ f.incoming γ.first :=
      Finset.single_le_sum (fun u _ => f.nonneg u γ.first) (Finset.mem_univ v)
    exact (he.trans_le hi).trans_le (le_max_left _ _)

/-- Every positive-weight path is simple, uses positive original edges,
and starts/ends at the actual net source/sink. Zero terms may be discarded. -/
theorem decomposition_support (a : ℝ × Walk V) (ha : a ∈ f.decomposition)
    (ha0 : 0 < a.1) :
    a.2.vertices.Nodup ∧ a.2.Allowed f.edge ∧
      0 < f.source a.2.first ∧ 0 < f.sink a.2.last := by
  simp only [decomposition, List.mem_flatMap, List.mem_map] at ha
  obtain ⟨v, _, a, ha, rfl⟩ := ha
  have hnn := paths_nonneg _ _ f.transition_nonneg f.stopping_nonneg _ v a ha
  have hs := pos_of_mul_pos_left ha0 hnn
  have hp := pos_of_mul_pos_right ha0 (f.source_nonneg v)
  have hal := paths_allowed _ _ f.transition_nonneg f.stopping_nonneg _ v a ha hp
  have hfirst := first_of_mem ha
  have ht : 0 < f.throughput a.2.first := by
    rw [hfirst]
    have := f.incoming_nonneg v
    dsimp [source] at hs
    linarith
  have hl := f.last_throughput a.2 hal ht
  have hstop := paths_terminal _ _ f.transition_nonneg f.stopping_nonneg f.normalized
    f.height f.transition_decreases _ v (Finset.le_sup (Finset.mem_univ v)) a ha hp
  refine ⟨a.2.nodup _ hal f.height f.transition_decreases, ?_, by simpa [hfirst], ?_⟩
  · have hc (γ : Walk V) (h : γ.Allowed f.transition) : γ.Allowed f.edge := by
      induction γ with
      | stop w => trivial
      | step w γ ih =>
        refine ⟨?_, ih h.2⟩
        exact lt_of_le_of_ne (f.nonneg w γ.first)
          (Ne.symm (fun he => h.1.ne' (by simp [transition, he])))
    exact hc a.2 hal
  · rw [← f.throughput_stopping]
    exact mul_pos hl hstop

theorem source_eq (v : V) : f.source v = max (f.outgoing v - f.incoming v) 0 := by
  unfold source throughput
  by_cases h : f.incoming v ≤ f.outgoing v
  · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_left (le_of_not_ge h), sub_self, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

theorem sink_eq (v : V) : f.sink v = max (f.incoming v - f.outgoing v) 0 := by
  unfold sink throughput
  by_cases h : f.outgoing v ≤ f.incoming v
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_right (le_of_not_ge h), sub_self, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

theorem source_sink_disjoint (v : V) : f.source v = 0 ∨ f.sink v = 0 := by
  rcases le_total (f.incoming v) (f.outgoing v) with h | h
  · right; simp [sink, throughput, max_eq_right h]
  · left; simp [source, throughput, max_eq_left h]

theorem decomposition_terminal (g : V → ℝ) :
    total f.decomposition (fun γ => g γ.last) = ∑ v, f.sink v * g v := by
  have he (γ : Walk V) : γ.reward g (fun _ _ => 0) = g γ.last := by
    induction γ with
    | stop v => rfl
    | step v γ ih => simpa [Walk.reward, Walk.last] using ih
  have hfun : Walk.reward g (fun _ _ => 0) = (fun γ => g γ.last) := funext he
  simpa only [hfun, mul_zero, Finset.sum_const_zero, add_zero] using
    f.decomposition_ledger g (fun _ _ => 0)

/-- Exact usage of a named edge, with multiplicity counted along each path. -/
theorem decomposition_edge [DecidableEq V] (u v : V) :
    total f.decomposition (Walk.reward (fun _ => 0)
      (fun x y => if x = u ∧ y = v then 1 else 0)) = f.edge u v := by
  simpa [ite_and] using f.decomposition_ledger (fun _ => 0)
    (fun x y => if x = u ∧ y = v then 1 else 0)

end Flow

/-- Acyclicity supplies the finite height: count strictly reachable vertices.
No topological ordering is assumed as additional external data. -/
def Flow.ofAcyclic (edge : V → V → ℝ) (hn : ∀ v w, 0 ≤ edge v w)
    (ha : ∀ v, ¬Relation.TransGen (fun x y => 0 < edge x y) v v) : Flow V := by
  classical
  let reachable (v : V) := Finset.univ.filter (Relation.TransGen (fun x y => 0 < edge x y) v)
  refine ⟨edge, hn, fun v => (reachable v).card, ?_⟩
  intro v w h
  have hp : 0 < edge v w := lt_of_le_of_ne (hn v w) (Ne.symm h)
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact Relation.TransGen.head hp hz
  · intro hsub
    have hw : w ∈ reachable v := by
      simp only [reachable, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single hp
    have hww := hsub hw
    exact ha w (Finset.mem_filter.mp hww).2

/-- Every finite nonnegative acyclic flow has a finite nonnegative simple-path
decomposition preserving each edge and both net boundary measures. -/
theorem exists_decomposition (edge : V → V → ℝ) (hn : ∀ v w, 0 ≤ edge v w)
    (ha : ∀ v, ¬Relation.TransGen (fun x y => 0 < edge x y) v v) :
    ∃ P : List (ℝ × Walk V),
      (∀ a ∈ P, 0 ≤ a.1) ∧
      (∀ a ∈ P, 0 < a.1 → a.2.vertices.Nodup ∧ a.2.Allowed edge ∧
        (∑ u, edge u a.2.first) < (∑ w, edge a.2.first w) ∧
        (∑ w, edge a.2.last w) < (∑ u, edge u a.2.last)) ∧
      (∀ g : V → ℝ, total P (fun γ => g γ.first) =
        ∑ v, max ((∑ w, edge v w) - ∑ u, edge u v) 0 * g v) ∧
      (∀ g : V → ℝ, total P (fun γ => g γ.last) =
        ∑ v, max ((∑ u, edge u v) - ∑ w, edge v w) 0 * g v) ∧
      (∀ c : V → V → ℝ, total P (Walk.reward (fun _ => 0) c) =
        ∑ v, ∑ w, edge v w * c v w) := by
  let f := Flow.ofAcyclic edge hn ha
  refine ⟨f.decomposition, f.decomposition_nonneg, ?_, ?_, ?_, ?_⟩
  · intro a ha hp
    obtain ⟨hnd, hal, hs, ht⟩ := f.decomposition_support a ha hp
    refine ⟨hnd, hal, ?_, ?_⟩
    · rw [f.source_eq] at hs
      have : 0 < f.outgoing a.2.first - f.incoming a.2.first :=
        (lt_max_iff.mp hs).resolve_right (lt_irrefl 0)
      exact sub_pos.mp this
    · rw [f.sink_eq] at ht
      have : 0 < f.incoming a.2.last - f.outgoing a.2.last :=
        (lt_max_iff.mp ht).resolve_right (lt_irrefl 0)
      exact sub_pos.mp this
  · intro g
    simpa only [f.source_eq, Flow.incoming, Flow.outgoing] using f.decomposition_initial g
  · intro g
    simpa only [f.sink_eq, Flow.incoming, Flow.outgoing] using f.decomposition_terminal g
  · intro c
    simpa only [mul_zero, Finset.sum_const_zero, zero_add] using f.decomposition_ledger (fun _ => 0) c

end CZExposure.FiniteRouting
