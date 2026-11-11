import LowerBoundCZ.PinnedInterfaces
import LowerBoundCZ.ProfileData

/-! Fixed final occupation profiles and honest conditional integral accounting.
The local profile inequalities and the mandatory-prefix crossing times are
analytic obligations, not numerical-certificate assumptions. This module does
not assert that those obligations have been discharged for the fixed data. -/
noncomputable section
namespace LowerBoundCZ.Certification.OccupationLedger
open CZExposure MvPolynomial MeasureTheory Set Slack

def entry (i : ℕ) : ProfileData.EncodedProfile := ProfileData.profiles[i]?.getD default
def left (i : ℕ) : ℚ := AllocationCodec.rational (entry i).left
def right (i : ℕ) : ℚ := AllocationCodec.rational (entry i).right
def power (i : ℕ) (k : Fin 15) : ℚ :=
  (AllocationCodec.rationals (entry i).power)[k.val]?.getD 0
def primitiveCoefficient (i : ℕ) (k : Fin 15) : ℚ := power i k / (k.val+1)
def primitive (i : ℕ) : MvPolynomial Unit ℝ :=
  ∑ k : Fin 15, C (primitiveCoefficient i k : ℝ) * X () ^ (k.val+1)
def credit (i : ℕ) : ℚ := (right i - left i) * ∑ k : Fin 15, primitiveCoefficient i k
def count (j : ℕ) : ℕ := if j = 4 then 65 else 64
def totalCredit : ℚ := ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range (count j), credit (64*j+k)

/-- The tail is slot 320, not a second credit for slot 319. -/
theorem index_unique {j j' k k' : ℕ} (hj : j < 5) (hj' : j' < 5)
    (hk : k < count j) (hk' : k' < count j') (h : 64*j+k = 64*j'+k') :
    j = j' ∧ k = k' := by
  simp only [count] at hk hk'
  split_ifs at hk hk' <;> omega

theorem index_lt {j k : ℕ} (hj : j < 5) (hk : k < count j) : 64*j+k < 321 := by
  simp only [count] at hk
  split_ifs at hk <;> omega

theorem primitive_credit (i : ℕ) :
    ((right i - left i : ℚ) : ℝ) *
      (eval (fun _ => 1) (primitive i) - eval (fun _ => 0) (primitive i)) =
      (credit i : ℝ) := by
  simp [primitive, credit, primitiveCoefficient]

/-- A finite local polynomial inequality yields the exact signed-power
primitive credit. Exposure may stall; no inverse parametrization is used. -/
theorem interval_credit (γ : ActivePulse) (j i : ℕ) {a b : ℝ}
    (hw : left i < right i) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S)
    (hl : γ.cumI a = left i) (hr : γ.cumI b = right i)
    (hpoint : ∀ t ∈ Icc a b,
      eval (fun _ : Unit => (γ.cumI t-left i)/(right i-left i))
        (pderiv () (primitive i)) * cost (γ.traj t) ≤
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t) :
    (credit i : ℝ) ≤ ∫ t in a..b,
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t := by
  have h := profile_credit Pinned.partition Pinned.order7.ceiling Pinned.order7.potential
    γ j (primitive i) (l := left i) (w := (right i : ℝ)-left i)
    (sub_pos.mpr (Rat.cast_lt.mpr hw)) ha hab hb hl (by rw [hr]; ring) hpoint
  rw [← Rat.cast_sub, primitive_credit] at h
  exact h

/-- Adjacent credited intervals occupy a prefix, not the whole cell. The
uncredited remainder can be discarded only when its slack is nonnegative. -/
theorem prefix_sum_le {n : ℕ} {f : ℝ → ℝ} {a : ℕ → ℝ} {b : ℝ}
    {c : ℕ → ℝ} (hcredit : ∀ k < n, c k ≤ ∫ t in a k..a (k+1), f t)
    (hint : ∀ k < n, IntervalIntegrable f volume (a k) (a (k+1)))
    (htail : IntervalIntegrable f volume (a n) b) (hend : a n ≤ b)
    (hnonneg : ∀ t ∈ Icc (a n) b, 0 ≤ f t) :
    ∑ k ∈ Finset.range n, c k ≤ ∫ t in a 0..b, f t := by
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun k hk =>
    hcredit k (Finset.mem_range.mp hk))
  rw [intervalIntegral.sum_integral_adjacent_intervals hint] at hsum
  have hpre : IntervalIntegrable f volume (a 0) (a n) :=
    IntervalIntegrable.trans_iterate hint
  have htailpos := intervalIntegral.integral_nonneg (μ := volume) hend hnonneg
  rw [← intervalIntegral.integral_add_adjacent_intervals hpre htail]
  linarith

/-- Explicit proof obligations for the time subdivision. In particular,
`exposure_left/right` must follow from a proved mandatory prefix; they are not
fields of a finite `NumericalChecks` interface. -/
structure Traversal (γ : ActivePulse) (s : Crossings γ) where
  time : ℕ → ℕ → ℝ
  start : ∀ j < 5, time j 0 = s.time j
  mem : ∀ j < 5, ∀ k ≤ count j, time j k ∈ Icc 0 γ.S
  ordered : ∀ j < 5, ∀ k < count j, time j k ≤ time j (k+1)
  finish : ∀ j < 5, time j (count j) ≤ s.time (j+1)
  width : ∀ j < 5, ∀ k < count j, left (64*j+k) < right (64*j+k)
  exposure_left : ∀ j < 5, ∀ k < count j, γ.cumI (time j k) = left (64*j+k)
  exposure_right : ∀ j < 5, ∀ k < count j, γ.cumI (time j (k+1)) = right (64*j+k)

def level (j k : ℕ) : ℚ := if k = 0 then left (64*j) else right (64*j+k-1)

/-- Only fixed rational endpoint facts; no statement about a physical pulse. -/
structure LayoutChecks : Prop where
  width : ∀ j < 5, ∀ k < count j, left (64*j+k) < right (64*j+k)
  join : ∀ j < 5, ∀ k < count j, level j k = left (64*j+k)
  start : ∀ j < 5, (left (64*j) : ℝ) = Pinned.order7.ceiling * Pinned.partition.a j
  bounds : ∀ j < 5, ∀ k ≤ count j,
    Pinned.order7.ceiling * Pinned.partition.a j ≤ (level j k : ℝ) ∧
    (level j k : ℝ) ≤ if j < 4 then
      Pinned.order7.ceiling * Pinned.partition.a (j+1) else (right 320 : ℝ)

theorem level_succ (j k : ℕ) : level j (k+1) = right (64*j+k) := by
  simp [level]

/-- Once the mandatory tail endpoint has been established, continuity supplies
all 321 crossings. The threshold remains an explicit analytic premise: it is
strictly stronger than the original 2.9305 bound and cannot be assumed as data. -/
theorem traversal_exists (h : LayoutChecks) {γ : ActivePulse} (s : Crossings γ)
    (hprefix : (right 320 : ℝ) ≤ γ.exposure) : Nonempty (Traversal γ s) := by
  classical
  have start_level (j : ℕ) (hj : j < 5) :
      γ.cumI (s.time j) = Pinned.order7.ceiling * Pinned.partition.a j := by
    cases j with
    | zero => simp [s.start, γ.cumI_zero, Pinned.partition]
    | succ k => exact s.level k (by omega)
  have hit (j : ℕ) (hj : j < 5) (k : ℕ) (hk : k ≤ count j) :
      ∃ t ∈ Icc (s.time j) (s.time (j+1)), γ.cumI t = (level j k : ℝ) := by
    apply intermediate_value_Icc (s.ordered j hj).le
      (γ.continuousOn_cumI.mono (Icc_subset_Icc (s.mem j (by omega)).1
        (s.mem (j+1) (by omega)).2))
    refine ⟨?_, ?_⟩
    · rw [start_level j hj]; exact (h.bounds j hj k hk).1
    · have hb := (h.bounds j hj k hk).2
      by_cases hj4 : j < 4
      · rw [if_pos hj4, ← s.level j hj4] at hb
        exact hb
      · have he : j = 4 := by omega
        rw [if_neg hj4] at hb
        subst j
        simpa only [s.finish, γ.cumI_S] using hb.trans hprefix
  choose t ht he using hit
  let time (j k : ℕ) : ℝ := if k = 0 then s.time j else
    if hj : j < 5 then if hk : k ≤ count j then t j hj k hk else 0 else 0
  have tm (j : ℕ) (hj : j < 5) (k : ℕ) (hk : k ≤ count j) :
      time j k ∈ Icc (s.time j) (s.time (j+1)) := by
    by_cases hk0 : k = 0
    · simp only [time, if_pos hk0]
      exact ⟨le_rfl, (s.ordered j hj).le⟩
    · simpa only [time, if_neg hk0, dif_pos hj, dif_pos hk] using ht j hj k hk
  have te (j : ℕ) (hj : j < 5) (k : ℕ) (hk : k ≤ count j) :
      γ.cumI (time j k) = (level j k : ℝ) := by
    by_cases hk0 : k = 0
    · subst k
      simpa [time, level, h.start j hj] using start_level j hj
    · simpa only [time, if_neg hk0, dif_pos hj, dif_pos hk] using he j hj k hk
  have mem (j : ℕ) (hj : j < 5) (k : ℕ) (hk : k ≤ count j) :
      time j k ∈ Icc 0 γ.S :=
    ⟨(s.mem j (by omega)).1.trans (tm j hj k hk).1,
      (tm j hj k hk).2.trans (s.mem (j+1) (by omega)).2⟩
  refine ⟨⟨time, ?_, mem, ?_, ?_, h.width, ?_, ?_⟩⟩
  · intro j hj; simp [time]
  · intro j hj k hk
    apply le_of_lt (cumI_lt_time_lt γ (mem j hj k (by omega)) (mem j hj (k+1) (by omega)) ?_)
    rw [te j hj k (by omega), te j hj (k+1) (by omega), h.join j hj k hk, level_succ]
    exact Rat.cast_lt.mpr (h.width j hj k hk)
  · intro j hj; exact (tm j hj (count j) le_rfl).2
  · intro j hj k hk; rw [te j hj k (by omega), h.join j hj k hk]
  · intro j hj k hk; rw [te j hj (k+1) (by omega), level_succ]

/-- Local profile bounds and nonnegative uncredited tails, as analytic
premises. No accumulated-slack inequality is taken as an input. -/
theorem occupation_credit {γ : ActivePulse} {s : Crossings γ} (a : Traversal γ s)
    (hpoint : ∀ j < 5, ∀ k < count j, ∀ t ∈ Icc (a.time j k) (a.time j (k+1)),
      eval (fun _ : Unit => (γ.cumI t-left (64*j+k))/(right (64*j+k)-left (64*j+k)))
        (pderiv () (primitive (64*j+k))) * cost (γ.traj t) ≤
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t)
    (htail : ∀ j < 5, ∀ t ∈ Icc (a.time j (count j)) (s.time (j+1)),
      0 ≤ occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t) :
    (totalCredit : ℝ) ≤ ∑ j ∈ Finset.range 5, ∫ t in s.time j..s.time (j+1),
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t := by
  simp only [totalCredit, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hint {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ γ.S) :
      IntervalIntegrable (occupationSlack Pinned.partition Pinned.order7.ceiling
        Pinned.order7.potential γ j) volume u v :=
    (γ.intervalIntegrable_cost hu huv hv).sub
      (cell_potential_intervalIntegrable _ _ _ γ j hu huv hv)
  rw [← a.start j hj']
  apply prefix_sum_le
  · intro k hk
    exact interval_credit γ j (64*j+k) (a.width j hj' k hk)
      (a.mem j hj' k (by omega)).1 (a.ordered j hj' k hk)
      (a.mem j hj' (k+1) (by omega)).2
      (a.exposure_left j hj' k hk) (a.exposure_right j hj' k hk) (hpoint j hj' k hk)
  · intro k hk
    exact hint (a.mem j hj' k (by omega)).1 (a.ordered j hj' k hk)
      (a.mem j hj' (k+1) (by omega)).2
  · exact hint (a.mem j hj' (count j) le_rfl).1 (a.finish j hj')
      (s.mem (j+1) (by omega)).2
  · exact a.finish j hj'
  · exact htail j hj'

/-- The discarded part of a cell has nonnegative slack by the original Gram
certificate, not by a new assumption on the trajectory's accumulated slack. -/
theorem slack_nonneg (A : GramBridge.Archive Pinned.order7) (h : GramBridge.MatrixChecks A)
    {γ : ActivePulse} (s : Crossings γ) (hcap : γ.exposure ≤ 733/250)
    {j : ℕ} (hj : j < 5) {t : ℝ} (ht : t ∈ Icc (s.time j) (s.time (j+1))) :
    0 ≤ occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t := by
  have ht' : t ∈ Icc 0 γ.S := ⟨(s.mem j (by omega)).1.trans ht.1,
    ht.2.trans (s.mem (j+1) (by omega)).2⟩
  have hC : γ.exposure ≤ Pinned.order7.ceiling :=
    hcap.trans (by norm_num [Pinned.order7])
  have hc := ((Pinned.order7_checks_of_grams A h).feasible j hj).2.2.1
  have hx : γ.traj t ∈ Xset := by rw [γ.traj_eq ht']; exact γ.x_mem t ht'
  have hn := hc.eval_nonneg (s.cell_domain hC hj ht) hx (γ.u_unit t ht')
  simpa only [ResidualSymmetry.eval_embed, Complex.ofReal_re, map_sub,
    eval_pt_cpoly, occupationSlack] using hn

/-- Fixed occupation credits and all four fixed interface credits in the same
physical accounting identity. The remaining analytic obligations are exposed
as `a` and `hpoint`; this is not yet the strengthened physical lower bound. -/
theorem credited_telescope (A : GramBridge.Archive Pinned.order7)
    (hmatrix : GramBridge.MatrixChecks A) (hinterface : PinnedInterface.NumericalChecks)
    {γ : ActivePulse} (s : Crossings γ) (hcap : γ.exposure ≤ 733/250) (a : Traversal γ s)
    (hpoint : ∀ j < 5, ∀ k < count j, ∀ t ∈ Icc (a.time j k) (a.time j (k+1)),
      eval (fun _ : Unit => (γ.cumI t-left (64*j+k))/(right (64*j+k)-left (64*j+k)))
        (pderiv () (primitive (64*j+k))) * cost (γ.traj t) ≤
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j t) :
    (totalCredit : ℝ) + (∑ j : Fin 4, (PinnedInterface.credit j : ℝ)) +
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S)
      (Pinned.order7.potential 4) -
    evalCell 0 (γ.traj 0) (Pinned.order7.potential 0) ≤ γ.exposure := by
  have ho := occupation_credit a hpoint (fun j hj t ht => by
    apply slack_nonneg A hmatrix s hcap hj
    refine ⟨?_, ht.2⟩
    have hstart : ∀ k ≤ count j, a.time j 0 ≤ a.time j k := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact (ih (by omega)).trans (a.ordered j hj k (by omega))
    rw [← a.start j hj]
    exact (hstart (count j) le_rfl).trans ht.1)
  linarith [PinnedInterface.credited_telescope hinterface s hcap]

end LowerBoundCZ.Certification.OccupationLedger
