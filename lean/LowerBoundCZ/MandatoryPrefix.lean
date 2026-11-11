import LowerBoundCZ.OccupationCoverage
import LowerBoundCZ.SlackEndpoint
import LowerBoundCZ.PrefixData

/-! Bootstrap from 319 profiles already reached at the base bound.
The last main profile and the tail are NOT used to prove their own traversal.
Only fixed polynomial identities and rational inequalities remain external. -/
noncomputable section
namespace LowerBoundCZ.Certification.MandatoryPrefix
open CZExposure MvPolynomial MeasureTheory Set Slack OccupationLedger TerminalCertificate

def count (j : ℕ) : ℕ := if j = 4 then 63 else 64
def credit : ℚ := ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range (count j), OccupationLedger.credit (64*j+k)
def base : ℚ := 5861/2000

theorem count_le (j : ℕ) : count j ≤ OccupationLedger.count j := by
  simp only [count, OccupationLedger.count]; split_ifs <;> omega

/-- All fields describe finite rational layout data, not physical reachability. -/
structure LayoutChecks : Prop where
  full : OccupationLedger.LayoutChecks
  reached : ∀ j < 5, ∀ k ≤ count j, (level j k : ℝ) ≤
    if j < 4 then Pinned.order7.ceiling * Pinned.partition.a (j+1) else (base : ℝ)

/-- Use only the 319 intervals ending below the already proved base bound. -/
theorem prefix_credit (h : LayoutChecks) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    {γ : ActivePulse} (s : Crossings γ) (hL : (base : ℝ) ≤ γ.exposure)
    (hcap : γ.exposure ≤ 733/250) :
    (credit : ℝ) ≤ ∑ j ∈ Finset.range 5, ∫ z in s.time j..s.time (j+1),
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j z := by
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
    · rw [start_level j hj]
      exact (h.full.bounds j hj k (hk.trans (count_le j))).1
    · have hb := h.reached j hj k hk
      by_cases hj4 : j < 4
      · rw [if_pos hj4, ← s.level j hj4] at hb; exact hb
      · have he : j = 4 := by omega
        rw [if_neg hj4] at hb
        subst j
        simpa only [s.finish, γ.cumI_S] using hb.trans hL
  choose t ht he using hit
  simp only [credit, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  let a (k : ℕ) : ℝ := if k = 0 then s.time j else
    if hk : k ≤ count j then t j hj' k hk else 0
  have am (k : ℕ) (hk : k ≤ count j) : a k ∈ Icc (s.time j) (s.time (j+1)) := by
    by_cases hk0 : k = 0
    · simp only [a, if_pos hk0]; exact ⟨le_rfl, (s.ordered j hj').le⟩
    · simpa only [a, if_neg hk0, dif_pos hk] using ht j hj' k hk
  have ae (k : ℕ) (hk : k ≤ count j) : γ.cumI (a k) = (level j k : ℝ) := by
    by_cases hk0 : k = 0
    · subst k; simpa [a, level, h.full.start j hj'] using start_level j hj'
    · simpa only [a, if_neg hk0, dif_pos hk] using he j hj' k hk
  have mem (k : ℕ) (hk : k ≤ count j) : a k ∈ Icc 0 γ.S :=
    ⟨(s.mem j (by omega)).1.trans (am k hk).1,
      (am k hk).2.trans (s.mem (j+1) (by omega)).2⟩
  have ord (k : ℕ) (hk : k < count j) : a k ≤ a (k+1) := by
    apply le_of_lt (cumI_lt_time_lt γ (mem k (by omega)) (mem (k+1) (by omega)) ?_)
    rw [ae k (by omega), ae (k+1) (by omega), h.full.join j hj' k (hk.trans_le (count_le j)), level_succ]
    exact Rat.cast_lt.mpr (h.full.width j hj' k (hk.trans_le (count_le j)))
  have hint {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ γ.S) :
      IntervalIntegrable (occupationSlack Pinned.partition Pinned.order7.ceiling
        Pinned.order7.potential γ j) volume u v :=
    (γ.intervalIntegrable_cost hu huv hv).sub
      (cell_potential_intervalIntegrable _ _ _ γ j hu huv hv)
  change _ ≤ ∫ z in a 0..s.time (j+1), _
  apply prefix_sum_le
  · intro k hk
    have hk' := hk.trans_le (count_le j)
    have hl : γ.cumI (a k) = left (64*j+k) := by rw [ae k (by omega), h.full.join j hj' k hk']
    have hright : γ.cumI (a (k+1)) = right (64*j+k) := by rw [ae (k+1) (by omega), level_succ]
    apply interval_credit γ j (64*j+k) (h.full.width j hj' k hk')
      (mem k (by omega)).1 (ord k hk) (mem (k+1) (by omega)).2 hl hright
    intro z hz
    have hz' : z ∈ Icc 0 γ.S := ⟨(mem k (by omega)).1.trans hz.1,
      hz.2.trans (mem (k+1) (by omega)).2⟩
    let i : OccupationCoverage.Slot := ⟨64*j+k, index_lt hj' hk'⟩
    have hi : OccupationCoverage.cell i = j := by
      simp only [OccupationCoverage.cell, i]
      simp only [count] at hk; split_ifs at hk <;> omega
    have hex : γ.cumI z ∈ Icc (left i.val : ℝ) (right i.val : ℝ) := by
      constructor
      · rw [show (left i.val : ℝ) = γ.cumI (a k) from hl.symm]
        exact γ.cumI_mono (mem k (by omega)).1 hz.1 hz'.2
      · rw [show (right i.val : ℝ) = γ.cumI (a (k+1)) from hright.symm]
        exact γ.cumI_mono hz'.1 hz.2 (mem (k+1) (by omega)).2
    simpa only [hi] using OccupationCoverage.pointwise_slack hc ha hr i γ hz' hcap hex
  · intro k hk; exact hint (mem k (by omega)).1 (ord k hk) (mem (k+1) (by omega)).2
  · exact hint (mem (count j) le_rfl).1 (am (count j) le_rfl).2 (s.mem (j+1) (by omega)).2
  · exact (am (count j) le_rfl).2
  · intro z hz
    exact slack_nonneg A hm s hcap hj' ⟨(am (count j) le_rfl).1.trans hz.1, hz.2⟩

def exposurePolynomial : UniPoly := C (base : ℝ) + C ((right 320 : ℝ)-base)*X ()
def xiPolynomial : UniPoly := C (36 / Pinned.order7.ceiling) * exposurePolynomial - C 35
def endpointPolynomial : UniPoly :=
  aeval (fun _ : Unit => xiPolynomial) (terminalRestriction (Pinned.order7.potential 4)) +
  C (Pinned.order7.offset + (base : ℝ) + (credit : ℝ) +
    (∑ j : Fin 4, (PinnedInterface.credit j : ℝ)) - (right 320 : ℝ))
def bernsteinPolynomial : UniPoly :=
  ∑ k : Fin 14, C (PrefixData.beta k : ℝ) * C (Nat.choose 13 k.val : ℝ) *
    X ()^k.val * (1-X ())^(13-k.val)

/-- A single fixed degree-13 identity and coefficient signs, not an endpoint
inequality along arbitrary physical trajectories. -/
structure EndpointChecks : Prop where
  gap : base < right 320
  cap : right 320 ≤ 733/250
  identity : endpointPolynomial = bernsteinPolynomial
  positive : ∀ k, 0 < PrefixData.beta k

theorem endpoint_positive (h : EndpointChecks) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < eval (fun _ => t) endpointPolynomial := by
  rw [h.identity]
  have hp := bernsteinSum_pos 13 PrefixData.beta h.positive ⟨t, ht⟩
  rw [bernsteinSum_eval] at hp
  simpa [bernsteinPolynomial, bernstein_apply, mul_assoc] using hp

/-- Physical endpoint reduction is proved, not included in EndpointChecks. -/
theorem endpoint_value (h : EndpointChecks) (γ : ActivePulse) :
    eval (fun _ => (γ.exposure-base)/(right 320-base)) endpointPolynomial =
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S)
      (Pinned.order7.potential 4) - evalCell 0 (γ.traj 0) (Pinned.order7.potential 0) +
      (credit : ℝ) + (∑ j : Fin 4, (PinnedInterface.credit j : ℝ)) - (right 320 : ℝ) := by
  have hn : (right 320 : ℝ) - base ≠ 0 := ne_of_gt (sub_pos.mpr (Rat.cast_lt.mpr h.gap))
  have he : eval (fun _ => (γ.exposure-base)/(right 320-base)) exposurePolynomial = γ.exposure := by
    simp only [exposurePolynomial, map_add, map_mul, eval_C, eval_X]
    field_simp; ring
  have hx : eval (fun _ => (γ.exposure-base)/(right 320-base)) xiPolynomial =
      cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S := by
    simp only [xiPolynomial, map_sub, map_mul, eval_C, he]
    simp [cellXi, γ.cumI_S, ExposurePartition.width, Pinned.partition]
    ring
  have hterm : γ.traj γ.S ∈ XCZ := by
    rw [γ.traj_eq ⟨γ.S_nonneg, le_rfl⟩]; exact γ.terminal
  have hinit : γ.traj 0 = x0 := γ.traj_zero
  have obj : -Pinned.order7.offset - evalCell 0 x0 (Pinned.order7.potential 0) = (base : ℝ) := by
    rw [Pinned.order7_objective]; norm_num [Pinned.order7, base]
  have hs (p : UniPoly) :
      eval (fun _ => (γ.exposure-base)/(right 320-base)) (aeval (fun _ : Unit => xiPolynomial) p) =
      eval (fun _ => cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp, hx]
  simp only [endpointPolynomial, map_add, eval_C, hs]
  rw [terminalRestriction_on_orbit _ (Pinned.order7_invariant 4) _ hterm, hinit]
  linarith

/-- No final-profile traversal is assumed: the base bound supplies all the
credits used in this contradiction. The two omitted profiles contribute zero. -/
theorem threshold (hl : LayoutChecks) (he : EndpointChecks) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    (hi : PinnedInterface.NumericalChecks) (γ : ActivePulse) :
    (right 320 : ℝ) ≤ γ.exposure := by
  have hL : (base : ℝ) ≤ γ.exposure := by
    have hb := EReal.coe_le_coe_iff.mp
      ((Pinned.order7_checks_of_grams A hm).active_lower.trans (iInf_le _ γ))
    simpa only [Pinned.order7, base, Rat.cast_div, Rat.cast_ofNat] using hb
  by_contra hn
  have hB : γ.exposure ≤ (right 320 : ℝ) := (lt_of_not_ge hn).le
  have hcap : γ.exposure ≤ 733/250 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hB.trans (Rat.cast_le.mpr he.cap)
  obtain ⟨s⟩ := crossings_exist γ (by simpa [base] using hL)
  have hp := prefix_credit hl hc ha hr A hm s hL hcap
  have ht := PinnedInterface.credited_telescope hi s hcap
  have hg : (0 : ℝ) < right 320 - base := sub_pos.mpr (Rat.cast_lt.mpr he.gap)
  have hpos := endpoint_positive he ((γ.exposure-base)/(right 320-base))
    ⟨div_nonneg (sub_nonneg.mpr hL) hg.le,
      (div_le_one hg).mpr (sub_le_sub_right hB _)⟩
  rw [endpoint_value he γ] at hpos
  linarith

theorem traversal (hl : LayoutChecks) (he : EndpointChecks) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    (hi : PinnedInterface.NumericalChecks) {γ : ActivePulse} (s : Crossings γ) :
    Nonempty (Traversal γ s) :=
  traversal_exists hl.full s (threshold hl he hc ha hr A hm hi γ)

/-- Full occupation/interface accounting with neither traversal nor local
trajectory inequalities supplied by the caller. -/
theorem credited_telescope (hl : LayoutChecks) (he : EndpointChecks)
    (hc : OccupationCoverage.DataChecks) (ha : PinnedAllocation.NumericalChecks)
    (hr : PinnedRegion.NumericalChecks) (A : GramBridge.Archive Pinned.order7)
    (hm : GramBridge.MatrixChecks A) (hi : PinnedInterface.NumericalChecks)
    {γ : ActivePulse} (hcap : γ.exposure ≤ 733/250) :
    (totalCredit : ℝ) + (∑ j : Fin 4, (PinnedInterface.credit j : ℝ)) +
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S)
      (Pinned.order7.potential 4) -
    evalCell 0 (γ.traj 0) (Pinned.order7.potential 0) ≤ γ.exposure := by
  obtain ⟨s⟩ := crossings_exist_of_grams A hm γ
  obtain ⟨a⟩ := traversal hl he hc ha hr A hm hi s
  exact OccupationCoverage.credited_telescope hc ha hr A hm hi s hcap a

end LowerBoundCZ.Certification.MandatoryPrefix
