module
public import RequestProject.AppendixE.LowCostPhase
public import Mathlib.Data.Finset.Sort

/-!
# Chronological discarded gaps

`FiniteExcursionSelection` retains finitely many open intervals with
pairwise-disjoint interiors inside `[0,T]`. Their start times are
injective, so sorting them yields a chronological order; the `N+1`
complementary gaps — before the first, between consecutive, and after
the last retained interval — then form an ordered valid gap family:
their closed intervals cover `discardedTimes` exactly, and their open
interiors are pairwise disjoint and cover it almost everywhere. `T = 0`,
an empty selection, touching retained intervals, and zero-length gaps
are all allowed.

`chronological_gap_phase_accounting` instantiates the low-cost phase
accounting with this constructed family, so the gap cover is no longer
an input hypothesis.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

namespace FiniteExcursionSelection

variable {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
variable (S : FiniteExcursionSelection T α β y u)

/-- Retained intervals have distinct start times: equal starts would
make the disjoint nondegenerate interiors overlap. -/
theorem start_injective : Function.Injective (fun i => (S.segment i).a) := by
  intro i j hij
  have hae : (S.segment i).a = (S.segment j).a := hij
  by_contra hne
  have hm : (S.segment i).a < min (S.segment i).b (S.segment j).b :=
    lt_min (S.segment i).a_lt_b (hae ▸ (S.segment j).a_lt_b)
  have hlt : (S.segment i).a <
      ((S.segment i).a + min (S.segment i).b (S.segment j).b) / 2 := by
    linarith
  have hrx : ((S.segment i).a + min (S.segment i).b (S.segment j).b) / 2 <
      min (S.segment i).b (S.segment j).b := by
    linarith
  have hxi : _ ∈ Set.Ioo (S.segment i).a (S.segment i).b :=
    ⟨hlt, hrx.trans_le (min_le_left _ _)⟩
  have hxj : _ ∈ Set.Ioo (S.segment j).a (S.segment j).b :=
    ⟨hae ▸ hlt, hrx.trans_le (min_le_right _ _)⟩
  exact (Set.disjoint_left.mp (S.disjoint hne) hxi) hxj

/-- The retained segments can be permuted into chronological order. -/
theorem exists_chronologicalOrder :
    ∃ e : Equiv.Perm (Fin S.count),
      StrictMono (fun i => (S.segment (e i)).a) := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun i => (S.segment i).a)
  have hc : s.card = S.count := by
    dsimp only [s]
    rw [Finset.card_image_of_injective _ S.start_injective,
      Finset.card_univ, Fintype.card_fin]
  let e0 : Fin S.count ≃ s := Equiv.ofBijective
    (fun i => ⟨(S.segment i).a,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => S.start_injective (congrArg Subtype.val h),
     fun x => by
       obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
       exact ⟨i, Subtype.ext hi⟩⟩
  have key : ∀ i : Fin S.count,
      (S.segment ((s.orderIsoOfFin hc).toEquiv.trans e0.symm i)).a =
        s.orderEmbOfFin hc i := fun i =>
    congrArg Subtype.val (e0.apply_symm_apply (s.orderIsoOfFin hc i))
  refine ⟨(s.orderIsoOfFin hc).toEquiv.trans e0.symm, ?_⟩
  have hfun :
      (fun i => (S.segment ((s.orderIsoOfFin hc).toEquiv.trans e0.symm i)).a) =
        fun i => s.orderEmbOfFin hc i := funext key
  rw [hfun]
  exact (s.orderEmbOfFin hc).strictMono

/-- A permutation of the retained indices ordering segments by start
time. -/
def chronologicalOrder : Equiv.Perm (Fin S.count) :=
  Classical.choose S.exists_chronologicalOrder

theorem chronologicalOrder_strictMono :
    StrictMono (fun i => (S.segment (S.chronologicalOrder i)).a) :=
  Classical.choose_spec S.exists_chronologicalOrder

/-- The `i`-th retained segment in chronological order. -/
def orderedSegment (i : Fin S.count) : PositiveExposureSegment :=
  S.segment (S.chronologicalOrder i)

theorem orderedSegment_separated {i j : Fin S.count} (hij : i < j) :
    (S.orderedSegment i).b ≤ (S.orderedSegment j).a :=
  S.right_le_left_of_start_lt (S.chronologicalOrder_strictMono hij)

/-- Chronological left endpoints are monotone. -/
private theorem orderedSegment_a_le_of_le {i j : Fin S.count} (h : i ≤ j) :
    (S.orderedSegment i).a ≤ (S.orderedSegment j).a :=
  S.chronologicalOrder_strictMono.monotone h

/-- Chronological right endpoints are monotone. -/
private theorem orderedSegment_b_le_of_le {i j : Fin S.count} (h : i ≤ j) :
    (S.orderedSegment i).b ≤ (S.orderedSegment j).b := by
  rcases lt_or_eq_of_le h with h1 | h1
  · exact (S.orderedSegment_separated h1).trans
      (S.orderedSegment j).a_lt_b.le
  · obtain rfl := h1
    exact le_rfl

/-- Left endpoint of the `j`-th discarded gap: `0` before the first
retained segment, otherwise the previous segment's right endpoint. -/
def gapLeft : Fin (S.count + 1) → ℝ :=
  Fin.cases (motive := fun _ => ℝ) 0 (fun i => (S.orderedSegment i).b)

/-- Right endpoint of the `j`-th discarded gap: `T` after the last
retained segment, otherwise the next segment's left endpoint. -/
def gapRight : Fin (S.count + 1) → ℝ :=
  Fin.lastCases (motive := fun _ => ℝ) T (fun i => (S.orderedSegment i).a)

@[simp] theorem gapLeft_zero : S.gapLeft 0 = 0 :=
  Fin.cases_zero

@[simp] theorem gapLeft_succ (i : Fin S.count) :
    S.gapLeft i.succ = (S.orderedSegment i).b :=
  Fin.cases_succ i

@[simp] theorem gapRight_last : S.gapRight (Fin.last S.count) = T :=
  Fin.lastCases_last

@[simp] theorem gapRight_castSucc (i : Fin S.count) :
    S.gapRight i.castSucc = (S.orderedSegment i).a :=
  Fin.lastCases_castSucc i

/-- `0 ≤ gapRight j`: every gap right endpoint lies in `[0,T]`. -/
private theorem gapRight_nonneg (hT : 0 ≤ T) (j : Fin (S.count + 1)) :
    0 ≤ S.gapRight j := by
  induction j using Fin.lastCases with
  | last => rw [S.gapRight_last]; exact hT
  | cast k =>
      rw [S.gapRight_castSucc]
      exact (S.bounds (S.chronologicalOrder k)).1

/-- `gapRight j ≤ T`. -/
private theorem gapRight_le_T (j : Fin (S.count + 1)) :
    S.gapRight j ≤ T := by
  induction j using Fin.lastCases with
  | last => rw [S.gapRight_last]
  | cast k =>
      rw [S.gapRight_castSucc]
      exact (S.orderedSegment k).a_lt_b.le.trans
        (S.bounds (S.chronologicalOrder k)).2

theorem gap_valid (hT : 0 ≤ T) (j : Fin (S.count + 1)) :
    0 ≤ S.gapLeft j ∧ S.gapLeft j ≤ S.gapRight j ∧ S.gapRight j ≤ T := by
  induction j using Fin.cases with
  | zero =>
      rw [S.gapLeft_zero]
      exact ⟨le_rfl, S.gapRight_nonneg hT 0, S.gapRight_le_T 0⟩
  | succ i =>
      refine ⟨?_, ?_, ?_⟩
      · rw [S.gapLeft_succ]
        exact (S.bounds (S.chronologicalOrder i)).1.trans
          (S.orderedSegment i).a_lt_b.le
      · rw [S.gapLeft_succ]
        rcases Fin.eq_castSucc_or_eq_last i.succ with ⟨i', hi'⟩ | hi'
        · rw [hi', S.gapRight_castSucc]
          have hlt : i < i' := by
            have hv := congrArg Fin.val hi'
            rw [Fin.val_succ, Fin.val_castSucc] at hv
            exact Fin.lt_def.mpr (show i.val < i'.val by omega)
          exact S.orderedSegment_separated hlt
        · rw [hi', S.gapRight_last]
          exact (S.bounds (S.chronologicalOrder i)).2
      · rcases Fin.eq_castSucc_or_eq_last i.succ with ⟨i', hi'⟩ | hi'
        · rw [hi', S.gapRight_castSucc]
          exact (S.orderedSegment i').a_lt_b.le.trans
            (S.bounds (S.chronologicalOrder i')).2
        · rw [hi', S.gapRight_last]

/-- The `i`-th ordered segment ends no later than gap `j` starts when
`i.val < j.val`. -/
private theorem orderedSegment_b_le_gapLeft {i : Fin S.count}
    {j : Fin (S.count + 1)} (h : i.val < j.val) :
    (S.orderedSegment i).b ≤ S.gapLeft j := by
  have hj0 : j.val - 1 < S.count := by have := j.isLt; omega
  have hjeq : j = (⟨j.val - 1, hj0⟩ : Fin S.count).succ :=
    Fin.ext (show j.val = j.val - 1 + 1 by omega)
  rw [hjeq, S.gapLeft_succ]
  exact S.orderedSegment_b_le_of_le
    (Fin.le_def.mpr (show i.val ≤ j.val - 1 by omega))

/-- Gap `j` ends no later than the `i`-th ordered segment starts when
`j.val ≤ i.val`. -/
private theorem gapRight_le_orderedSegment_a {i : Fin S.count}
    {j : Fin (S.count + 1)} (h : j.val ≤ i.val) :
    S.gapRight j ≤ (S.orderedSegment i).a := by
  have hj : j.val < S.count := h.trans_lt i.isLt
  have hjeq : j = (⟨j.val, hj⟩ : Fin S.count).castSucc := Fin.ext rfl
  rw [hjeq, S.gapRight_castSucc]
  exact S.orderedSegment_a_le_of_le (Fin.le_def.mpr h)

theorem gap_ordered {i j : Fin (S.count + 1)} (hij : i < j) :
    S.gapRight i ≤ S.gapLeft j := by
  have hlt : i.val < j.val := Fin.lt_def.mp hij
  have hi_lt : i.val < S.count := by have := j.isLt; omega
  have hj_lt : j.val - 1 < S.count := by have := j.isLt; omega
  have hieq : i = (⟨i.val, hi_lt⟩ : Fin S.count).castSucc := Fin.ext rfl
  have hjeq : j = (⟨j.val - 1, hj_lt⟩ : Fin S.count).succ :=
    Fin.ext (show j.val = j.val - 1 + 1 by omega)
  rw [hieq, S.gapRight_castSucc, hjeq, S.gapLeft_succ]
  exact (S.orderedSegment_a_le_of_le
    (Fin.le_def.mpr (show i.val ≤ j.val - 1 by omega))).trans
      (S.orderedSegment _).a_lt_b.le

/-- Distinct gaps are separated by a retained interval, so their open
interiors are disjoint. -/
private theorem gap_disjoint_of_lt {i j : Fin (S.count + 1)} (h : i < j) :
    Disjoint (Set.Ioo (S.gapLeft i) (S.gapRight i))
      (Set.Ioo (S.gapLeft j) (S.gapRight j)) := by
  rw [Set.disjoint_left]
  rintro t ⟨-, htr⟩ ⟨htl, -⟩
  exact (not_lt_of_gt htl) (htr.trans_le (S.gap_ordered h))

theorem gap_pairwiseDisjoint : Pairwise (fun i j =>
    Disjoint (Set.Ioo (S.gapLeft i) (S.gapRight i))
      (Set.Ioo (S.gapLeft j) (S.gapRight j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact S.gap_disjoint_of_lt h
  · exact (S.gap_disjoint_of_lt h).symm

theorem gap_subset_discardedTimes (hT : 0 ≤ T) (j : Fin (S.count + 1)) :
    Set.Icc (S.gapLeft j) (S.gapRight j) ⊆ S.discardedTimes := by
  intro t ht
  rw [S.mem_discardedTimes_iff]
  refine ⟨⟨(S.gap_valid hT j).1.trans ht.1,
    ht.2.trans (S.gap_valid hT j).2.2⟩, ?_⟩
  intro i hti
  have hk : S.orderedSegment (S.chronologicalOrder.symm i) = S.segment i :=
    congrArg S.segment (S.chronologicalOrder.apply_symm_apply i)
  rcases lt_or_ge (S.chronologicalOrder.symm i).val j.val with h | h
  · have hb := S.orderedSegment_b_le_gapLeft h
    rw [hk] at hb
    exact (not_lt_of_ge (hb.trans ht.1)) hti.2
  · have ha := S.gapRight_le_orderedSegment_a h
    rw [hk] at ha
    exact (not_lt_of_ge (ht.2.trans ha)) hti.1

theorem iUnion_closed_gaps (hT : 0 ≤ T) :
    (⋃ j, Set.Icc (S.gapLeft j) (S.gapRight j)) = S.discardedTimes := by
  classical
  refine Set.Subset.antisymm
    (Set.iUnion_subset fun j => S.gap_subset_discardedTimes hT j) ?_
  intro t ht
  rw [S.mem_discardedTimes_iff] at ht
  obtain ⟨htT, hout⟩ := ht
  let G : Finset (Fin (S.count + 1)) :=
    Finset.univ.filter fun j => t ≤ S.gapRight j
  have hG : G.Nonempty := ⟨Fin.last S.count,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [S.gapRight_last]; exact htT.2⟩⟩
  have key : ∀ j ∈ G, (∀ k ∈ G, j ≤ k) → S.gapLeft j ≤ t := by
    intro j hjG hjmin
    induction j using Fin.cases with
    | zero =>
        rw [S.gapLeft_zero]
        exact htT.1
    | succ i =>
        rw [S.gapLeft_succ]
        have hlt : i.castSucc < i.succ := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
          exact Nat.lt_succ_self _
        have hnotmem : i.castSucc ∉ G := fun hk =>
          absurd (hjmin _ hk) (not_le_of_gt hlt)
        have hnot : ¬ t ≤ S.gapRight i.castSucc := fun hle =>
          hnotmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
        have hgt : (S.orderedSegment i).a < t := by
          have h1 : S.gapRight i.castSucc < t := not_le.mp hnot
          rwa [S.gapRight_castSucc] at h1
        have hni := hout (S.chronologicalOrder i)
        rw [Set.mem_Ioo, not_and] at hni
        exact not_lt.mp (hni hgt)
  have hmem : G.min' hG ∈ G := G.min'_mem hG
  exact Set.mem_iUnion.mpr ⟨G.min' hG,
    ⟨key _ hmem fun k hk => G.min'_le _ hk,
     (Finset.mem_filter.mp hmem).2⟩⟩

theorem iUnion_open_gaps_ae (hT : 0 ≤ T) :
    (⋃ j, Set.Ioo (S.gapLeft j) (S.gapRight j)) =ᵐ[volume]
      S.discardedTimes := by
  have hpt : ∀ᵐ t ∂volume,
      (t ∈ ⋃ j, Set.Ioo (S.gapLeft j) (S.gapRight j)) ↔
        t ∈ ⋃ j, Set.Icc (S.gapLeft j) (S.gapRight j) := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr
      (fun j : Fin (S.count + 1) =>
        (Filter.eventuallyEq_set.mp
          (Ioo_ae_eq_Icc (a := S.gapLeft j) (b := S.gapRight j)) :
          ∀ᵐ t ∂volume, t ∈ Set.Ioo (S.gapLeft j) (S.gapRight j) ↔
            t ∈ Set.Icc (S.gapLeft j) (S.gapRight j)))] with t ht
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (ht j).mp hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (ht j).mpr hj⟩
  exact (Filter.eventuallyEq_set.mpr hpt).trans
    (Filter.EventuallyEq.of_eq (S.iUnion_closed_gaps hT))

theorem cost_lt_on_gap (hT : 0 ≤ T) (j : Fin (S.count + 1))
    {t : ℝ} (ht : t ∈ Set.Icc (S.gapLeft j) (S.gapRight j)) :
    euclideanExposureCost (y t) < β :=
  S.cost_lt_on_discarded (S.gap_subset_discardedTimes hT j ht)

/-- The chronological gaps discharge the supplied-cover hypotheses of the
phase theorem: signed sum and endpoint-ratio product equal the discarded
angular integral and its phase factor, with `8T√β` bounds. -/
theorem chronological_gap_phase_accounting {K : NNReal}
    (hT : 0 ≤ T) (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hβ : β ≤ 1/12) :
    (∑ j, |exposurePhaseIncrement y u (S.gapLeft j) (S.gapRight j)|) ≤
      8 * T * Real.sqrt β ∧
    (∑ j, exposurePhaseIncrement y u (S.gapLeft j) (S.gapRight j)) =
      S.discardedAngularIntegral ∧
    (∏ j, complexUnitPhase (exposureProgressPath y (S.gapRight j)) /
        complexUnitPhase (exposureProgressPath y (S.gapLeft j))) =
      phaseFactor S.discardedAngularIntegral ∧
    |S.discardedAngularIntegral| ≤ 8 * T * Real.sqrt β ∧
    ‖(∏ j, complexUnitPhase (exposureProgressPath y (S.gapRight j)) /
        complexUnitPhase (exposureProgressPath y (S.gapLeft j))) - 1‖ ≤
      8 * T * Real.sqrt β := by
  have hvalid : ∀ j ∈ (Finset.univ : Finset (Fin (S.count + 1))),
      0 ≤ S.gapLeft j ∧ S.gapLeft j ≤ S.gapRight j ∧ S.gapRight j ≤ T :=
    fun j _ => S.gap_valid hT j
  have hdisj :
      (↑(Finset.univ : Finset (Fin (S.count + 1))) :
        Set (Fin (S.count + 1))).PairwiseDisjoint
        (fun j => Set.Ioo (S.gapLeft j) (S.gapRight j)) :=
    fun i _ j _ hij => S.gap_pairwiseDisjoint hij
  have hlow : ∀ j ∈ (Finset.univ : Finset (Fin (S.count + 1))),
      ∀ t ∈ Set.Icc (S.gapLeft j) (S.gapRight j),
        euclideanExposureCost (y t) ≤ β :=
    fun j _ t ht => (S.cost_lt_on_gap hT j ht).le
  have hcover : (⋃ j ∈ (Finset.univ : Finset (Fin (S.count + 1))),
      Set.Ioo (S.gapLeft j) (S.gapRight j)) =ᵐ[volume]
        S.discardedTimes := by
    simpa using S.iUnion_open_gaps_ae hT
  obtain ⟨habs, -, -, -, -⟩ := finite_low_cost_phase_accounting
    (Finset.univ : Finset (Fin (S.count + 1))) S.gapLeft S.gapRight
    hT hy hu hub hdom hode hβ hvalid hdisj hlow
  obtain ⟨gsum, gprod, gbound, gerr⟩ :=
    S.discarded_phase_product_of_gap_cover
      (Finset.univ : Finset (Fin (S.count + 1))) S.gapLeft S.gapRight
      hT hy hu hub hdom hode hβ hvalid hdisj
      (fun j _ => S.gap_subset_discardedTimes hT j) hcover
  exact ⟨habs, gsum, gprod, gbound, gerr⟩

end FiniteExcursionSelection

end CZExposure
