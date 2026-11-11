import RequestProject.AppendixE.ExcursionGaps

/-!
# Axiom audit: chronological discarded gaps

Expected: all results use only `[propext, Classical.choice, Quot.sound]`.
No additional geometric or analytical axiom is introduced.

Edge checks below: an empty retained selection leaves the single gap
`[0,T]`, and a degenerate gap (`gapLeft = gapRight`, e.g. between
touching retained intervals) has empty interior and zero phase
increment.
-/

open CZExposure

#check @FiniteExcursionSelection.start_injective
#check @FiniteExcursionSelection.exists_chronologicalOrder
#check @FiniteExcursionSelection.chronologicalOrder
#check @FiniteExcursionSelection.chronologicalOrder_strictMono
#check @FiniteExcursionSelection.orderedSegment
#check @FiniteExcursionSelection.orderedSegment_separated
#check @FiniteExcursionSelection.gapLeft
#check @FiniteExcursionSelection.gapRight
#check @FiniteExcursionSelection.gapLeft_zero
#check @FiniteExcursionSelection.gapLeft_succ
#check @FiniteExcursionSelection.gapRight_last
#check @FiniteExcursionSelection.gapRight_castSucc
#check @FiniteExcursionSelection.gap_valid
#check @FiniteExcursionSelection.gap_ordered
#check @FiniteExcursionSelection.gap_pairwiseDisjoint
#check @FiniteExcursionSelection.gap_subset_discardedTimes
#check @FiniteExcursionSelection.iUnion_closed_gaps
#check @FiniteExcursionSelection.iUnion_open_gaps_ae
#check @FiniteExcursionSelection.cost_lt_on_gap
#check @FiniteExcursionSelection.chronological_gap_phase_accounting

/-- Empty selection: the unique gap is `[0,T]` and every time is
discarded. -/
example {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
    (S : FiniteExcursionSelection T α β y u) (h0 : S.count = 0) :
    S.gapLeft 0 = 0 ∧ S.gapRight 0 = T ∧
      S.discardedTimes = Set.Icc 0 T := by
  refine ⟨S.gapLeft_zero, ?_, ?_⟩
  · have hlast : (0 : Fin (S.count + 1)) = Fin.last S.count :=
      Fin.ext (by simp [h0])
    rw [hlast]
    exact S.gapRight_last
  · have hempty : (⋃ i, Set.Ioo (S.segment i).a (S.segment i).b) = ∅ := by
      apply Set.iUnion_eq_empty.mpr
      intro i
      exfalso
      have := i.isLt
      omega
    rw [FiniteExcursionSelection.discardedTimes, hempty, Set.diff_empty]

/-- A degenerate gap has empty open interior and zero phase increment. -/
example {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
    (S : FiniteExcursionSelection T α β y u) (j : Fin (S.count + 1))
    (hd : S.gapLeft j = S.gapRight j) :
    Set.Ioo (S.gapLeft j) (S.gapRight j) = ∅ ∧
      exposurePhaseIncrement y u (S.gapLeft j) (S.gapRight j) = 0 := by
  rw [hd]
  exact ⟨Set.Ioo_self _, by simp [exposurePhaseIncrement]⟩

#print axioms FiniteExcursionSelection.start_injective
#print axioms FiniteExcursionSelection.exists_chronologicalOrder
#print axioms FiniteExcursionSelection.chronologicalOrder
#print axioms FiniteExcursionSelection.chronologicalOrder_strictMono
#print axioms FiniteExcursionSelection.orderedSegment
#print axioms FiniteExcursionSelection.orderedSegment_separated
#print axioms FiniteExcursionSelection.gapLeft
#print axioms FiniteExcursionSelection.gapRight
#print axioms FiniteExcursionSelection.gapLeft_zero
#print axioms FiniteExcursionSelection.gapLeft_succ
#print axioms FiniteExcursionSelection.gapRight_last
#print axioms FiniteExcursionSelection.gapRight_castSucc
#print axioms FiniteExcursionSelection.gap_valid
#print axioms FiniteExcursionSelection.gap_ordered
#print axioms FiniteExcursionSelection.gap_pairwiseDisjoint
#print axioms FiniteExcursionSelection.gap_subset_discardedTimes
#print axioms FiniteExcursionSelection.iUnion_closed_gaps
#print axioms FiniteExcursionSelection.iUnion_open_gaps_ae
#print axioms FiniteExcursionSelection.cost_lt_on_gap
#print axioms FiniteExcursionSelection.chronological_gap_phase_accounting
