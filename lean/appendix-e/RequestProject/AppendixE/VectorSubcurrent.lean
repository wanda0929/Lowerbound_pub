module
public import RequestProject.AppendixE.VectorMeasureBounds
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Vector-measure subcurrents (Appendix E support)

The analogue of Paolini–Stepanov's subcurrent relation (arXiv:1303.5664,
Def. 3.1: `S ≤ T` iff `M(T - S) + M(S) ≤ M(T)`; Remark 3.2 notes equality
holds by the triangle inequality; Remark 3.3 gives transitivity; Remark 3.5
localizes the condition to Borel sets under finite mass) for vector measures:
variation `‖T‖` plays the role of mass.  We prove pointwise
`‖T s‖ₑ ≤ |T| s`, the variation triangle inequality, and — under finite total
variation — the localized identity `|T - S| + |S| = |T|` and domination
`|S| ≤ |T|` consequences.  No normal-current correspondence, arc
decomposition, or acyclicity is asserted.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem vectorMeasure_enorm_le_variation (T : VectorMeasure X E)
    {s : Set X} (hs : MeasurableSet s) : ‖T s‖ₑ ≤ T.variation s := by
  by_cases h0 : s = ∅
  · simp [h0]
  have hne : (⟨s, hs⟩ : Subtype MeasurableSet) ≠ ⊥ := by
    intro h
    apply h0
    have h' := congrArg Subtype.val h
    simp at h'
    exact h'
  show ‖T s‖ₑ ≤
    (MeasureTheory.ennrealPreVariation (‖T ·‖ₑ) _ _).ennrealToMeasure s
  rw [VectorMeasure.ennrealToMeasure_apply hs]
  show ‖T s‖ₑ ≤ MeasureTheory.preVariationFun (‖T ·‖ₑ) s
  rw [MeasureTheory.preVariationFun, dif_pos hs]
  have hpart : (Finpartition.indiscrete hne).parts =
      ({⟨s, hs⟩} : Finset (Subtype MeasurableSet)) := rfl
  refine le_iSup_of_le (Finpartition.indiscrete hne) ?_
  rw [hpart, Finset.sum_singleton]

theorem vectorMeasure_variation_zero :
    (0 : VectorMeasure X E).variation = 0 := by
  apply le_antisymm _ (Measure.le_iff.mpr fun s _ => zero_le _)
  exact vectorMeasure_variation_le_of_bound 0 0 (by simp)

theorem vectorMeasure_variation_add_le (S T : VectorMeasure X E) :
    (S + T).variation ≤ S.variation + T.variation := by
  refine vectorMeasure_variation_le_of_bound (S + T)
    (S.variation + T.variation) ?_
  intro s hs
  calc ‖(S + T) s‖ₑ ≤ ‖S s‖ₑ + ‖T s‖ₑ := by
        rw [VectorMeasure.add_apply]
        exact enorm_add_le _ _
    _ ≤ S.variation s + T.variation s :=
        add_le_add (vectorMeasure_enorm_le_variation S hs)
          (vectorMeasure_enorm_le_variation T hs)
    _ = (S.variation + T.variation) s := (Measure.add_apply _ _ _).symm

theorem vectorMeasure_variation_eq_zero_iff (T : VectorMeasure X E) :
    T.variation = 0 ↔ T = 0 := by
  constructor
  · intro h
    ext s
    by_cases hs : MeasurableSet s
    · have hle := vectorMeasure_enorm_le_variation T hs
      rw [h] at hle
      have : ‖T s‖ₑ = 0 := le_antisymm hle (zero_le _)
      exact enorm_eq_zero.mp this
    · exact T.not_measurable hs
  · intro h
    rw [h, vectorMeasure_variation_zero]

/-- Vector-measure version of PS Def. 3.1: `S` is a subcurrent of `T` when
`M(T - S) + M(S) ≤ M(T)`.  The global inequality alone does not enforce
localization when `T` has infinite mass. -/
def IsVectorSubcurrent (S T : VectorMeasure X E) : Prop :=
  (T - S).variation Set.univ + S.variation Set.univ ≤ T.variation Set.univ

namespace IsVectorSubcurrent

theorem refl (T : VectorMeasure X E) : IsVectorSubcurrent T T := by
  simp [IsVectorSubcurrent, sub_self, vectorMeasure_variation_zero]

theorem zero (T : VectorMeasure X E) : IsVectorSubcurrent 0 T := by
  simp [IsVectorSubcurrent, sub_zero, vectorMeasure_variation_zero]

theorem complement {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) : IsVectorSubcurrent (T - S) T := by
  rw [IsVectorSubcurrent, sub_sub_self, add_comm]
  exact hST

theorem trans {R S T : VectorMeasure X E}
    (hRS : IsVectorSubcurrent R S) (hST : IsVectorSubcurrent S T) :
    IsVectorSubcurrent R T := by
  have e : T - R = (T - S) + (S - R) := (sub_add_sub_cancel T S R).symm
  calc (T - R).variation Set.univ + R.variation Set.univ
      = ((T - S) + (S - R)).variation Set.univ + R.variation Set.univ := by
        rw [e]
    _ ≤ ((T - S).variation Set.univ + (S - R).variation Set.univ) +
          R.variation Set.univ := by
        have h := (vectorMeasure_variation_add_le (T - S) (S - R)) Set.univ
        rw [Measure.add_apply] at h
        exact add_le_add h le_rfl
    _ = (T - S).variation Set.univ +
          ((S - R).variation Set.univ + R.variation Set.univ) :=
        add_assoc _ _ _
    _ ≤ (T - S).variation Set.univ + S.variation Set.univ :=
        add_le_add le_rfl hRS
    _ ≤ T.variation Set.univ := hST

theorem totalMass_eq {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) :
    (T - S).variation Set.univ + S.variation Set.univ =
      T.variation Set.univ := by
  apply le_antisymm hST
  have h := (vectorMeasure_variation_add_le (T - S) S) Set.univ
  rwa [sub_add_cancel, Measure.add_apply] at h

theorem variation_add_eq {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) (hT : T.variation Set.univ < ⊤) :
    (T - S).variation + S.variation = T.variation := by
  haveI : IsFiniteMeasure T.variation := ⟨hT⟩
  have hle : T.variation ≤ (T - S).variation + S.variation := by
    have h := vectorMeasure_variation_add_le (T - S) S
    rwa [sub_add_cancel] at h
  have huniv : T.variation Set.univ =
      ((T - S).variation + S.variation) Set.univ := by
    rw [Measure.add_apply]
    exact hST.totalMass_eq.symm
  exact (Measure.eq_of_le_of_measure_univ_eq hle huniv).symm

theorem variation_le {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) (hT : T.variation Set.univ < ⊤) :
    S.variation ≤ T.variation :=
  calc S.variation ≤ (T - S).variation + S.variation := by
        rw [Measure.le_iff]
        intro s _
        rw [Measure.add_apply]
        exact le_add_left le_rfl
    _ = T.variation := hST.variation_add_eq hT

theorem variation_univ_lt_top {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) (hT : T.variation Set.univ < ⊤) :
    S.variation Set.univ < ⊤ :=
  lt_of_le_of_lt ((hST.variation_le hT) Set.univ) hT

theorem variation_null {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) (hT : T.variation Set.univ < ⊤)
    {s : Set X} (hs : T.variation s = 0) : S.variation s = 0 :=
  le_antisymm (((hST.variation_le hT) s).trans hs.le) (zero_le _)

theorem antisymm {S T : VectorMeasure X E}
    (hST : IsVectorSubcurrent S T) (hTS : IsVectorSubcurrent T S)
    (hT : T.variation Set.univ < ⊤) : S = T := by
  have hSfin : S.variation Set.univ < ⊤ := hST.variation_univ_lt_top hT
  have hvarEq : S.variation = T.variation :=
    le_antisymm (hST.variation_le hT) (hTS.variation_le hSfin)
  have hlocal := hST.variation_add_eq hT
  haveI : IsFiniteMeasure S.variation := ⟨hSfin⟩
  have h'' : (T - S).variation + S.variation = S.variation :=
    hlocal.trans hvarEq.symm
  have h' : S.variation + (T - S).variation ≤ S.variation + 0 :=
    le_of_eq (by rw [add_comm, h'', add_zero])
  have h0 : (T - S).variation = 0 :=
    le_antisymm (Measure.le_of_add_le_add_left h')
      (Measure.le_iff.mpr fun s _ => zero_le _)
  have hTS0 : T - S = 0 := (vectorMeasure_variation_eq_zero_iff (T - S)).mp h0
  exact (sub_eq_zero.mp hTS0).symm

end IsVectorSubcurrent

end CZExposure
