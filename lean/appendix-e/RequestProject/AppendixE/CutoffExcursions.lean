module
public import Mathlib

/-!
# Cutoff excursions of a continuous cost function

For continuous `c` with `c 0 ≤ α` and `c T ≤ α`, every `t ∈ [0,T]` with
`c t > α` lies in a unique interval whose endpoints have cost `α` and
whose interior stays strictly above `α`: the left endpoint is the last
sublevel point before `t` and the right endpoint is the first sublevel
point after it.  Compactness supplies the extrema and the intermediate
value theorem pins the endpoint costs to `α`.  Distinct such intervals
have disjoint interiors.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open Set

/-- A cutoff interval: endpoints in `[0,T]` at cost `α`, interior
strictly above `α`. -/
structure IsCutoffExcursion (c : ℝ → ℝ) (T α : ℝ) (I : ℝ × ℝ) : Prop where
  left_nonneg : 0 ≤ I.1
  nondegenerate : I.1 < I.2
  right_le : I.2 ≤ T
  cost_left : c I.1 = α
  cost_right : c I.2 = α
  above : ∀ t ∈ Set.Ioo I.1 I.2, α < c t

/-- The endpoint pairs whose cutoff interval reaches `β`. -/
def retainedExcursionSet (c : ℝ → ℝ) (T α β : ℝ) : Set (ℝ × ℝ) :=
  {I | IsCutoffExcursion c T α I ∧
    ∃ p ∈ Set.Ioo I.1 I.2, β ≤ c p}

namespace IsCutoffExcursion

variable {c : ℝ → ℝ} {T α : ℝ} {I J : ℝ × ℝ}

theorem cost_ge (hI : IsCutoffExcursion c T α I)
    {t : ℝ} (ht : t ∈ Set.Icc I.1 I.2) : α ≤ c t := by
  rcases lt_or_eq_of_le ht.1 with hlt | heq
  · rcases lt_or_eq_of_le ht.2 with htr | heq2
    · exact (hI.above t ⟨hlt, htr⟩).le
    · rw [heq2, hI.cost_right]
  · rw [← heq, hI.cost_left]

theorem eq_of_overlap (hI : IsCutoffExcursion c T α I)
    (hJ : IsCutoffExcursion c T α J) {t : ℝ}
    (htI : t ∈ Set.Ioo I.1 I.2) (htJ : t ∈ Set.Ioo J.1 J.2) : I = J := by
  have hleft : I.1 = J.1 := by
    rcases lt_trichotomy I.1 J.1 with h | h | h
    · exact absurd hJ.cost_left (hI.above J.1 ⟨h, htJ.1.trans htI.2⟩).ne'
    · exact h
    · exact absurd hI.cost_left (hJ.above I.1 ⟨h, htI.1.trans htJ.2⟩).ne'
  have hright : I.2 = J.2 := by
    rcases lt_trichotomy I.2 J.2 with h | h | h
    · exact absurd hI.cost_right (hJ.above I.2 ⟨htJ.1.trans htI.2, h⟩).ne'
    · exact h
    · exact absurd hJ.cost_right (hI.above J.2 ⟨htI.1.trans htJ.2, h⟩).ne'
  exact Prod.ext hleft hright

theorem right_le_left_of_left_lt (hI : IsCutoffExcursion c T α I)
    (hJ : IsCutoffExcursion c T α J) (hleft : I.1 < J.1) : I.2 ≤ J.1 := by
  by_contra h
  push_neg at h
  exact absurd hJ.cost_left (hI.above J.1 ⟨hleft, h⟩).ne'

end IsCutoffExcursion

/-- Every above-`α` time in `[0,T]` lies in a cutoff interval. -/
theorem exists_cutoff_excursion_through {c : ℝ → ℝ} {T α t : ℝ}
    (hc : Continuous c) (hstart : c 0 ≤ α) (hend : c T ≤ α)
    (ht : t ∈ Set.Icc 0 T) (hhigh : α < c t) :
    ∃ I : ℝ × ℝ, IsCutoffExcursion c T α I ∧ t ∈ Set.Ioo I.1 I.2 := by
  have hclosed : IsClosed {s : ℝ | c s ≤ α} := isClosed_le hc continuous_const
  have hL : IsCompact (Set.Icc 0 t ∩ {s : ℝ | c s ≤ α}) :=
    isCompact_Icc.inter_right hclosed
  have hLne : (Set.Icc 0 t ∩ {s : ℝ | c s ≤ α}).Nonempty :=
    ⟨0, ⟨le_rfl, ht.1⟩, hstart⟩
  obtain ⟨l, ⟨hlIcc, hlcost⟩, hlmax⟩ := hL.exists_isGreatest hLne
  have hR : IsCompact (Set.Icc t T ∩ {s : ℝ | c s ≤ α}) :=
    isCompact_Icc.inter_right hclosed
  have hRne : (Set.Icc t T ∩ {s : ℝ | c s ≤ α}).Nonempty :=
    ⟨T, ⟨ht.2, le_rfl⟩, hend⟩
  obtain ⟨r, ⟨hrIcc, hrcost⟩, hrmin⟩ := hR.exists_isLeast hRne
  have hlt : l < t := by
    rcases lt_or_eq_of_le hlIcc.2 with h | h
    · exact h
    · rw [← h] at hhigh
      exact absurd hhigh (not_lt.mpr hlcost)
  have htr : t < r := by
    rcases lt_or_eq_of_le hrIcc.1 with h | h
    · exact h
    · rw [h] at hhigh
      exact absurd hhigh (not_lt.mpr hrcost)
  obtain ⟨w, ⟨hlw, hwt⟩, hw⟩ :=
    (intermediate_value_Icc hlt.le hc.continuousOn) ⟨hlcost, hhigh.le⟩
  have hwL : w ∈ Set.Icc 0 t ∩ {s : ℝ | c s ≤ α} :=
    ⟨⟨hlIcc.1.trans hlw, hwt⟩, hw.le⟩
  have hw_eq : w = l := le_antisymm (hlmax hwL) hlw
  have hlcl : c l = α := hw_eq ▸ hw
  obtain ⟨w, ⟨hwt', hwr⟩, hw⟩ :=
    (intermediate_value_Icc' htr.le hc.continuousOn) ⟨hrcost, hhigh.le⟩
  have hwR : w ∈ Set.Icc t T ∩ {s : ℝ | c s ≤ α} :=
    ⟨⟨hwt', hwr.trans hrIcc.2⟩, hw.le⟩
  have hw_eq : w = r := le_antisymm hwr (hrmin hwR)
  have hrcr : c r = α := hw_eq ▸ hw
  have habove : ∀ s ∈ Set.Ioo l r, α < c s := by
    intro s hs
    rcases lt_or_ge s t with hts | hts
    · by_contra hnc
      push_neg at hnc
      have hsL : s ∈ Set.Icc 0 t ∩ {s : ℝ | c s ≤ α} :=
        ⟨⟨hlIcc.1.trans hs.1.le, hts.le⟩, hnc⟩
      exact absurd (hlmax hsL) (not_le.mpr hs.1)
    · by_contra hnc
      push_neg at hnc
      have hsR : s ∈ Set.Icc t T ∩ {s : ℝ | c s ≤ α} :=
        ⟨⟨hts, hs.2.le.trans hrIcc.2⟩, hnc⟩
      exact absurd (hrmin hsR) (not_le.mpr hs.2)
  exact ⟨⟨l, r⟩, ⟨hlIcc.1, hlt.trans htr, hrIcc.2, hlcl, hrcr, habove⟩,
    ⟨hlt, htr⟩⟩

theorem retainedExcursionSet_pairwiseDisjoint
    (c : ℝ → ℝ) (T α β : ℝ) :
    (retainedExcursionSet c T α β).PairwiseDisjoint
      (fun I => Set.Ioo I.1 I.2) := by
  intro I hI J hJ hIJ
  apply Set.disjoint_left.mpr
  intro t htI htJ
  exact hIJ (hI.1.eq_of_overlap hJ.1 htI htJ)

theorem exists_retainedExcursion_containing {c : ℝ → ℝ} {T α β t : ℝ}
    (hc : Continuous c) (hstart : c 0 ≤ α) (hend : c T ≤ α)
    (hαβ : α < β) (ht : t ∈ Set.Icc 0 T) (hhigh : β ≤ c t) :
    ∃ I ∈ retainedExcursionSet c T α β, t ∈ Set.Ioo I.1 I.2 := by
  obtain ⟨I, hI, htI⟩ :=
    exists_cutoff_excursion_through hc hstart hend ht (hαβ.trans_le hhigh)
  exact ⟨I, ⟨hI, t, htI, hhigh⟩, htI⟩

theorem cost_lt_threshold_outside_retained {c : ℝ → ℝ} {T α β t : ℝ}
    (hc : Continuous c) (hstart : c 0 ≤ α) (hend : c T ≤ α)
    (hαβ : α < β) (ht : t ∈ Set.Icc 0 T)
    (hout : ∀ I ∈ retainedExcursionSet c T α β, t ∉ Set.Ioo I.1 I.2) :
    c t < β := by
  by_contra h
  push_neg at h
  obtain ⟨I, hI, htI⟩ :=
    exists_retainedExcursion_containing hc hstart hend hαβ ht h
  exact hout I hI htI

end CZExposure
