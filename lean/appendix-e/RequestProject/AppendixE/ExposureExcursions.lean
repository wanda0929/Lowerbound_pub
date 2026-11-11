module
public import RequestProject.AppendixE.CostGrowth
public import RequestProject.AppendixE.PhysicalReparam

/-!
# Excursion width bounds, finite-count packing, and retained exposure

A `3/2`-Lipschitz height `H(c) = c√c` forces every rise-and-fall excursion
from level `α` to a peak `≥ β` to last at least `(4/3)(Hβ − Hα)`.  Disjoint
open intervals pack inside `[0,T]`, so the excursion family has a uniform
count bound and is in fact FINITE for arbitrary index types.  Finally the
retained physical exposures of disjoint `PositiveExposureSegment`s sum to
at most `T`.  Supplied endpoint/peak/disjointness data; `CutoffExcursions`
and `ExcursionSelection` construct these data and prove coverage.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

theorem cost_excursion_duration_lower_bound
    {c : ℝ → ℝ} {T α β l p r : ℝ}
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (c t)) (Set.Icc 0 T))
    (hα : 0 ≤ α) (hαβ : α < β)
    (hl : 0 ≤ l) (hlp : l ≤ p) (hpr : p ≤ r) (hr : r ≤ T)
    (hcl : c l = α) (hcr : c r = α) (hcp : β ≤ c p) :
    (4/3 : ℝ) * (costThreeHalves β - costThreeHalves α) ≤ r - l := by
  have hβ0 : 0 ≤ β := hα.trans hαβ.le
  have hαβH : costThreeHalves α ≤ costThreeHalves β :=
    monotoneOn_costThreeHalves hα hβ0 hαβ.le
  have hHp : costThreeHalves β ≤ costThreeHalves (c p) :=
    monotoneOn_costThreeHalves hβ0 (hβ0.trans hcp) hcp
  have hl' : l ∈ Set.Icc 0 T := ⟨hl, (hlp.trans hpr).trans hr⟩
  have hp' : p ∈ Set.Icc 0 T := ⟨hl.trans hlp, hpr.trans hr⟩
  have hr' : r ∈ Set.Icc 0 T := ⟨hl.trans (hlp.trans hpr), hr⟩
  have d1 := hH.dist_le_mul l hl' p hp'
  have d2 := hH.dist_le_mul p hp' r hr'
  rw [Real.dist_eq, Real.dist_eq] at d1 d2
  rw [hcl] at d1
  rw [hcr] at d2
  rw [abs_of_nonpos (sub_nonpos.mpr (hαβH.trans hHp)),
    abs_of_nonpos (sub_nonpos.mpr hlp)] at d1
  rw [abs_of_nonneg (sub_nonneg.mpr (hαβH.trans hHp)),
    abs_of_nonpos (sub_nonpos.mpr hpr)] at d2
  push_cast at d1 d2
  nlinarith

theorem sum_disjoint_interval_lengths_le {A : Type*}
    (I : Finset A) (l r : A → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hvalid : ∀ i ∈ I, 0 ≤ l i ∧ l i ≤ r i ∧ r i ≤ T)
    (hdisj : (↑I : Set A).PairwiseDisjoint (fun i => Set.Ioo (l i) (r i))) :
    ∑ i ∈ I, (r i - l i) ≤ T := by
  have hmeas : ∀ i ∈ I, MeasurableSet (Set.Ioo (l i) (r i)) :=
    fun _ _ => measurableSet_Ioo
  have hvol : volume (⋃ i ∈ I, Set.Ioo (l i) (r i)) =
      ∑ i ∈ I, volume (Set.Ioo (l i) (r i)) :=
    measure_biUnion_finset hdisj hmeas
  have hsub : (⋃ i ∈ I, Set.Ioo (l i) (r i)) ⊆ Set.Icc 0 T := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioo] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hv := hvalid i hi
    exact ⟨hv.1.trans hxi.1.le, hxi.2.le.trans hv.2.2⟩
  have hle : volume (⋃ i ∈ I, Set.Ioo (l i) (r i)) ≤ volume (Set.Icc 0 T) :=
    measure_mono hsub
  rw [hvol] at hle
  simp only [Real.volume_Ioo] at hle
  rw [Real.volume_Icc] at hle
  rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i hi => sub_nonneg.mpr (hvalid i hi).2.1),
    show T - 0 = T from sub_zero T] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hT).mp hle

theorem cost_excursion_count_bound {A : Type*} (I : Finset A)
    (l p r : A → ℝ) {c : ℝ → ℝ} {T α β : ℝ}
    (hT : 0 ≤ T)
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (c t)) (Set.Icc 0 T))
    (hα : 0 ≤ α) (hαβ : α < β)
    (hvalid : ∀ i ∈ I, 0 ≤ l i ∧ l i ≤ p i ∧ p i ≤ r i ∧ r i ≤ T)
    (hcost : ∀ i ∈ I, c (l i) = α ∧ c (r i) = α ∧ β ≤ c (p i))
    (hdisj : (↑I : Set A).PairwiseDisjoint (fun i => Set.Ioo (l i) (r i))) :
    (I.card : ℝ) * ((4/3 : ℝ) * (costThreeHalves β - costThreeHalves α)) ≤ T := by
  have hw : ∀ i ∈ I,
      (4/3 : ℝ) * (costThreeHalves β - costThreeHalves α) ≤ r i - l i :=
    fun i hi =>
      cost_excursion_duration_lower_bound hH hα hαβ (hvalid i hi).1
        (hvalid i hi).2.1 (hvalid i hi).2.2.1 (hvalid i hi).2.2.2
        (hcost i hi).1 (hcost i hi).2.1 (hcost i hi).2.2
  calc (I.card : ℝ) * ((4/3 : ℝ) * (costThreeHalves β - costThreeHalves α))
      = ∑ _i ∈ I, (4/3 : ℝ) * (costThreeHalves β - costThreeHalves α) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ I, (r i - l i) := Finset.sum_le_sum hw
    _ ≤ T := sum_disjoint_interval_lengths_le I l r hT
        (fun i hi => ⟨(hvalid i hi).1,
          (hvalid i hi).2.1.trans (hvalid i hi).2.2.1,
          (hvalid i hi).2.2.2⟩) hdisj

theorem cost_excursion_family_finite {A : Type*}
    (l p r : A → ℝ) {c : ℝ → ℝ} {T α β : ℝ}
    (hT : 0 ≤ T)
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (c t)) (Set.Icc 0 T))
    (hα : 0 ≤ α) (hαβ : α < β)
    (hvalid : ∀ i, 0 ≤ l i ∧ l i ≤ p i ∧ p i ≤ r i ∧ r i ≤ T)
    (hcost : ∀ i, c (l i) = α ∧ c (r i) = α ∧ β ≤ c (p i))
    (hdisj : Pairwise (fun i j => Disjoint (Set.Ioo (l i) (r i))
      (Set.Ioo (l j) (r j)))) : Finite A := by
  classical
  cases finite_or_infinite A with
  | inl h => exact h
  | inr hInf =>
    letI := hInf
    have hL : (0 : ℝ) < (4/3 : ℝ) * (costThreeHalves β - costThreeHalves α) :=
      mul_pos (by norm_num)
        (sub_pos.mpr (strictMonoOn_costThreeHalves hα (hα.trans hαβ.le) hαβ))
    obtain ⟨n, hn⟩ := exists_nat_gt
      (T / ((4/3 : ℝ) * (costThreeHalves β - costThreeHalves α)))
    obtain ⟨I, hI⟩ := Finset.exists_card_eq (α := A) n
    have hI' : (↑I : Set A).PairwiseDisjoint (fun i => Set.Ioo (l i) (r i)) :=
      fun _ _ _ _ hij => hdisj hij
    have hb := cost_excursion_count_bound I l p r hT hH hα hαβ
      (fun i _ => hvalid i) (fun i _ => hcost i) hI'
    rw [hI] at hb
    have hT' := (div_lt_iff₀ hL).mp hn
    linarith

theorem cost_excursion_count_bound_half_cutoff {A : Type*} (I : Finset A)
    (l p r : A → ℝ) {c : ℝ → ℝ} {T α β : ℝ}
    (hT : 0 ≤ T)
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (c t)) (Set.Icc 0 T))
    (hα : 0 ≤ α) (hβ : 0 < β) (hhalf : α ≤ β/2)
    (hvalid : ∀ i ∈ I, 0 ≤ l i ∧ l i ≤ p i ∧ p i ≤ r i ∧ r i ≤ T)
    (hcost : ∀ i ∈ I, c (l i) = α ∧ c (r i) = α ∧ β ≤ c (p i))
    (hdisj : (↑I : Set A).PairwiseDisjoint (fun i => Set.Ioo (l i) (r i))) :
    (I.card : ℝ) * ((2/3 : ℝ) * costThreeHalves β) ≤ T := by
  have hαβ : α < β := hhalf.trans_lt (half_lt_self hβ)
  have hHα : costThreeHalves α ≤ costThreeHalves β / 2 := by
    show α * Real.sqrt α ≤ β * Real.sqrt β / 2
    calc α * Real.sqrt α ≤ α * Real.sqrt β :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hαβ.le) hα
      _ ≤ (β / 2) * Real.sqrt β :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg β)
      _ = β * Real.sqrt β / 2 := by ring
  have hL : (2/3 : ℝ) * costThreeHalves β ≤
      (4/3 : ℝ) * (costThreeHalves β - costThreeHalves α) := by
    nlinarith
  calc (I.card : ℝ) * ((2/3 : ℝ) * costThreeHalves β)
      ≤ (I.card : ℝ) *
        ((4/3 : ℝ) * (costThreeHalves β - costThreeHalves α)) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
    _ ≤ T := cost_excursion_count_bound I l p r hT hH hα hαβ hvalid hcost hdisj

theorem sum_retained_physicalExposure_le {A : Type*}
    (I : Finset A) (segments : A → PositiveExposureSegment)
    {T : ℝ} (hT : 0 ≤ T)
    (hvalid : ∀ i ∈ I, 0 ≤ (segments i).a ∧ (segments i).b ≤ T)
    (hdisj : (↑I : Set A).PairwiseDisjoint
      (fun i => Set.Ioo (segments i).a (segments i).b)) :
    ∑ i ∈ I, (segments i).physicalExposure ≤ T := by
  have hsum : ∑ i ∈ I, (segments i).physicalExposure =
      ∑ i ∈ I, ((segments i).b - (segments i).a) :=
    Finset.sum_congr rfl (fun i _ => (segments i).physicalExposure_eq)
  rw [hsum]
  exact sum_disjoint_interval_lengths_le I
    (fun i => (segments i).a) (fun i => (segments i).b) hT
    (fun i hi => ⟨(hvalid i hi).1, (segments i).a_lt_b.le, (hvalid i hi).2⟩)
    hdisj

end CZExposure
