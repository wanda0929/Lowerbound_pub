module
public import RequestProject.AppendixE.CutoffExcursions
public import RequestProject.AppendixE.ExposureExcursions

/-!
# Finite cutoff-excursion selection

For `0 ≤ α < β`, `retainedExcursionSet` — the endpoint pairs whose
`α`-cutoff interval reaches `β` — is finite (the `3/2`-Lipschitz height forces each interval
to be wide, and they are disjoint inside `[0,T]`).  For `α > 0` the
retained intervals become `PositiveExposureSegment`s on the original
trajectory, packaged as `FiniteExcursionSelection`, with total physical
exposure `≤ T`, total duration `≤ T/α`, count `N·(4/3)(Hβ−Hα) ≤ T`,
coverage of every `c ≥ β` time, and pairwise-disjoint interiors.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- The retained set is finite: subtype endpoints feed the
`cost_excursion_family_finite` packing argument. -/
theorem retainedExcursionSet_finite {c : ℝ → ℝ} {T α β : ℝ}
    (hT : 0 ≤ T)
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (c t)) (Set.Icc 0 T))
    (hα : 0 ≤ α) (hαβ : α < β) :
    (retainedExcursionSet c T α β).Finite := by
  have hfin : Finite (retainedExcursionSet c T α β) := by
    apply cost_excursion_family_finite
      (fun I : retainedExcursionSet c T α β => I.1.1)
      (fun I : retainedExcursionSet c T α β => Classical.choose I.2.2)
      (fun I : retainedExcursionSet c T α β => I.1.2)
      hT hH hα hαβ
    · intro I
      have hp := Classical.choose_spec I.2.2
      exact ⟨I.2.1.left_nonneg, hp.1.1.le, hp.1.2.le, I.2.1.right_le⟩
    · intro I
      exact ⟨I.2.1.cost_left, I.2.1.cost_right,
        (Classical.choose_spec I.2.2).2⟩
    · intro I J hIJ
      exact retainedExcursionSet_pairwiseDisjoint c T α β I.2 J.2
        (Subtype.val_injective.ne hIJ)
  exact Set.finite_coe_iff.mp hfin

/-- Output data of finite cutoff-excursion selection: a finite family of
`PositiveExposureSegment`s sharing the input trajectory and control. -/
structure FiniteExcursionSelection (T α β : ℝ)
    (y : ℝ → ExposureEuclidean) (u : ℝ → ℂ) where
  count : ℕ
  segment : Fin count → PositiveExposureSegment
  bounds : ∀ i, 0 ≤ (segment i).a ∧ (segment i).b ≤ T
  trajectory_eq : ∀ i, (segment i).y = y
  control_eq : ∀ i, (segment i).u = u
  cutoff_eq : ∀ i, (segment i).cutoff = α
  endpoint_cost : ∀ i, euclideanExposureCost (y (segment i).a) = α ∧
    euclideanExposureCost (y (segment i).b) = α
  above_cutoff : ∀ i, ∀ t ∈ Set.Ioo (segment i).a (segment i).b,
    α < euclideanExposureCost (y t)
  reaches : ∀ i, ∃ p ∈ Set.Ioo (segment i).a (segment i).b,
    β ≤ euclideanExposureCost (y p)
  disjoint : Pairwise (fun i j => Disjoint
    (Set.Ioo (segment i).a (segment i).b)
    (Set.Ioo (segment j).a (segment j).b))
  covers : ∀ t ∈ Set.Icc 0 T, β ≤ euclideanExposureCost (y t) →
    ∃ i, t ∈ Set.Ioo (segment i).a (segment i).b

namespace FiniteExcursionSelection

/-- Build the selection from a trajectory by retaining the cutoff
intervals that reach `β`. -/
def ofTrajectory {T α β : ℝ} {y : ℝ → ExposureEuclidean}
    {u : ℝ → ℂ} {K : NNReal}
    (hT : 0 ≤ T) (hα : 0 < α) (hαβ : α < β)
    (hy : LipschitzWith K y) (hu : Measurable u) (hu_bound : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hstart : euclideanExposureCost (y 0) ≤ α)
    (hend : euclideanExposureCost (y T) ≤ α) :
    FiniteExcursionSelection T α β y u := by
  have hc : Continuous (fun t => euclideanExposureCost (y t)) :=
    continuous_euclideanExposureCost.comp hy.continuous
  have hH := lipschitzOn_costThreeHalves_exposure hT hy hdom hu_bound hode
  have hfinite := retainedExcursionSet_finite hT hH hα.le hαβ
  let A := retainedExcursionSet (fun t => euclideanExposureCost (y t)) T α β
  haveI : Fintype A := hfinite.fintype
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  exact ⟨Fintype.card A,
    fun i => PositiveExposureSegment.ofTrajectory
      (e i).2.1.left_nonneg (e i).2.1.nondegenerate (e i).2.1.right_le hα
      hy hu hu_bound hdom hode (fun t ht => (e i).2.1.cost_ge ht),
    fun i => ⟨(e i).2.1.left_nonneg, (e i).2.1.right_le⟩,
    fun i => rfl, fun i => rfl, fun i => rfl,
    fun i => ⟨(e i).2.1.cost_left, (e i).2.1.cost_right⟩,
    fun i t ht => (e i).2.1.above t ht,
    fun i => (e i).2.2,
    fun i j hij =>
      retainedExcursionSet_pairwiseDisjoint _ _ _ _ (e i).2 (e j).2
        (Subtype.val_injective.ne (e.injective.ne hij)),
    fun t ht hhigh => by
      obtain ⟨I, hI, htI⟩ :=
        exists_retainedExcursion_containing hc hstart hend hαβ ht hhigh
      refine ⟨e.symm ⟨I, hI⟩, ?_⟩
      have hval : (e (e.symm ⟨I, hI⟩)).1 = I :=
        congrArg Subtype.val (e.apply_symm_apply ⟨I, hI⟩)
      show t ∈ Set.Ioo ((e (e.symm ⟨I, hI⟩)).1.1)
        ((e (e.symm ⟨I, hI⟩)).1.2)
      rw [hval]
      exact htI⟩

variable {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
variable (S : FiniteExcursionSelection T α β y u)

theorem cost_lt_outside {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hout : ∀ i, t ∉ Set.Ioo (S.segment i).a (S.segment i).b) :
    euclideanExposureCost (y t) < β := by
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := S.covers t ht h
  exact hout i hi

theorem right_le_left_of_start_lt {i j : Fin S.count}
    (hij : (S.segment i).a < (S.segment j).a) :
    (S.segment i).b ≤ (S.segment j).a := by
  by_contra h
  push_neg at h
  exact absurd (S.endpoint_cost j).1
    (S.above_cutoff i _ ⟨hij, h⟩).ne'

theorem exposure_le (hT : 0 ≤ T) :
    (∑ i, (S.segment i).physicalExposure) ≤ T :=
  sum_retained_physicalExposure_le Finset.univ S.segment hT
    (fun i _ => S.bounds i)
    (fun _i _ _j _ hij => S.disjoint hij)

theorem duration_le (hT : 0 ≤ T) (hα : 0 < α) :
    (∑ i, (S.segment i).duration) ≤ T / α := by
  have h1 : ∀ i, (S.segment i).duration ≤
      ((S.segment i).b - (S.segment i).a) / α := fun i => by
    have h := (S.segment i).duration_bounds.2
    rwa [S.cutoff_eq i] at h
  have h2 : ∑ i, (S.segment i).duration ≤
      ∑ i, ((S.segment i).b - (S.segment i).a) / α :=
    Finset.sum_le_sum fun i _ => h1 i
  rw [← Finset.sum_div] at h2
  have h3 : ∑ i, ((S.segment i).b - (S.segment i).a) =
      ∑ i, (S.segment i).physicalExposure :=
    Finset.sum_congr rfl fun i _ => ((S.segment i).physicalExposure_eq).symm
  rw [h3] at h2
  exact h2.trans (div_le_div_of_nonneg_right (S.exposure_le hT) hα.le)

theorem count_bound (hT : 0 ≤ T) (hα : 0 ≤ α) (hαβ : α < β)
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (euclideanExposureCost (y t)))
        (Set.Icc 0 T)) :
    (S.count : ℝ) *
      ((4/3 : ℝ) * (costThreeHalves β - costThreeHalves α)) ≤ T := by
  have hb := cost_excursion_count_bound (A := Fin S.count) Finset.univ
    (fun i => (S.segment i).a) (fun i => Classical.choose (S.reaches i))
    (fun i => (S.segment i).b)
    (c := fun t => euclideanExposureCost (y t))
    hT hH hα hαβ
    (fun i _ => ⟨(S.bounds i).1,
      (Classical.choose_spec (S.reaches i)).1.1.le,
      (Classical.choose_spec (S.reaches i)).1.2.le,
      (S.bounds i).2⟩)
    (fun i _ => ⟨(S.endpoint_cost i).1, (S.endpoint_cost i).2,
      (Classical.choose_spec (S.reaches i)).2⟩)
    (fun i _ j _ hij => S.disjoint hij)
  rwa [Finset.card_univ, Fintype.card_fin] at hb

theorem physical_endpoints_cost (i : Fin S.count) :
    cost ((S.segment i).physicalPath 0) = α ∧
    cost ((S.segment i).physicalPath (S.segment i).duration) = α := by
  have ha : (S.segment i).a ∈ Set.Icc (S.segment i).a (S.segment i).b :=
    ⟨le_rfl, (S.segment i).a_lt_b.le⟩
  have hb : (S.segment i).b ∈ Set.Icc (S.segment i).a (S.segment i).b :=
    ⟨(S.segment i).a_lt_b.le, le_rfl⟩
  constructor
  · rw [(S.segment i).physicalPath_zero,
      (S.segment i).cost_liftedState ha, S.trajectory_eq i]
    exact (S.endpoint_cost i).1
  · rw [(S.segment i).physicalPath_terminal,
      (S.segment i).cost_liftedState hb, S.trajectory_eq i]
    exact (S.endpoint_cost i).2

end FiniteExcursionSelection

@[simp] theorem euclideanExposureCost_y0 :
    euclideanExposureCost (exposureEuclideanEquiv y0) = 0 := by
  show Real.sqrt ((exposureEuclideanEquiv.symm
    (exposureEuclideanEquiv y0)) 2) = 0
  rw [exposureEuclideanEquiv.symm_apply_apply,
    show y0 2 = 0 from rfl, Real.sqrt_zero]

@[simp] theorem euclideanExposureCost_yPi :
    euclideanExposureCost (exposureEuclideanEquiv yPi) = 0 := by
  show Real.sqrt ((exposureEuclideanEquiv.symm
    (exposureEuclideanEquiv yPi)) 2) = 0
  rw [exposureEuclideanEquiv.symm_apply_apply,
    show yPi 2 = 0 from rfl, Real.sqrt_zero]

theorem exists_finite_excursion_selection
    {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hT : 0 ≤ T) (hα : 0 < α) (hαβ : α < β)
    (hy : LipschitzWith K y) (hu : Measurable u) (hu_bound : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hstart : y 0 = exposureEuclideanEquiv y0)
    (hend : y T = exposureEuclideanEquiv yPi) :
    ∃ S : FiniteExcursionSelection T α β y u,
      (S.count : ℝ) *
        ((4/3 : ℝ) * (costThreeHalves β - costThreeHalves α)) ≤ T ∧
      (∑ i, (S.segment i).physicalExposure) ≤ T ∧
      (∑ i, (S.segment i).duration) ≤ T / α := by
  refine ⟨FiniteExcursionSelection.ofTrajectory hT hα hαβ hy hu hu_bound
      hdom hode
      (by rw [hstart, euclideanExposureCost_y0]; exact hα.le)
      (by rw [hend, euclideanExposureCost_yPi]; exact hα.le),
    ?_, ?_, ?_⟩
  · exact FiniteExcursionSelection.count_bound _ hT hα.le hαβ
      (lipschitzOn_costThreeHalves_exposure hT hy hdom hu_bound hode)
  · exact FiniteExcursionSelection.exposure_le _ hT
  · exact FiniteExcursionSelection.duration_le _ hT hα

end CZExposure
