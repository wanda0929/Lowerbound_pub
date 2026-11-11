module
public import RequestProject.AppendixE.VectorSubcurrent
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Exact variation of density vector measures (Appendix E support)

For finite `μ` and integrable `v : X → E` (real Banach), we prove

  `(μ.withDensityᵥ v).variation = μ.withDensity (fun x => ‖v x‖ₑ)`

— first for simple functions via fibre partitions, then for `v` by L¹ simple
approximation and the variation triangle inequality.  Upgrading the previous
`≤` bound; no claim about the original scalar mass.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set Filter

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]

theorem withDensity_vectorMeasure_variation_eq_simpleFunc
    (g : SimpleFunc X E) (hg : Integrable (g : X → E) μ) :
    (μ.withDensityᵥ (g : X → E)).variation =
      μ.withDensity (fun x => ‖g x‖ₑ) := by
  apply le_antisymm (withDensity_vectorMeasure_variation_le hg)
  rw [Measure.le_iff]
  intro s hs
  classical
  have hAy : ∀ y ∈ g.range, MeasurableSet (s ∩ g ⁻¹' {y}) :=
    fun y _ => hs.inter (g.measurableSet_fiber y)
  -- LHS = sum over fibres of norm-weighted fibre mass
  rw [MeasureTheory.withDensity_apply _ hs]
  have hl : (∫⁻ x in s, ‖g x‖ₑ ∂μ) =
      ∑ y ∈ g.range, ‖y‖ₑ * μ (s ∩ g ⁻¹' {y}) := by
    calc (∫⁻ x in s, ‖g x‖ₑ ∂μ)
        = (g.map (fun y => ‖y‖ₑ)).lintegral (μ.restrict s) := by
          simpa only [SimpleFunc.coe_map, Function.comp_apply] using
            (SimpleFunc.lintegral_eq_lintegral
              (g.map (fun y => ‖y‖ₑ)) (μ.restrict s))
      _ = ∑ y ∈ g.range, ‖y‖ₑ * (μ.restrict s) (g ⁻¹' {y}) :=
          SimpleFunc.map_lintegral (fun y => ‖y‖ₑ) g
      _ = ∑ y ∈ g.range, ‖y‖ₑ * μ (s ∩ g ⁻¹' {y}) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Measure.restrict_apply (g.measurableSet_fiber y), Set.inter_comm]
  rw [hl]
  -- each fibre term: (withDensityᵥ g) A_y = μ.real A_y • y
  have hval : ∀ y ∈ g.range,
      (μ.withDensityᵥ (g : X → E)) (s ∩ g ⁻¹' {y}) =
        (μ (s ∩ g ⁻¹' {y})).toReal • y := by
    intro y hy
    rw [withDensityᵥ_apply hg (hAy y hy)]
    calc (∫ x in s ∩ g ⁻¹' {y}, g x ∂μ)
        = ∫ _ in s ∩ g ⁻¹' {y}, y ∂μ :=
          setIntegral_congr_fun (hAy y hy) (fun x hx => hx.2)
      _ = (μ (s ∩ g ⁻¹' {y})).toReal • y := by
          simp only [integral_const, Measure.real,
            Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  -- norm of each fibre value is bounded by variation of the fibre
  have hterm : ∀ y ∈ g.range,
      ‖y‖ₑ * μ (s ∩ g ⁻¹' {y}) ≤
        (μ.withDensityᵥ (g : X → E)).variation (s ∩ g ⁻¹' {y}) := by
    intro y hy
    have h1 := vectorMeasure_enorm_le_variation
      (μ.withDensityᵥ (g : X → E)) (hAy y hy)
    rw [hval y hy, enorm_smul,
      Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top μ _)] at h1
    rwa [mul_comm] at h1
  -- sum of variations over disjoint fibres ≤ variation of s
  have hdisj : Set.PairwiseDisjoint (g.range : Set E)
      (fun y => s ∩ g ⁻¹' {y}) := by
    intro y _ z _ hyz
    apply Set.disjoint_left.mpr
    rintro x ⟨-, hx⟩ ⟨-, hz⟩
    exact hyz (hx.symm.trans hz)
  calc ∑ y ∈ g.range, ‖y‖ₑ * μ (s ∩ g ⁻¹' {y})
      ≤ ∑ y ∈ g.range,
          (μ.withDensityᵥ (g : X → E)).variation (s ∩ g ⁻¹' {y}) :=
        Finset.sum_le_sum fun y hy => hterm y hy
    _ = (μ.withDensityᵥ (g : X → E)).variation
          (⋃ y ∈ g.range, s ∩ g ⁻¹' {y}) :=
        (measure_biUnion_finset hdisj
          (fun y hy => hAy y hy)).symm
    _ ≤ (μ.withDensityᵥ (g : X → E)).variation s :=
        measure_mono (Set.iUnion_subset fun y =>
          Set.iUnion_subset fun _ => Set.inter_subset_left)

theorem withDensity_vectorMeasure_variation_eq
    {v : X → E} (hv : Integrable v μ) :
    (μ.withDensityᵥ v).variation = μ.withDensity (fun x => ‖v x‖ₑ) := by
  apply le_antisymm (withDensity_vectorMeasure_variation_le hv)
  rw [Measure.le_iff]
  intro s hs
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨g, hglt, hgmem⟩ := MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt
    (memLp_one_iff_integrable.mpr hv) ENNReal.one_ne_top
    (ε := (ε : ENNReal) / 2) (ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by simp : (2 : ENNReal) ≠ ⊤)).ne'
  have hg : Integrable (g : X → E) μ := memLp_one_iff_integrable.mp hgmem
  have hδ : (∫⁻ x, ‖v x - g x‖ₑ ∂μ) < (ε : ENNReal) / 2 := by
    simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hglt
  have hδs : (∫⁻ x in s, ‖v x - g x‖ₑ ∂μ) < (ε : ENNReal) / 2 :=
    (lintegral_mono' (Measure.restrict_le_self : μ.restrict s ≤ μ)
      (le_refl _)).trans_lt hδ
  -- vector measures Tv, Tg, Terr with Tg = Tv + Terr
  have hsplit : μ.withDensityᵥ (g : X → E) =
      μ.withDensityᵥ v + μ.withDensityᵥ (fun x => g x - v x) := by
    have hsub : Integrable (fun x => g x - v x) μ := hg.sub hv
    rw [← withDensityᵥ_add' hv hsub]
    congr 1
    funext x
    change g x = v x + (g x - v x)
    abel
  have hvar_split : (μ.withDensityᵥ (g : X → E)).variation s ≤
      (μ.withDensityᵥ v).variation s +
        (μ.withDensityᵥ (fun x => g x - v x)).variation s := by
    rw [hsplit]
    simpa only [Measure.add_apply] using
      (vectorMeasure_variation_add_le (μ.withDensityᵥ v)
        (μ.withDensityᵥ (fun x => g x - v x))) s
  have hrev (x : X) : ‖g x - v x‖ₑ = ‖v x - g x‖ₑ := by
    calc ‖g x - v x‖ₑ = ‖-(v x - g x)‖ₑ := by congr 1; abel
      _ = ‖v x - g x‖ₑ := enorm_neg _
  have herr : (μ.withDensityᵥ (fun x => g x - v x)).variation s <
      (ε : ENNReal) / 2 := by
    apply lt_of_le_of_lt _ hδs
    apply le_trans ((withDensity_vectorMeasure_variation_le (hg.sub hv)) s)
    rw [MeasureTheory.withDensity_apply _ hs]
    exact lintegral_mono (fun x => (hrev x).le)
  -- norm density bound: ‖v‖ₑ ≤ ‖g‖ₑ + ‖v - g‖ₑ
  have hnorm : (μ.withDensity (fun x => ‖v x‖ₑ)) s ≤
      (μ.withDensityᵥ v).variation s + (ε : ENNReal) := by
    rw [MeasureTheory.withDensity_apply _ hs]
    calc ∫⁻ x in s, ‖v x‖ₑ ∂μ
        ≤ ∫⁻ x in s, (‖g x‖ₑ + ‖v x - g x‖ₑ) ∂μ := by
          apply lintegral_mono
          intro x
          show ‖v x‖ₑ ≤ ‖g x‖ₑ + ‖v x - g x‖ₑ
          conv_lhs => rw [show v x = g x + (v x - g x) by simp]
          exact enorm_add_le _ _
      _ = (∫⁻ x in s, ‖g x‖ₑ ∂μ) + ∫⁻ x in s, ‖v x - g x‖ₑ ∂μ :=
          lintegral_add_left' (g.aestronglyMeasurable.enorm).restrict _
      _ = (μ.withDensityᵥ (g : X → E)).variation s +
            ∫⁻ x in s, ‖v x - g x‖ₑ ∂μ := by
          rw [← MeasureTheory.withDensity_apply _ hs,
            ← withDensity_vectorMeasure_variation_eq_simpleFunc g hg]
      _ ≤ (μ.withDensityᵥ v).variation s + (ε : ENNReal) := by
          have h1 : (μ.withDensityᵥ (g : X → E)).variation s ≤
              (μ.withDensityᵥ v).variation s + (ε : ENNReal) / 2 :=
            hvar_split.trans (add_le_add le_rfl herr.le)
          calc (μ.withDensityᵥ (g : X → E)).variation s +
                ∫⁻ x in s, ‖v x - g x‖ₑ ∂μ
              ≤ ((μ.withDensityᵥ v).variation s + (ε : ENNReal) / 2) +
                  (ε : ENNReal) / 2 := add_le_add h1 hδs.le
            _ = (μ.withDensityᵥ v).variation s +
                  ((ε : ENNReal) / 2 + (ε : ENNReal) / 2) := by rw [add_assoc]
            _ = (μ.withDensityᵥ v).variation s + (ε : ENNReal) := by
                rw [ENNReal.add_halves]
  exact hnorm
end CZExposure
