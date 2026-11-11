module
public import RequestProject.AppendixE.ExcursionPhaseAccounting
public import RequestProject.AppendixE.EndpointRepair

/-!
# Finite repaired-excursion assembly

Conditional on `H : LocalSteering`, the actual retained physical
segments are repaired and phase-aligned from `x0`; the terminal
phase repair then closes the assembled `-E` deficit before unit
conversion.  All bounds are explicitly conditional on `H`.
-/

@[expose] public section

noncomputable section

namespace CZExposure.FiniteExcursionSelection

open MeasureTheory Set
open scoped NNReal ENNReal

variable {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
variable (S : FiniteExcursionSelection T α β y u)

/-- Repair the actual chronological retained segments, not a supplied
family. -/
theorem exists_repaired_blocks (H : LocalSteering)
    (hα : 0 ≤ α) (hcut : α ≤ 1/12) (hnear : 32 * Real.sqrt α ≤ H.radius) :
  ∃ B : Fin S.count → FaceBlock, ∀ i,
    (B i).initial = faceProjection ((S.orderedSegment i).physicalPath 0) ∧
    (B i).terminal = faceProjection
      ((S.orderedSegment i).physicalPath (S.orderedSegment i).duration) ∧
    (B i).segment.duration ≤ (S.orderedSegment i).duration +
      2 * H.timeBound (32 * Real.sqrt α) ∧
    (B i).segment.exposure ≤ (S.orderedSegment i).physicalExposure +
      2 * H.exposureBound (32 * Real.sqrt α) ∧
    (B i).phaseRatio = S.retainedPhaseRatio i := by
  classical
  have hstep : ∀ i : Fin S.count, ∃ B : FaceBlock,
      B.initial = faceProjection ((S.orderedSegment i).physicalPath 0) ∧
      B.terminal = faceProjection ((S.orderedSegment i).physicalPath
        (S.orderedSegment i).duration) ∧
      B.segment.duration ≤ (S.orderedSegment i).duration +
        2 * H.timeBound (32 * Real.sqrt α) ∧
      B.segment.exposure ≤ (S.orderedSegment i).physicalExposure +
        2 * H.exposureBound (32 * Real.sqrt α) ∧
      B.phaseRatio = S.retainedPhaseRatio i := by
    intro i
    obtain ⟨B0, hBi, hBt, hBd, hBe, hBr⟩ :=
      H.exists_repaired_faceBlock
        (PhysicalSegment.ofPositiveExposureSegment (S.orderedSegment i))
        hα hcut
        (le_of_eq (S.physical_endpoints_cost (S.chronologicalOrder i)).1)
        (le_of_eq (S.physical_endpoints_cost (S.chronologicalOrder i)).2)
        hnear
    have hproj := S.physical_endpoints_projection hcut (S.chronologicalOrder i)
    refine ⟨B0, hBi, hBt, hBd, hBe, ?_⟩
    have hX0 : (S.orderedSegment i).physicalPath 0 ∈ Xset :=
      (S.orderedSegment i).physicalPath_mem 0
    have hXd : (S.orderedSegment i).physicalPath
        (S.orderedSegment i).duration ∈ Xset :=
      (S.orderedSegment i).physicalPath_mem _
    have hc0 : cost ((S.orderedSegment i).physicalPath 0) ≤ 1/12 :=
      (le_of_eq (S.physical_endpoints_cost (S.chronologicalOrder i)).1).trans
        hcut
    have hcd : cost ((S.orderedSegment i).physicalPath
        (S.orderedSegment i).duration) ≤ 1/12 :=
      (le_of_eq (S.physical_endpoints_cost (S.chronologicalOrder i)).2).trans
        hcut
    rw [hBr]
    show complexUnitPhase (zObs ((S.orderedSegment i).physicalPath
            (S.orderedSegment i).duration)) /
        complexUnitPhase (zObs ((S.orderedSegment i).physicalPath 0)) =
      complexUnitPhase (exposureProgressPath y (S.orderedSegment i).b) /
        complexUnitPhase (exposureProgressPath y (S.orderedSegment i).a)
    rw [← zObs_faceProjection hXd hcd, ← zObs_faceProjection hX0 hc0]
    rw [show zObs (faceProjection ((S.orderedSegment i).physicalPath
          (S.orderedSegment i).duration)) =
        complexUnitPhase (exposureProgressPath y (S.orderedSegment i).b)
        from hproj.2.2.2.2.2]
    rw [show zObs (faceProjection ((S.orderedSegment i).physicalPath 0)) =
        complexUnitPhase (exposureProgressPath y (S.orderedSegment i).a)
        from hproj.2.2.2.2.1]
  exact ⟨fun i => Classical.choose (hstep i),
    fun i => Classical.choose_spec (hstep i)⟩

/-- Aligned finite assembly, with actual retained phase product. -/
theorem exists_repaired_assembly (H : LocalSteering)
    (hT : 0 ≤ T) (hα : 0 < α) (hcut : α ≤ 1/12)
    (hnear : 32 * Real.sqrt α ≤ H.radius) :
  ∃ A : FaceBlock, A.initial = x0 ∧
    A.segment.duration ≤ T/α + 2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α) ∧
    A.segment.exposure ≤ T + 2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α) ∧
    A.phaseRatio = S.retainedPhaseProduct := by
  obtain ⟨B, hB⟩ := S.exists_repaired_blocks H hα.le hcut hnear
  refine ⟨FaceBlock.assemble x0 FaceBlock.x0_mem_Fface (List.ofFn B),
    FaceBlock.assemble_initial x0 FaceBlock.x0_mem_Fface (List.ofFn B), ?_,
    ?_, ?_⟩
  · have hd := FaceBlock.assemble_duration x0 FaceBlock.x0_mem_Fface
      (List.ofFn B)
    have hperm : ∑ i, (S.orderedSegment i).duration =
        ∑ i, (S.segment i).duration :=
      Equiv.sum_comp S.chronologicalOrder (fun i => (S.segment i).duration)
    have hSdur := S.duration_le hT hα
    have hbind : ∑ i, (B i).segment.duration ≤
        ∑ i, ((S.orderedSegment i).duration +
          2 * H.timeBound (32 * Real.sqrt α)) :=
      Finset.sum_le_sum fun i _ => (hB i).2.2.1
    have hsumD : ((List.ofFn B).map (fun Bi => Bi.segment.duration)).sum =
        ∑ i, (B i).segment.duration := by
      rw [List.map_ofFn, List.sum_ofFn]
      exact Finset.sum_congr rfl fun i _ => rfl
    have h1 : ∑ i, (B i).segment.duration ≤
        ∑ i, (S.segment i).duration +
          2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α) := by
      calc ∑ i, (B i).segment.duration
          ≤ ∑ i, ((S.orderedSegment i).duration +
              2 * H.timeBound (32 * Real.sqrt α)) := hbind
        _ = ∑ i, (S.orderedSegment i).duration +
            (S.count : ℝ) * (2 * H.timeBound (32 * Real.sqrt α)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑ i, (S.segment i).duration +
            (S.count : ℝ) * (2 * H.timeBound (32 * Real.sqrt α)) := by
          rw [hperm]
        _ = _ := by ring
    rw [hd, hsumD]
    linarith [h1, hSdur]
  · have he := FaceBlock.assemble_exposure x0 FaceBlock.x0_mem_Fface
      (List.ofFn B)
    have hperm : ∑ i, (S.orderedSegment i).physicalExposure =
        ∑ i, (S.segment i).physicalExposure :=
      Equiv.sum_comp S.chronologicalOrder
        (fun i => (S.segment i).physicalExposure)
    have hSexp := S.exposure_le hT
    have hbind : ∑ i, (B i).segment.exposure ≤
        ∑ i, ((S.orderedSegment i).physicalExposure +
          2 * H.exposureBound (32 * Real.sqrt α)) :=
      Finset.sum_le_sum fun i _ => (hB i).2.2.2.1
    have hsumE : ((List.ofFn B).map (fun Bi => Bi.segment.exposure)).sum =
        ∑ i, (B i).segment.exposure := by
      rw [List.map_ofFn, List.sum_ofFn]
      exact Finset.sum_congr rfl fun i _ => rfl
    have h1 : ∑ i, (B i).segment.exposure ≤
        ∑ i, (S.segment i).physicalExposure +
          2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α) := by
      calc ∑ i, (B i).segment.exposure
          ≤ ∑ i, ((S.orderedSegment i).physicalExposure +
              2 * H.exposureBound (32 * Real.sqrt α)) := hbind
        _ = ∑ i, (S.orderedSegment i).physicalExposure +
            (S.count : ℝ) * (2 * H.exposureBound (32 * Real.sqrt α)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑ i, (S.segment i).physicalExposure +
            (S.count : ℝ) * (2 * H.exposureBound (32 * Real.sqrt α)) := by
          rw [hperm]
        _ = _ := by ring
    rw [he, hsumE]
    linarith [h1, hSexp]
  · have hpr := FaceBlock.assemble_phaseRatio x0 FaceBlock.x0_mem_Fface
      (List.ofFn B)
    have hpsum : ((List.ofFn B).map FaceBlock.phaseRatio).prod =
        ∏ i, (B i).phaseRatio := by
      rw [List.map_ofFn, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => rfl
    rw [hpr, hpsum]
    calc ∏ i, (B i).phaseRatio = ∏ i, S.retainedPhaseRatio i :=
        Finset.prod_congr rfl fun i _ => (hB i).2.2.2.2
      _ = S.retainedPhaseProduct := rfl

/-- Finite exact-CZ pulse with explicit cutoff and count budget. -/
theorem exists_pulse_with_count_budget (H : LocalSteering) {K : NNReal}
    (hT : 0 ≤ T) (hα : 0 < α) (hαβ : α < β)
    (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hstart : y 0 = exposureEuclideanEquiv y0)
    (hend : y T = exposureEuclideanEquiv yPi)
    (hβ : β ≤ 1/12)
    (hendpoint : 32 * Real.sqrt α ≤ H.radius)
    (hphaseNear : 8 * T * Real.sqrt β ≤ H.radius) :
  ∃ γ : Pulse,
    γ.S ≤ T/α + 2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α) +
      H.timeBound (8 * T * Real.sqrt β) ∧
    γ.exposure ≤ T + 2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α) +
      H.exposureBound (8 * T * Real.sqrt β) := by
  obtain ⟨A, hAi, hAd, hAe, hApr⟩ :=
    S.exists_repaired_assembly H hT hα (hαβ.le.trans hβ) hendpoint
  obtain ⟨hProd, hE⟩ :=
    S.retained_phase_and_error hT (hαβ.le.trans hβ) hy hu hub hdom hode
      hstart hend hβ
  have hzI : zObs A.initial = 1 := by
    rw [hAi]
    show zObs x0 = 1
    change zObs (mkState 1 0 1 0) = 1
    simp [zObs]
  have hzT : zObs A.terminal =
      -phaseFactor (-S.discardedAngularIntegral) := by
    have h : zObs A.terminal / zObs A.initial =
        -phaseFactor (-S.discardedAngularIntegral) := hApr.trans hProd
    rw [hzI, div_one] at h
    exact h
  obtain ⟨γ, hγd, hγe⟩ := H.exists_closed_pulse A.segment hAi A.terminal_face
    hzT (by rw [abs_neg]; exact hE.trans hphaseNear)
  have hTmono : H.timeBound |(-S.discardedAngularIntegral)| ≤
      H.timeBound (8 * T * Real.sqrt β) :=
    H.timeBound_mono (abs_nonneg _) (by rw [abs_neg]; exact hE)
  have hEmono : H.exposureBound |(-S.discardedAngularIntegral)| ≤
      H.exposureBound (8 * T * Real.sqrt β) :=
    H.exposureBound_mono (abs_nonneg _) (by rw [abs_neg]; exact hE)
  refine ⟨γ, ?_, ?_⟩
  · calc γ.S ≤ A.segment.duration +
        H.timeBound |(-S.discardedAngularIntegral)| := hγd
      _ ≤ (T/α + 2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α)) +
          H.timeBound |(-S.discardedAngularIntegral)| :=
        add_le_add hAd le_rfl
      _ ≤ (T/α + 2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α)) +
          H.timeBound (8 * T * Real.sqrt β) :=
        add_le_add le_rfl hTmono
      _ = T/α + 2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α) +
          H.timeBound (8 * T * Real.sqrt β) := by ring
  · calc γ.exposure ≤ A.segment.exposure +
        H.exposureBound |(-S.discardedAngularIntegral)| := hγe
      _ ≤ (T + 2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α)) +
          H.exposureBound |(-S.discardedAngularIntegral)| :=
        add_le_add hAe le_rfl
      _ ≤ (T + 2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α)) +
          H.exposureBound (8 * T * Real.sqrt β) :=
        add_le_add le_rfl hEmono
      _ = T + 2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α) +
          H.exposureBound (8 * T * Real.sqrt β) := by ring

/-- Specialize the existing half-cutoff packing theorem to this
selection. -/
theorem count_bound_half_cutoff
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hβ : 0 < β) (hhalf : α ≤ β/2)
    (hH : LipschitzOnWith (3/2 : NNReal)
      (fun t => costThreeHalves (euclideanExposureCost (y t))) (Set.Icc 0 T)) :
    (S.count : ℝ) * ((2/3 : ℝ) * costThreeHalves β) ≤ T := by
  have hb := cost_excursion_count_bound_half_cutoff (A := Fin S.count)
    Finset.univ
    (fun i => (S.segment i).a) (fun i => Classical.choose (S.reaches i))
    (fun i => (S.segment i).b)
    (c := fun t => euclideanExposureCost (y t))
    hT hH hα hβ hhalf
    (fun i _ => ⟨(S.bounds i).1,
      (Classical.choose_spec (S.reaches i)).1.1.le,
      (Classical.choose_spec (S.reaches i)).1.2.le,
      (S.bounds i).2⟩)
    (fun i _ => ⟨(S.endpoint_cost i).1, (S.endpoint_cost i).2,
      (Classical.choose_spec (S.reaches i)).2⟩)
    (fun i _ j _ hij => S.disjoint hij)
  rwa [Finset.card_univ, Fintype.card_fin] at hb

end CZExposure.FiniteExcursionSelection

namespace CZExposure.LocalSteering

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Construct selection, repaired blocks, assembly, final correction,
and unit pulse. -/
theorem exists_pulse_of_exposure_trajectory (H : LocalSteering)
    {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hT : 0 ≤ T) (hα : 0 < α) (hβ : 0 < β) (hhalf : α ≤ β/2)
    (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hstart : y 0 = exposureEuclideanEquiv y0)
    (hend : y T = exposureEuclideanEquiv yPi)
    (hβsmall : β ≤ 1/12)
    (hendpoint : 32 * Real.sqrt α ≤ H.radius)
    (hphaseNear : 8 * T * Real.sqrt β ≤ H.radius) :
  ∃ γ : Pulse,
    γ.S ≤ T/α + (3 * T/costThreeHalves β) * H.timeBound (32 * Real.sqrt α) +
      H.timeBound (8 * T * Real.sqrt β) ∧
    γ.exposure ≤ T + (3 * T/costThreeHalves β) *
        H.exposureBound (32 * Real.sqrt α) +
      H.exposureBound (8 * T * Real.sqrt β) := by
  have hαβ : α < β := hhalf.trans_lt (half_lt_self hβ)
  obtain ⟨S, -, -, -⟩ := exists_finite_excursion_selection hT hα hαβ hy hu
    hub hdom hode hstart hend
  obtain ⟨γ, hγd, hγe⟩ := S.exists_pulse_with_count_budget H hT hα hαβ hy hu
    hub hdom hode hstart hend hβsmall hendpoint hphaseNear
  have hpack : (S.count : ℝ) * ((2/3 : ℝ) * costThreeHalves β) ≤ T :=
    S.count_bound_half_cutoff hT hα.le hβ hhalf
      (lipschitzOn_costThreeHalves_exposure hT hy hdom hub hode)
  have hc3 : (0:ℝ) < costThreeHalves β := by
    show 0 < β * Real.sqrt β
    exact mul_pos hβ (Real.sqrt_pos.mpr hβ)
  have hN : 2 * (S.count : ℝ) ≤ 3 * T / costThreeHalves β := by
    rw [le_div_iff₀ hc3]
    nlinarith [hpack]
  have hTnn : 0 ≤ H.timeBound (32 * Real.sqrt α) :=
    H.timeBound_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg α))
  have hEnn : 0 ≤ H.exposureBound (32 * Real.sqrt α) :=
    H.exposureBound_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg α))
  have hd2 : 2 * (S.count : ℝ) * H.timeBound (32 * Real.sqrt α) ≤
      (3 * T/costThreeHalves β) * H.timeBound (32 * Real.sqrt α) :=
    mul_le_mul_of_nonneg_right hN hTnn
  have he2 : 2 * (S.count : ℝ) * H.exposureBound (32 * Real.sqrt α) ≤
      (3 * T/costThreeHalves β) * H.exposureBound (32 * Real.sqrt α) :=
    mul_le_mul_of_nonneg_right hN hEnn
  exact ⟨γ, by linarith [hγd, hd2], by linarith [hγe, he2]⟩

end CZExposure.LocalSteering
