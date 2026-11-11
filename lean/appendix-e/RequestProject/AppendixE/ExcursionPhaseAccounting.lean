module
public import RequestProject.AppendixE.ExcursionGaps
public import RequestProject.AppendixE.FaceProjection
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Retained/gap phase accounting

The exact telescope between the retained intervals and the
chronological gaps.  Writing `E` for `discardedAngularIntegral`, the
retained normalized phase ratios multiply to `−exp(−iE)`, with
`|E| ≤ 8T√β`.  The proof includes empty selections and zero-length
gaps; no principal phase choice is made.
-/

@[expose] public section

noncomputable section

namespace CZExposure.FiniteExcursionSelection

open MeasureTheory Set
open scoped NNReal ENNReal

variable {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
variable (S : FiniteExcursionSelection T α β y u)

def retainedPhaseRatio (i : Fin S.count) : ℂ :=
  complexUnitPhase (exposureProgressPath y (S.orderedSegment i).b) /
    complexUnitPhase (exposureProgressPath y (S.orderedSegment i).a)

def retainedPhaseProduct : ℂ := ∏ i, S.retainedPhaseRatio i

/-- Endpoint phases are unit-modulus: they are the `zObs` values of
face states via `physical_endpoints_projection`. -/
theorem norm_ordered_endpoint_unitPhase (hα : α ≤ 1/12) (i : Fin S.count) :
    ‖complexUnitPhase (exposureProgressPath y (S.orderedSegment i).a)‖ = 1 ∧
    ‖complexUnitPhase (exposureProgressPath y (S.orderedSegment i).b)‖ = 1 := by
  have h := S.physical_endpoints_projection hα (S.chronologicalOrder i)
  have hFi := norm_zObs_of_mem_Fface h.1
  have hFt := norm_zObs_of_mem_Fface h.2.1
  have ea : complexUnitPhase (exposureProgressPath y
      (S.orderedSegment i).a) =
      zObs (faceProjection ((S.orderedSegment i).physicalPath 0)) :=
    h.2.2.2.2.1.symm
  have eb : complexUnitPhase (exposureProgressPath y
      (S.orderedSegment i).b) =
      zObs (faceProjection ((S.orderedSegment i).physicalPath
        (S.orderedSegment i).duration)) :=
    h.2.2.2.2.2.symm
  exact ⟨by rw [ea]; exact hFi, by rw [eb]; exact hFt⟩

theorem retainedPhaseProduct_of_count_eq_zero (hn : S.count = 0) :
    S.retainedPhaseProduct = 1 := by
  have h0 : (Finset.univ : Finset (Fin S.count)).card = 0 := by
    rw [Finset.card_univ, Fintype.card_fin, hn]
  have he := Finset.card_eq_zero.mp h0
  rw [retainedPhaseProduct, he]
  simp

/-- The progress value at the start is `1`. -/
private theorem progress_start (hstart : y 0 = exposureEuclideanEquiv y0) :
    complexUnitPhase (exposureProgressPath y 0) = 1 := by
  have hp : exposureProgressPath y 0 = 1 := by
    simp [exposureProgressPath, euclideanProgressCLM, hstart, y0]
  rw [hp]
  simp [complexUnitPhase]

/-- The progress value at the end is `-1`. -/
private theorem progress_end (hend : y T = exposureEuclideanEquiv yPi) :
    complexUnitPhase (exposureProgressPath y T) = -1 := by
  have hp : exposureProgressPath y T = -1 := by
    simp [exposureProgressPath, euclideanProgressCLM, hend, yPi]
  rw [hp]
  simp [complexUnitPhase]

theorem retained_phase_product_mul_gap_product (hα : α ≤ 1/12)
    (hstart : y 0 = exposureEuclideanEquiv y0)
    (hend : y T = exposureEuclideanEquiv yPi) :
    S.retainedPhaseProduct *
      (∏ j, complexUnitPhase (exposureProgressPath y (S.gapRight j)) /
        complexUnitPhase (exposureProgressPath y (S.gapLeft j))) = -1 := by
  classical
  have hAnz : ∏ i, complexUnitPhase
      (exposureProgressPath y (S.orderedSegment i).a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have h1 := (S.norm_ordered_endpoint_unitPhase hα i).1
    intro h
    rw [h] at h1
    simp at h1
  have hBnz : ∏ i, complexUnitPhase
      (exposureProgressPath y (S.orderedSegment i).b) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have h1 := (S.norm_ordered_endpoint_unitPhase hα i).2
    intro h
    rw [h] at h1
    simp at h1
  have hprodR : S.retainedPhaseProduct =
      (∏ i, complexUnitPhase
        (exposureProgressPath y (S.orderedSegment i).b)) /
        (∏ i, complexUnitPhase
          (exposureProgressPath y (S.orderedSegment i).a)) := by
    simp only [retainedPhaseProduct, retainedPhaseRatio]
    rw [Finset.prod_div_distrib]
  have hgapRight : ∏ j, complexUnitPhase
      (exposureProgressPath y (S.gapRight j)) =
      (∏ i, complexUnitPhase
        (exposureProgressPath y (S.orderedSegment i).a)) * (-1) := by
    rw [Fin.prod_univ_castSucc]
    rw [show (∏ i : Fin S.count, complexUnitPhase
        (exposureProgressPath y (S.gapRight i.castSucc))) =
      ∏ i, complexUnitPhase (exposureProgressPath y
        (S.orderedSegment i).a) from
      Finset.prod_congr rfl fun i _ => by rw [S.gapRight_castSucc]]
    rw [S.gapRight_last, progress_end hend]
  have hgapLeft : ∏ j, complexUnitPhase
      (exposureProgressPath y (S.gapLeft j)) =
      1 * ∏ i, complexUnitPhase (exposureProgressPath y
        (S.orderedSegment i).b) := by
    rw [Fin.prod_univ_succ, S.gapLeft_zero,
      show (∏ i : Fin S.count, complexUnitPhase
        (exposureProgressPath y (S.gapLeft i.succ))) =
      ∏ i, complexUnitPhase (exposureProgressPath y
        (S.orderedSegment i).b) from
      Finset.prod_congr rfl fun i _ => by rw [S.gapLeft_succ],
      progress_start hstart]
  rw [hprodR, Finset.prod_div_distrib, hgapRight, hgapLeft]
  field_simp [hAnz, hBnz]

theorem retained_phase_and_error {K : NNReal}
    (hT : 0 ≤ T) (hα : α ≤ 1/12)
    (hy : LipschitzWith K y) (hu : Measurable u)
    (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hstart : y 0 = exposureEuclideanEquiv y0)
    (hend : y T = exposureEuclideanEquiv yPi)
    (hβ : β ≤ 1/12) :
    S.retainedPhaseProduct = -phaseFactor (-S.discardedAngularIntegral) ∧
      |S.discardedAngularIntegral| ≤ 8 * T * Real.sqrt β := by
  obtain ⟨-, -, hGap, hE, -⟩ :=
    S.chronological_gap_phase_accounting hT hy hu hub hdom hode hβ
  have hTel := S.retained_phase_product_mul_gap_product hα hstart hend
  rw [hGap] at hTel
  have hpfE : phaseFactor S.discardedAngularIntegral ≠ 0 := by
    intro h
    have h1 := norm_phaseFactor S.discardedAngularIntegral
    rw [h] at h1
    simp at h1
  have key : phaseFactor S.discardedAngularIntegral *
      phaseFactor (-S.discardedAngularIntegral) = 1 := by
    rw [← phaseFactor_add, add_neg_cancel, phaseFactor_zero]
  have hinv : phaseFactor (-S.discardedAngularIntegral) =
      (phaseFactor S.discardedAngularIntegral)⁻¹ :=
    eq_inv_of_mul_eq_one_right key
  constructor
  · calc S.retainedPhaseProduct
        = S.retainedPhaseProduct *
            (phaseFactor S.discardedAngularIntegral *
              phaseFactor (-S.discardedAngularIntegral)) := by
          rw [key, mul_one]
      _ = (S.retainedPhaseProduct *
            phaseFactor S.discardedAngularIntegral) *
            phaseFactor (-S.discardedAngularIntegral) := by ring
      _ = -1 * phaseFactor (-S.discardedAngularIntegral) := by rw [hTel]
      _ = -phaseFactor (-S.discardedAngularIntegral) := by ring
  · exact hE

end CZExposure.FiniteExcursionSelection
