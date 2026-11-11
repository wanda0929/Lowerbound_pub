module
public import RequestProject.AppendixE.QuantitativeSteering
public import RequestProject.AppendixE.UnitControlRealization
public import RequestProject.AppendixE.LocalSteeringConstruction

/-!
# Conditional endpoint repair and terminal phase correction

The reusable results take `H : LocalSteering` visibly; the final
system-specific results instantiate it with the proved finite-pulse construction.
`faceProjection` repairs low-cost endpoints into face
states while preserving the normalized endpoint phase ratio, and
`faceCZTarget` corrects a small terminal phase error by an actual
physical trajectory.  `toUnitPulse` then packages the completed
disk-control segment into an exact-CZ `Pulse`.
-/

@[expose] public section

noncomputable section

namespace CZExposure.LocalSteering

open MeasureTheory Set
open scoped NNReal ENNReal

variable (H : LocalSteering)

/-- Repair both ends of a supplied low-endpoint-cost segment.
Steering remains explicit. -/
theorem exists_repaired_faceBlock (P : PhysicalSegment) {α : ℝ}
    (hα : 0 ≤ α) (hcut : α ≤ 1/12)
    (hstart : cost (P.path 0) ≤ α)
    (hend : cost (P.path P.duration) ≤ α)
    (hnear : 32 * Real.sqrt α ≤ H.radius) :
    ∃ B : FaceBlock,
      B.initial = faceProjection (P.path 0) ∧
      B.terminal = faceProjection (P.path P.duration) ∧
      B.segment.duration ≤ P.duration + 2 * H.timeBound (32 * Real.sqrt α) ∧
      B.segment.exposure ≤ P.exposure +
        2 * H.exposureBound (32 * Real.sqrt α) ∧
      B.phaseRatio =
        complexUnitPhase (zObs (P.path P.duration)) /
          complexUnitPhase (zObs (P.path 0)) := by
  have hxX : P.path 0 ∈ Xset :=
    P.path_mem 0 (Set.left_mem_Icc.mpr P.duration_nonneg)
  have hyX : P.path P.duration ∈ Xset :=
    P.path_mem P.duration (Set.right_mem_Icc.mpr P.duration_nonneg)
  have hcx : cost (P.path 0) ≤ 1/12 := hstart.trans hcut
  have hcy : cost (P.path P.duration) ≤ 1/12 := hend.trans hcut
  have hpxF := faceProjection_mem hxX hcx
  have hpyF := faceProjection_mem hyX hcy
  have hsqrt : (0:ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hdpx : ‖P.path 0 - faceProjection (P.path 0)‖ ≤
      32 * Real.sqrt α := by
    rw [norm_sub_rev]
    calc ‖faceProjection (P.path 0) - P.path 0‖
        ≤ 32 * Real.sqrt (cost (P.path 0)) :=
          norm_faceProjection_sub_le hxX hcx
      _ ≤ 32 * Real.sqrt α :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstart) (by norm_num)
  have hdpy : ‖faceProjection (P.path P.duration) - P.path P.duration‖ ≤
      32 * Real.sqrt α := by
    calc ‖faceProjection (P.path P.duration) - P.path P.duration‖
        ≤ 32 * Real.sqrt (cost (P.path P.duration)) :=
          norm_faceProjection_sub_le hyX hcy
      _ ≤ 32 * Real.sqrt α :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hend) (by norm_num)
  obtain ⟨L, hL0, hLD, hLdur, hLex⟩ :=
    H.exists_from_face hpxF hxX hdpx hnear
  obtain ⟨R, hR0, hRD, hRdur, hRex⟩ :=
    H.exists_to_face hyX hpyF hdpy hnear
  have hmatch1 : L.path L.duration = P.path 0 := hLD
  have hmatch2 : (L.concat P hmatch1).path ((L.concat P hmatch1).duration)
      = R.path 0 := by
    show (L.concat P hmatch1).path (L.duration + P.duration) = R.path 0
    rw [PhysicalSegment.concat_terminal]
    exact hR0.symm
  set Q := (L.concat P hmatch1).concat R hmatch2 with hQ
  have hQ0 : Q.path 0 = faceProjection (P.path 0) := by
    rw [hQ, PhysicalSegment.concat_initial, PhysicalSegment.concat_initial]
    exact hL0
  have hQD : Q.path Q.duration = faceProjection (P.path P.duration) := by
    have h := PhysicalSegment.concat_terminal (L.concat P hmatch1) R hmatch2
    calc Q.path Q.duration = R.path R.duration := h
      _ = faceProjection (P.path P.duration) := hRD
  refine ⟨⟨Q, (by rw [hQ0]; exact hpxF), (by rw [hQD]; exact hpyF)⟩,
    hQ0, hQD, ?_, ?_, ?_⟩
  · have hd1 := PhysicalSegment.concat_duration (L.concat P hmatch1) R hmatch2
    have hd2 := PhysicalSegment.concat_duration L P hmatch1
    have hdeq : Q.duration = L.duration + P.duration + R.duration := by
      rw [hQ, hd1, hd2]
    show Q.duration ≤ P.duration + 2 * H.timeBound (32 * Real.sqrt α)
    rw [hdeq]
    linarith [hLdur, hRdur]
  · have he1 := PhysicalSegment.concat_exposure (L.concat P hmatch1) R hmatch2
    have he2 := PhysicalSegment.concat_exposure L P hmatch1
    have heeq : Q.exposure = L.exposure + P.exposure + R.exposure := by
      rw [hQ, he1, he2]
    show Q.exposure ≤ P.exposure + 2 * H.exposureBound (32 * Real.sqrt α)
    rw [heeq]
    linarith [hLex, hRex]
  · show zObs (Q.path Q.duration) / zObs (Q.path 0) =
        complexUnitPhase (zObs (P.path P.duration)) /
          complexUnitPhase (zObs (P.path 0))
    rw [hQD, hQ0, zObs_faceProjection hxX hcx,
      zObs_faceProjection hyX hcy]

/-- A terminal face-state phase error is repaired by an actual
supplied-steering trajectory. -/
theorem exists_phase_repair {x : State} (hx : x ∈ Fface) {θ : ℝ}
    (hphase : zObs x = -phaseFactor θ) (hnear : |θ| ≤ H.radius) :
    ∃ R : FaceBlock, R.initial = x ∧ R.terminal = faceCZTarget x ∧
      R.segment.duration ≤ H.timeBound |θ| ∧
      R.segment.exposure ≤ H.exposureBound |θ| ∧
      R.phaseRatio = phaseFactor (-θ) := by
  have htCZ : faceCZTarget x ∈ XCZ := faceCZTarget_mem hx
  have htF : faceCZTarget x ∈ Fface := ⟨htCZ.1, htCZ.2.1, htCZ.2.2.1⟩
  have hdist := norm_faceCZTarget_sub_le_phase hx hphase
  obtain ⟨Q, hQ0, hQD, hQdur, hQex⟩ :=
    H.exists_from_face hx htF.1 hdist hnear
  have hzT : zObs (faceCZTarget x) = -1 :=
    (mem_XCZ_iff_zObs_eq_neg_one htF).mp htCZ
  have hpf : phaseFactor θ ≠ 0 := by
    intro h
    have := norm_phaseFactor θ
    rw [h] at this
    simp at this
  have key : phaseFactor (-θ) * phaseFactor θ = 1 := by
    rw [← phaseFactor_add, neg_add_cancel, phaseFactor_zero]
  refine ⟨⟨Q, (by rw [hQ0]; exact hx), (by rw [hQD]; exact htF)⟩,
    hQ0, hQD, hQdur, hQex, ?_⟩
  show zObs (Q.path Q.duration) / zObs (Q.path 0) = phaseFactor (-θ)
  rw [hQD, hQ0, hzT, hphase]
  rw [div_eq_iff (neg_ne_zero.mpr hpf), mul_neg, key]

/-- Close a supplied `x0`-to-`F` disk-control segment and normalize it
into a `Pulse`. -/
theorem exists_closed_pulse (P : PhysicalSegment)
    (hstart : P.path 0 = x0) (hend : P.path P.duration ∈ Fface)
    {θ : ℝ} (hphase : zObs (P.path P.duration) = -phaseFactor θ)
    (hnear : |θ| ≤ H.radius) :
    ∃ γ : Pulse,
      γ.S ≤ P.duration + H.timeBound |θ| ∧
      γ.exposure ≤ P.exposure + H.exposureBound |θ| := by
  obtain ⟨R, hRi, hRt, hRdur, hRex, _⟩ :=
    H.exists_phase_repair hend hphase hnear
  have hmatch : P.path P.duration = R.segment.path 0 := hRi.symm
  set Q := P.concat R.segment hmatch with hQ
  have hQ0 : Q.path 0 = x0 := by
    rw [hQ, PhysicalSegment.concat_initial]
    exact hstart
  have hQD : Q.path Q.duration ∈ XCZ := by
    have hterm : Q.path Q.duration = faceCZTarget (P.path P.duration) := by
      have h := PhysicalSegment.concat_terminal P R.segment hmatch
      rw [hQ]
      calc Q.path Q.duration = R.segment.path R.segment.duration := h
        _ = faceCZTarget (P.path P.duration) := hRt
    rw [hterm]
    exact faceCZTarget_mem hend
  refine ⟨Q.toUnitPulse hQ0 hQD, ?_, ?_⟩
  · have hd1 := PhysicalSegment.toUnitPulse_duration_le Q hQ0 hQD
    have hd2 := PhysicalSegment.concat_duration P R.segment hmatch
    have hT := H.timeBound_nonneg (abs_nonneg θ)
    linarith [hd1, hd2, hRdur]
  · have he1 := PhysicalSegment.toUnitPulse_exposure_le Q hQ0 hQD
    have he2 := PhysicalSegment.concat_exposure P R.segment hmatch
    have hT := H.exposureBound_nonneg (abs_nonneg θ)
    linarith [he1, he2, hRex]

end CZExposure.LocalSteering

namespace CZExposure.LocalSteeringConstruction

/-- Physical endpoint repair using the constructed system-specific steering. -/
theorem exists_repaired_faceBlock (P : PhysicalSegment) {α : ℝ}
    (hα : 0 ≤ α) (hcut : α ≤ 1/12)
    (hstart : cost (P.path 0) ≤ α) (hend : cost (P.path P.duration) ≤ α)
    (hnear : 32 * Real.sqrt α ≤ physicalLocalSteering.radius) :
    ∃ B : FaceBlock,
      B.initial = faceProjection (P.path 0) ∧
      B.terminal = faceProjection (P.path P.duration) ∧
      B.segment.duration ≤ P.duration + 2 * physicalLocalSteering.timeBound (32 * Real.sqrt α) ∧
      B.segment.exposure ≤ P.exposure + 2 * physicalLocalSteering.exposureBound (32 * Real.sqrt α) ∧
      B.phaseRatio = complexUnitPhase (zObs (P.path P.duration)) /
        complexUnitPhase (zObs (P.path 0)) :=
  physicalLocalSteering.exists_repaired_faceBlock P hα hcut hstart hend hnear

/-- Exact CZ closure with no supplied steering package. -/
theorem exists_closed_pulse (P : PhysicalSegment)
    (hstart : P.path 0 = x0) (hend : P.path P.duration ∈ Fface)
    {θ : ℝ} (hphase : zObs (P.path P.duration) = -phaseFactor θ)
    (hnear : |θ| ≤ physicalLocalSteering.radius) :
    ∃ γ : Pulse,
      γ.S ≤ P.duration + physicalLocalSteering.timeBound |θ| ∧
      γ.exposure ≤ P.exposure + physicalLocalSteering.exposureBound |θ| :=
  physicalLocalSteering.exists_closed_pulse P hstart hend hphase hnear

end CZExposure.LocalSteeringConstruction
