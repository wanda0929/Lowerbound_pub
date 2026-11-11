import RequestProject.AppendixE.SectorPhase
import RequestProject.AppendixE.EndpointRepair
import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.ControlLieAlgebra
import RequestProject.AppendixE.RelaxedSubsolution
/-!
# Axiom audit: endpoint projection and phase alignment

Expected: all results use only `[propext, Classical.choice, Quot.sound]`.
No additional geometric or analytical axiom is introduced, and no
declaration below is closed by `sorryAx` or an `External` axiom.

The projection and endpoint-projection statements use the explicit
sufficient cutoff `cost x ≤ 1/12` (respectively `α ≤ 1/12`) for the
small-cost region of the manuscript's Step 3. `faceProjection_mem`, `zObs_faceProjection`,
`norm_faceProjection_sub_le`, and `physical_endpoints_projection` carry
it as an explicit hypothesis — no hidden assumption is added.  The norm
in `norm_faceProjection_sub_le` and `norm_faceCZTarget_sub_le` is the
ambient sup norm on `State = Fin 8 → ℝ`, not the Riemannian distance of
the manuscript's ball-box argument.

Edge checks below: `x₀ ∈ F` explicitly and the projection fixes `x₀`;
the static repair fixes every already-CZ state; and `faceAlign p p` is
the identity on every state.
-/

open CZExposure

/-! ## FaceProjection.lean declarations -/

#check @g1_mkState
#check @r1_mkState
#check @g2_mkState
#check @r2_mkState
#check @state_ext
#check @mkState_eta
#check @complexUnitPhase_of_norm_one
#check @complexUnitPhase_mul
#check @complexUnitPhase_conj
#check @norm_complexUnitPhase_sub_self
#check @norm_complexUnitPhase_sub_unit_le
#check @norm_ground_of_mem_Fface
#check @norm_zObs_of_mem_Fface
#check @mem_XCZ_iff_zObs_eq_neg_one
#check @faceProjection
#check @cost_faceProjection
#check @faceProjection_mem
#check @zObs_faceProjection
#check @faceProjection_eq_self
#check @norm_faceProjection_sub_le
#check @faceCZTarget
#check @faceCZTarget_mem
#check @norm_faceCZTarget_sub_le
#check @norm_faceCZTarget_sub_le_phase
#check @PositiveExposureSegment.zObs_liftedState
#check @FiniteExcursionSelection.physical_endpoints_projection

/-! ## SectorPhase.lean declarations -/

#check @sectorPhase
#check @sectorPhaseLM
#check @sectorPhaseCLM
#check @sectorPhaseCLM_apply
#check @sectorPhase_mem_Xset
#check @sectorPhase_mem_Fface
#check @cost_sectorPhase
#check @zObs_sectorPhase
#check @sectorPhase_vf
#check @hasDerivAt_sectorPhase
#check @sectorPhase_integralEquation
#check @zObs_ratio_sectorPhase
#check @unitPhase_ratio_sectorPhase
#check @faceAlign
#check @faceAlign_unit
#check @faceAlign_source
#check @faceAlign_cost
#check @faceAlign_zObs_ratio

/-! ## Edge examples -/

/-- The initial state `x₀` lies on the zero-cost face, and the
projection fixes it. -/
example : x0 ∈ Fface ∧ faceProjection x0 = x0 := by
  have hg1 : g1 x0 = 1 := by
    apply Complex.ext <;> simp [x0, g1]
  have hr1 : r1 x0 = 0 := by
    apply Complex.ext <;> simp [x0, r1]
  have hg2 : g2 x0 = 1 := by
    apply Complex.ext <;> simp [x0, g2]
  have hr2 : r2 x0 = 0 := by
    apply Complex.ext <;> simp [x0, r2]
  have hx0F : x0 ∈ Fface :=
    ⟨⟨by rw [hg1, hr1]; simp, by rw [hg2, hr2]; simp⟩, hr1, hr2⟩
  exact ⟨hx0F, faceProjection_eq_self hx0F⟩

/-- The static repair fixes every state already on the exact CZ orbit. -/
example {x : State} (hx : x ∈ XCZ) : faceCZTarget x = x := by
  obtain ⟨hxX, hr1, hr2, hg⟩ := hx
  apply state_ext <;> simp [faceCZTarget, hr1, hr2, hg]

/-- `faceAlign p p` is the identity on every state. -/
example {p x : State} (hp : p ∈ Fface) : faceAlign p p x = x := by
  obtain ⟨hgp1, hgp2⟩ := norm_ground_of_mem_Fface hp
  have hg1 : g1 p ≠ 0 := norm_ne_zero_iff.mp (by rw [hgp1]; norm_num)
  have hg2 : g2 p ≠ 0 := norm_ne_zero_iff.mp (by rw [hgp2]; norm_num)
  show sectorPhase (g1 p / g1 p) (g2 p / g2 p) x = x
  rw [div_self hg1, div_self hg2]
  apply state_ext <;> simp [sectorPhase]

/-! ## Axiom reports -/

#print axioms g1_mkState
#print axioms r1_mkState
#print axioms g2_mkState
#print axioms r2_mkState
#print axioms state_ext
#print axioms mkState_eta
#print axioms complexUnitPhase_of_norm_one
#print axioms complexUnitPhase_mul
#print axioms complexUnitPhase_conj
#print axioms norm_complexUnitPhase_sub_self
#print axioms norm_complexUnitPhase_sub_unit_le
#print axioms norm_ground_of_mem_Fface
#print axioms norm_zObs_of_mem_Fface
#print axioms mem_XCZ_iff_zObs_eq_neg_one
#print axioms faceProjection
#print axioms cost_faceProjection
#print axioms faceProjection_mem
#print axioms zObs_faceProjection
#print axioms faceProjection_eq_self
#print axioms norm_faceProjection_sub_le
#print axioms faceCZTarget
#print axioms faceCZTarget_mem
#print axioms norm_faceCZTarget_sub_le
#print axioms norm_faceCZTarget_sub_le_phase
#print axioms PositiveExposureSegment.zObs_liftedState
#print axioms FiniteExcursionSelection.physical_endpoints_projection
#print axioms sectorPhase
#print axioms sectorPhaseLM
#print axioms sectorPhaseCLM
#print axioms sectorPhaseCLM_apply
#print axioms sectorPhase_mem_Xset
#print axioms sectorPhase_mem_Fface
#print axioms cost_sectorPhase
#print axioms zObs_sectorPhase
#print axioms sectorPhase_vf
#print axioms hasDerivAt_sectorPhase
#print axioms sectorPhase_integralEquation
#print axioms zObs_ratio_sectorPhase
#print axioms unitPhase_ratio_sectorPhase
#print axioms faceAlign
#print axioms faceAlign_unit
#print axioms faceAlign_source
#print axioms faceAlign_cost
#print axioms faceAlign_zObs_ratio

/-!
# Audit: conditional endpoint/phase repair under `LocalSteering`

Aggregate-import axiom audit of `QuantitativeSteering.lean` and
`EndpointRepair.lean`, composed with `StateGeometry`,
`ControlLieAlgebra`, and `RelaxedSubsolution`.  Expected axioms are
only `[propext, Classical.choice, Quot.sound]`.

`LocalSteering` is a plain structure: no inhabitant is constructed
anywhere in the repository, and every repair theorem takes `H`
visibly.  There is no steering-existence axiom.
-/

open CZExposure MeasureTheory
open scoped NNReal ENNReal

namespace CZExposure

/-! ## The explicit hypothesis and its cost bounds -/

#check @LocalSteering.mk
#print axioms LocalSteering
#check @LocalSteering.timeBound
#print axioms LocalSteering.timeBound
#check @LocalSteering.exposureBound
#print axioms LocalSteering.exposureBound
#check @LocalSteering.timeBound_nonneg
#print axioms LocalSteering.timeBound_nonneg
#check @LocalSteering.timeBound_mono
#print axioms LocalSteering.timeBound_mono
#check @LocalSteering.timeBound_zero
#print axioms LocalSteering.timeBound_zero
#check @LocalSteering.exposureBound_zero
#print axioms LocalSteering.exposureBound_zero
#check @LocalSteering.exposureBound_nonneg
#print axioms LocalSteering.exposureBound_nonneg
#check @LocalSteering.exposureBound_eq
#print axioms LocalSteering.exposureBound_eq
#check @LocalSteering.exists_from_face
#print axioms LocalSteering.exists_from_face
#check @LocalSteering.exists_to_face
#print axioms LocalSteering.exists_to_face
#check @LocalSteering.projection_pair_exposureBound_eq
#print axioms LocalSteering.projection_pair_exposureBound_eq

/-! ## Conditional repair theorems — full types displayed, including
the `H : LocalSteering` variable and the cutoff hypotheses -/

#check @LocalSteering.exists_repaired_faceBlock
#print axioms LocalSteering.exists_repaired_faceBlock
#check @LocalSteering.exists_phase_repair
#print axioms LocalSteering.exists_phase_repair
#check @LocalSteering.exists_closed_pulse
#print axioms LocalSteering.exists_closed_pulse

/-! ## Edge examples: zero-distance boundary -/

namespace Edge

/-! `timeBound 0 = exposureBound 0 = 0`, so `α = 0` and `θ = 0` inputs
carry zero overhead. -/

example (H : LocalSteering) : H.timeBound 0 = 0 := H.timeBound_zero

example (H : LocalSteering) : H.exposureBound 0 = 0 :=
  H.exposureBound_zero

example (H : LocalSteering) : H.exposureBound (32 * Real.sqrt 0) = 0 := by
  simp

/-! `α = 0`: the projection points of `unitZero` coincide with its
face endpoints, so the repaired block has zero total overhead. -/

example (H : LocalSteering) :
    ∃ B : FaceBlock,
      B.initial = faceProjection
          ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).path 0) ∧
      B.terminal = faceProjection
          ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).path
            (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).duration) ∧
      B.segment.duration ≤
        (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).duration +
          2 * H.timeBound (32 * Real.sqrt 0) ∧
      B.segment.exposure ≤
        (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).exposure +
          2 * H.exposureBound (32 * Real.sqrt 0) ∧
      B.phaseRatio =
        complexUnitPhase (zObs
          ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).path
            (PhysicalSegment.unitZero x0
              FaceBlock.x0_mem_Fface.1).duration)) /
          complexUnitPhase (zObs
            ((PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).path 0)) :=
  H.exists_repaired_faceBlock
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1)
    le_rfl (by norm_num)
    (by simp [cost, x0, r1, r2];
        rw [show (⟨(0:ℝ),(0:ℝ)⟩ : ℂ) = 0 from rfl]; norm_num)
    (by simp [cost, x0, r1, r2];
        rw [show (⟨(0:ℝ),(0:ℝ)⟩ : ℂ) = 0 from rfl]; norm_num)
    (by simp; exact H.radius_pos.le)

/-! Its duration/exposure upper bounds collapse to the original
segment's (zero) quantities. -/
example (H : LocalSteering) :
    (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).duration +
        2 * H.timeBound (32 * Real.sqrt 0) = 0 ∧
      (PhysicalSegment.unitZero x0 FaceBlock.x0_mem_Fface.1).exposure +
        2 * H.exposureBound (32 * Real.sqrt 0) = 0 := by
  simp

/-! `θ = 0`: any face state with `z = -1` (i.e. already on `XCZ`)
repairs to itself with zero overhead; the hypothesis is kept generic
rather than asserting a constructed state. -/
example (H : LocalSteering) {x : State} (hx : x ∈ Fface)
    (h : zObs x = -phaseFactor (0 : ℝ)) :
    ∃ R : FaceBlock, R.initial = x ∧ R.terminal = faceCZTarget x ∧
      R.segment.duration ≤ H.timeBound |(0 : ℝ)| ∧
      R.segment.exposure ≤ H.exposureBound |(0 : ℝ)| ∧
      R.phaseRatio = phaseFactor (-(0 : ℝ)) :=
  H.exists_phase_repair hx h (by simpa using H.radius_pos.le)

example : |(0 : ℝ)| = 0 := by simp
example (H : LocalSteering) : H.timeBound |(0 : ℝ)| = 0 := by simp
example (H : LocalSteering) : H.exposureBound |(0 : ℝ)| = 0 := by simp

/-! NOTE: no `LocalSteering` inhabitant is constructed anywhere; the
structure's `connect` field remains an unproved guarantee carried as
a hypothesis. -/

end Edge

end CZExposure
