import RequestProject.AppendixE.ExcursionAssembly
import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.ControlLieAlgebra
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Excursion assembly audit

Axiom audit for the finite repaired-excursion assembly and the
conditional pulse budget. The repaired-block, assembly, and pulse
constructions explicitly require `H : LocalSteering`; no inhabitant
of `LocalSteering` is constructed or assumed by an axiom in this
development. The final
trajectory-to-pulse theorem takes no supplied repaired blocks and no
supplied phase-product identity; no `ε`-limit claim is made (choosing
`α`, taking limits, and proving `H` remain open).
-/

noncomputable section

namespace CZExposure

/-! ## Quantitative-steering helper -/

#check @LocalSteering.exposureBound_mono
#print axioms LocalSteering.exposureBound_mono

/-! ## Retained/gap phase accounting -/

#check @FiniteExcursionSelection.retainedPhaseRatio
#print axioms FiniteExcursionSelection.retainedPhaseRatio
#check @FiniteExcursionSelection.retainedPhaseProduct
#print axioms FiniteExcursionSelection.retainedPhaseProduct
#check @FiniteExcursionSelection.norm_ordered_endpoint_unitPhase
#print axioms FiniteExcursionSelection.norm_ordered_endpoint_unitPhase
#check @FiniteExcursionSelection.retainedPhaseProduct_of_count_eq_zero
#print axioms FiniteExcursionSelection.retainedPhaseProduct_of_count_eq_zero
#check @FiniteExcursionSelection.retained_phase_product_mul_gap_product
#print axioms FiniteExcursionSelection.retained_phase_product_mul_gap_product
#check @FiniteExcursionSelection.retained_phase_and_error
#print axioms FiniteExcursionSelection.retained_phase_and_error

/-! ## Repaired blocks, assembly, and pulse budget -/

#check @FiniteExcursionSelection.exists_repaired_blocks
#print axioms FiniteExcursionSelection.exists_repaired_blocks
#check @FiniteExcursionSelection.exists_repaired_assembly
#print axioms FiniteExcursionSelection.exists_repaired_assembly
#check @FiniteExcursionSelection.exists_pulse_with_count_budget
#print axioms FiniteExcursionSelection.exists_pulse_with_count_budget
#check @FiniteExcursionSelection.count_bound_half_cutoff
#print axioms FiniteExcursionSelection.count_bound_half_cutoff

/-! ## Trajectory-to-pulse theorem: full type shows `H`, all cutoffs,
radius constraints, and the trajectory/derivative hypotheses -/

#check @LocalSteering.exists_pulse_of_exposure_trajectory
#print axioms LocalSteering.exists_pulse_of_exposure_trajectory

/-! ## Edge examples -/

/-- Empty selection: the retained product is `1` (instantiates the
public lemma; no positivity on `count` is needed). -/
example {T α β : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
    (S : FiniteExcursionSelection T α β y u) (hn : S.count = 0) :
    S.retainedPhaseProduct = 1 :=
  S.retainedPhaseProduct_of_count_eq_zero hn

/-- Sign-cancellation: `exp(iE) * exp(-iE) = 1`, the minus sign used
when solving the telescope for the retained product. -/
example (E : ℝ) : phaseFactor E * phaseFactor (-E) = 1 := by
  rw [← phaseFactor_add, add_neg_cancel, phaseFactor_zero]

/-- The empty-list assembly is an actual `FaceBlock` starting at
`x0` with zero exposure and trivial phase ratio — the `count = 0`
boundary of `exists_repaired_assembly`. -/
example : (FaceBlock.assemble x0 FaceBlock.x0_mem_Fface []).initial = x0 :=
  FaceBlock.assemble_initial x0 FaceBlock.x0_mem_Fface []

example :
    (FaceBlock.assemble x0 FaceBlock.x0_mem_Fface []).segment.exposure = 0 := by
  rw [FaceBlock.assemble_exposure]
  simp

example :
    (FaceBlock.assemble x0 FaceBlock.x0_mem_Fface []).phaseRatio = 1 := by
  rw [FaceBlock.assemble_phaseRatio]
  simp

end CZExposure
