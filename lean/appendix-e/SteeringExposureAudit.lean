import RequestProject.AppendixE.SteeringExposure
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Audit: physical segments and cubic steering exposure

Checks every public declaration introduced in `PhysicalSegment.lean`
and `SteeringExposure.lean`, prints their axiom dependencies, and
elaborates a few edge examples:

* `PhysicalSegment.zero` has zero duration and zero exposure.
* Double reversal returns path and control pointwise.
* Reversing a face-start segment yields a face-terminal segment with
  the same exposure.

The relaxed-subsolution module is also imported to check namespace
compatibility with the existing completeness development.

Expected axiom dependencies: `propext`, `Classical.choice`,
`Quot.sound` only — no `sorryAx`, no external axiom.
-/

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-! ## Public helper declarations -/

#check @uIcc_subset_uIcc_of_mem
#check @mem_Icc_of_mem_uIoc
#check @mem_Icc_sub
#check @PhysicalSegment.vf_neg_control

#print axioms uIcc_subset_uIcc_of_mem
#print axioms mem_Icc_of_mem_uIoc
#print axioms mem_Icc_sub
#print axioms PhysicalSegment.vf_neg_control

/-! ## `PhysicalSegment` structure and basic interface -/

#check @PhysicalSegment
#check @PhysicalSegment.mk
#check @PhysicalSegment.exposure
#check @PhysicalSegment.velocity_integrable_subinterval
#check @PhysicalSegment.integral_velocity
#check @PhysicalSegment.path_lipschitzOn
#check @PhysicalSegment.continuousOn_path
#check @PhysicalSegment.cost_intervalIntegrable
#check @PhysicalSegment.exposure_nonneg

#print axioms PhysicalSegment
#print axioms PhysicalSegment.exposure
#print axioms PhysicalSegment.velocity_integrable_subinterval
#print axioms PhysicalSegment.integral_velocity
#print axioms PhysicalSegment.path_lipschitzOn
#print axioms PhysicalSegment.continuousOn_path
#print axioms PhysicalSegment.cost_intervalIntegrable
#print axioms PhysicalSegment.exposure_nonneg

/-! ## Zero, retained realization, reversal -/

#check @PhysicalSegment.zero
#check @PhysicalSegment.zero_exposure
#check @PhysicalSegment.ofPositiveExposureSegment
#check @PhysicalSegment.ofPositiveExposureSegment_exposure
#check @PhysicalSegment.ofPositiveExposureSegment_endpoints
#check @PhysicalSegment.reverse
#check @PhysicalSegment.reverse_duration
#check @PhysicalSegment.reverse_path
#check @PhysicalSegment.reverse_control
#check @PhysicalSegment.reverse_endpoints
#check @PhysicalSegment.reverse_exposure

#print axioms PhysicalSegment.zero
#print axioms PhysicalSegment.zero_exposure
#print axioms PhysicalSegment.ofPositiveExposureSegment
#print axioms PhysicalSegment.ofPositiveExposureSegment_exposure
#print axioms PhysicalSegment.ofPositiveExposureSegment_endpoints
#print axioms PhysicalSegment.reverse
#print axioms PhysicalSegment.reverse_duration
#print axioms PhysicalSegment.reverse_path
#print axioms PhysicalSegment.reverse_control
#print axioms PhysicalSegment.reverse_endpoints
#print axioms PhysicalSegment.reverse_exposure

/-! ## Rephase and `Pulse` bridge -/

#check @PhysicalSegment.rephase
#check @PhysicalSegment.rephase_duration
#check @PhysicalSegment.rephase_path
#check @PhysicalSegment.rephase_control
#check @PhysicalSegment.rephase_exposure
#check @PhysicalSegment.toPulse
#check @PhysicalSegment.toPulse_exposure

#print axioms PhysicalSegment.rephase
#print axioms PhysicalSegment.rephase_duration
#print axioms PhysicalSegment.rephase_path
#print axioms PhysicalSegment.rephase_control
#print axioms PhysicalSegment.rephase_exposure
#print axioms PhysicalSegment.toPulse
#print axioms PhysicalSegment.toPulse_exposure

/-! ## Sharp bounds and cubic exposure -/

#check @norm_fC_rydberg1_le
#check @norm_fC_rydberg2_le
#check @PhysicalSegment.rydberg_integralEquations
#check @PhysicalSegment.norm_r1_le_time
#check @PhysicalSegment.norm_r2_le_time
#check @PhysicalSegment.cost_le_time_sq_div_four
#check @PhysicalSegment.cumulative_exposure_le_cube_div_twelve
#check @PhysicalSegment.exposure_le_cube_div_twelve
#check @PhysicalSegment.cost_le_remaining_time_sq_div_four
#check @PhysicalSegment.exposure_le_cube_div_twelve_of_end

#print axioms norm_fC_rydberg1_le
#print axioms norm_fC_rydberg2_le
#print axioms PhysicalSegment.rydberg_integralEquations
#print axioms PhysicalSegment.norm_r1_le_time
#print axioms PhysicalSegment.norm_r2_le_time
#print axioms PhysicalSegment.cost_le_time_sq_div_four
#print axioms PhysicalSegment.cumulative_exposure_le_cube_div_twelve
#print axioms PhysicalSegment.exposure_le_cube_div_twelve
#print axioms PhysicalSegment.cost_le_remaining_time_sq_div_four
#print axioms PhysicalSegment.exposure_le_cube_div_twelve_of_end

/-! ## Edge examples -/

/-- The zero segment has duration `0` and zero exposure. -/
example (x : State) (hx : x ∈ Xset) :
    (PhysicalSegment.zero x hx).duration = 0 ∧
      (PhysicalSegment.zero x hx).exposure = 0 :=
  ⟨rfl, PhysicalSegment.zero_exposure x hx⟩

/-- Double reversal returns the path and the control pointwise. -/
example (P : PhysicalSegment) (s : ℝ) :
    P.reverse.reverse.path s = P.path s ∧
      P.reverse.reverse.control s = P.control s := by
  constructor
  · show P.path (P.duration - (P.duration - s)) = P.path s
    rw [sub_sub_self]
  · show -(-P.control (P.duration - (P.duration - s))) = P.control s
    rw [sub_sub_self, neg_neg]

/-- Reversing a face-start segment yields a face-terminal segment with
the same exposure. -/
example (P : PhysicalSegment) (h : P.path 0 ∈ Fface) :
    P.reverse.path P.reverse.duration ∈ Fface ∧
      P.reverse.exposure = P.exposure := by
  refine ⟨?_, P.reverse_exposure⟩
  rw [PhysicalSegment.reverse_path, PhysicalSegment.reverse_duration,
    sub_self]
  exact h

end CZExposure
