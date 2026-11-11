import RequestProject.AppendixE.LowCostPhase

/-!
# Audit: phase transport across low-cost gaps

All audited results must use only `propext`, `Classical.choice`, and
`Quot.sound`.  No `sorryAx`, no external geometry or superposition axiom.
-/

noncomputable section

namespace CZExposure

open MeasureTheory Set

-- Basic phase-factor and unit-phase algebra.
#check @complexUnitPhase
#check @phaseFactor
#check @complexPhaseLift
#check @phaseFactor_zero
#check @phaseFactor_add
#check @norm_phaseFactor
#check @norm_complexUnitPhase
#check @phaseFactor_arg
#check @phaseFactor_sum
#check @norm_phaseFactor_sub_one_le
#check @lipschitz_phaseFactor
#check @hasDerivAt_phaseFactor_comp
#check @contDiffAt_complexUnitPhase
#check @hasDerivAt_complexUnitPhase
#check @complex_phase_transport
#check @complexPhaseLift_spec
#check @exposurePhaseIncrement
#check @low_cost_phase_lift
#check @low_cost_phase_transport
#check @low_cost_normalized_progress_increment_le
#check @finite_low_cost_phase_accounting
#check @FiniteExcursionSelection.discarded_phase_product_of_gap_cover

#print axioms complexUnitPhase
#print axioms phaseFactor
#print axioms complexPhaseLift
#print axioms phaseFactor_zero
#print axioms phaseFactor_add
#print axioms norm_phaseFactor
#print axioms norm_complexUnitPhase
#print axioms phaseFactor_arg
#print axioms phaseFactor_sum
#print axioms norm_phaseFactor_sub_one_le
#print axioms lipschitz_phaseFactor
#print axioms hasDerivAt_phaseFactor_comp

-- Normalization regularity and derivative.
#print axioms contDiffAt_complexUnitPhase
#print axioms hasDerivAt_complexUnitPhase

-- Generic transport and the real phase lift.
#print axioms complex_phase_transport
#print axioms complexPhaseLift_spec

-- Low-cost-gap application.
#print axioms exposurePhaseIncrement
#print axioms low_cost_phase_lift
#print axioms low_cost_phase_transport
#print axioms low_cost_normalized_progress_increment_le

-- Finite gap family.
#print axioms finite_low_cost_phase_accounting

-- Selected discarded-set cover corollary.
#print axioms FiniteExcursionSelection.discarded_phase_product_of_gap_cover

/-- Winding example: for `f(t) = exp(it)` the angular-rate integrand is `1`,
    so the integral over `[0, 2π]` is `2π` even though the unit-phase
    endpoints coincide — the lift, not the principal argument, records the
    turn. -/
example :
    (∫ t in (0:ℝ)..(2 * Real.pi),
      ((Complex.I * phaseFactor t) / phaseFactor t).im) = 2 * Real.pi := by
  have hz : ∀ t : ℝ, phaseFactor t ≠ 0 := fun t => by
    rw [← norm_ne_zero_iff, norm_phaseFactor]
    norm_num
  have e : (fun t => ((Complex.I * phaseFactor t) / phaseFactor t).im) =
      fun _ : ℝ => 1 := by
    funext t
    field_simp [hz t]
    exact Complex.I_im
  rw [e]
  simp

/-- The normalized endpoints coincide: `phaseFactor (2π) = phaseFactor 0`
    without any principal-argument difference. -/
example : phaseFactor (2 * Real.pi) = phaseFactor 0 := by
  rw [phaseFactor_zero, phaseFactor]
  rw [show (Complex.I * (↑(2 * Real.pi) : ℂ)) =
      2 * ↑Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

end CZExposure
