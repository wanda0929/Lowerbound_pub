import RequestProject.AppendixE.ControlTranslation
import RequestProject.AppendixE.CommutatorFactorization
import RequestProject.AppendixE.BallBoxSteering
import RequestProject.AppendixE.PulseWords
import RequestProject.AppendixE.PulseExpansion
import RequestProject.AppendixE.SignedRootPulse
import RequestProject.AppendixE.EndpointMap
import RequestProject.AppendixE.LocalSteeringConstruction

/-!
Audit of the unconditional system-specific LocalSteering construction.
Expected axioms: propext, Classical.choice, Quot.sound (or a subset).
The old conditional ball-box API is imported to check compatibility.
-/

#print axioms CZExposure.ControlTranslation.translate_vf
#print axioms CZExposure.ControlTranslation.translate_mem
#print axioms CZExposure.ControlTranslation.translate_inverse_cancel
#print axioms CZExposure.ControlTranslation.relative_target_distance
#print axioms CZExposure.ControlTranslation.segment
#print axioms CZExposure.ControlTranslation.transport_endpoints
#print axioms CZExposure.PulseCommutator.word_sub_one
#print axioms CZExposure.PulseCommutator.factor
#print axioms CZExposure.PulseCommutator.coefficient_contDiff
#print axioms CZExposure.PulseCommutator.coefficient_zero

-- Physical signed pulses and their exact chronological composition.
#print axioms CZExposure.ShortPulse.orbit_deriv
#print axioms CZExposure.ShortPulse.orbit_mem
#print axioms CZExposure.ShortPulse.orbit_contDiff
#print axioms CZExposure.ShortPulse.positive
#print axioms CZExposure.ShortPulse.signed
#print axioms CZExposure.ShortPulse.signed_duration
#print axioms CZExposure.ShortPulse.signed_terminal
#print axioms CZExposure.ShortPulse.signed_unit
#print axioms CZExposure.PulseWords.run
#print axioms CZExposure.PulseWords.run_terminal
#print axioms CZExposure.PulseWords.run_duration
#print axioms CZExposure.PulseWords.run_unit
#print axioms CZExposure.PulseWords.endpoint_inv
#print axioms CZExposure.PulseWords.run_round_trip
#print axioms CZExposure.PulseWords.endpoint_zero
#print axioms CZExposure.PulseWords.commutator_endpoint
#print axioms CZExposure.PulseWords.six_lengths
#print axioms CZExposure.PulseWords.six_duration

-- Freeze the noncommuting chronological order, not merely the length.
example : CZExposure.PulseWords.W2 =
    [(false, false), (true, false), (false, true), (true, true)] := by decide

-- Exact bracket leading terms and analytic remainders of physical endpoints.
#print axioms CZExposure.PulseExpansion.op_apply
#print axioms CZExposure.PulseExpansion.op_analytic
#print axioms CZExposure.PulseExpansion.expanded_commutator
#print axioms CZExposure.PulseExpansion.expanded_W2
#print axioms CZExposure.PulseExpansion.expanded_W3X
#print axioms CZExposure.PulseExpansion.expanded_W3Y
#print axioms CZExposure.PulseExpansion.expanded_W4
#print axioms CZExposure.PulseExpansion.leading_field
#print axioms CZExposure.PulseExpansion.remainder
#print axioms CZExposure.PulseExpansion.six_endpoint_expansion
#print axioms CZExposure.PulseExpansion.six_physical_expansion

-- Nonzero, unequal sector coefficients catch bracket sign/scaling errors.
open CZExposure CZExposure.ControlLie CZExposure.PulseExpansion in
example : leading 2 x0 = ![0, -1/2, 0, 0, 0, -1, 0, 0] := by
  rw [leading_field]
  change bracket2 x0 = _
  rw [bracket2_eq_act]
  funext i
  fin_cases i <;> simp [act, x0]

open CZExposure CZExposure.ControlLie CZExposure.PulseExpansion in
example : leading 5 x0 = ![0, -1/2, 0, 0, 0, -2, 0, 0] := by
  rw [leading_field]
  change bracket4 x0 = _
  rw [bracket4_eq_act]
  funext i
  fin_cases i <;> simp [act, x0]

-- Both value and derivative glue at zero, including even bracket orders.
#print axioms CZExposure.RootRegularity.weighted_zero_deriv
#print axioms CZExposure.RootRegularity.weighted_hasDeriv
#print axioms CZExposure.RootRegularity.weightedDeriv_continuous
#print axioms CZExposure.RootRegularity.glued_weighted_contDiff
#print axioms CZExposure.SignedRootPulse.six_contDiff
#print axioms CZExposure.SignedRootPulse.six_deriv_zero
#print axioms CZExposure.SignedRootPulse.six_state_deriv_zero
#print axioms CZExposure.SignedRootPulse.physical_terminal
#print axioms CZExposure.SignedRootPulse.physical_duration
#print axioms CZExposure.SignedRootPulse.physical_unit
#print axioms CZExposure.SignedRootPulse.six_zero

open CZExposure.PulseWords CZExposure.PulseExpansion CZExposure.SignedRootPulse in
example : curve W4 4 (-1) = op (inv W4) 1 := by
  simp [curve, CZExposure.RootRegularity.root]

open CZExposure.PulseWords CZExposure.PulseExpansion CZExposure.SignedRootPulse in
example : curve W4 4 1 = op W4 1 := by
  simp [curve, CZExposure.RootRegularity.root]

-- A genuine inverse for the six-parameter physical endpoint map.
#print axioms CZExposure.EndpointMap.chart_bracket
#print axioms CZExposure.EndpointMap.state_deriv
#print axioms CZExposure.EndpointMap.coordinates_strictDeriv
#print axioms CZExposure.EndpointMap.parameters_right_inverse
#print axioms CZExposure.EndpointMap.parameters_left_inverse
#print axioms CZExposure.EndpointMap.parameters_deriv
#print axioms CZExposure.EndpointMap.parameters_bound
#print axioms CZExposure.EndpointMap.state_mem
#print axioms CZExposure.EndpointMap.chart_injective
#print axioms CZExposure.EndpointMap.exact_endpoint

-- The derivative assertion is unconditional, with the actual six words.
open CZExposure.ControlLie CZExposure.EndpointMap in
example : HasFDerivAt coordinates (ContinuousLinearMap.id ℝ Params) 0 :=
  coordinates_deriv

-- The inverse reaches the full eight-coordinate state, not only its projection.
open CZExposure CZExposure.EndpointMap in
example : ∀ᶠ y in nhds x0, y ∈ Xset → endpoint (parameters (chart y)) = y :=
  exact_endpoint

#print axioms CZExposure.LocalSteeringConstruction.trajectory
#print axioms CZExposure.LocalSteeringConstruction.trajectory_duration
#print axioms CZExposure.LocalSteeringConstruction.trajectory_unit
#print axioms CZExposure.LocalSteeringConstruction.root_le_quarter
#print axioms CZExposure.LocalSteeringConstruction.trajectory_bound
#print axioms CZExposure.LocalSteeringConstruction.origin_steering
#print axioms CZExposure.LocalSteeringConstruction.uniform_steering
#print axioms CZExposure.LocalSteeringConstruction.physicalLocalSteering

-- No generic ball-box or LocalSteering parameter remains.
open CZExposure CZExposure.LocalSteeringConstruction in
example : Nonempty LocalSteering := ⟨physicalLocalSteering⟩

-- Zero distance is included; there is no fixed-duration preparation pulse.
open CZExposure CZExposure.LocalSteeringConstruction in
example (x : State) (hx : x ∈ Xset) : ∃ P : PhysicalSegment,
    P.path 0 = x ∧ P.path P.duration = x ∧ P.duration = 0 := by
  obtain ⟨P, h0, hT, htime⟩ := physicalLocalSteering.connect x hx x hx
    (by simpa using physicalLocalSteering.radius_pos.le)
  refine ⟨P, h0, hT, le_antisymm ?_ P.duration_nonneg⟩
  simpa using htime
