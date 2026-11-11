import RequestProject.AppendixE.Completeness

/-!
# Main completeness audit

Axiom audit of the main completeness module. Groups:
* (A) unconditional bounds/algebra — standard axioms only;
* (B) checked conditional physical results — standard axioms only,
  with `EuclideanDirectedArcSuperposition` as the sole generic input (no
  `External`, no `sorryAx`, no realization admission);
* (C) conditional polynomial certificates and convergence — standard axioms
  only, with superposition explicit. The matrix Positivstellensatz and
  C¹ approximation are proved. The final dependency check fails if any
  nonstandard axiom (including sorryAx) enters these theorems.
-/

noncomputable section

namespace CZExposure

/-! ## (A) Unconditional bounds and algebra -/

#check @Lunsplit_nonneg
#print axioms Lunsplit_nonneg
#check @Lunsplit_mono
#print axioms Lunsplit_mono
#check @Lunsplit_le_Cstar
#print axioms Lunsplit_le_Cstar
#check @Lunsplit_le_Lsplit
#print axioms Lunsplit_le_Lsplit
#check @Lsplit_mono
#print axioms Lsplit_mono
#check @Lsplit_le_Cstar
#print axioms Lsplit_le_Cstar
#check @stationary_hierarchy_bounds
#print axioms stationary_hierarchy_bounds
#check @split_hierarchy_bounds
#print axioms split_hierarchy_bounds
#check @vf_neg
#print axioms vf_neg
#check @cost_eq_zero_of_mem_Fface
#print axioms cost_eq_zero_of_mem_Fface
#check @sos_factors_vanish_on_face
#print axioms sos_factors_vanish_on_face

/-! ## (B) Checked conditional physical results
(superposition explicit; no `External`, no `sorryAx`) -/

#check @Cstar_le_pRelaxed
#print axioms Cstar_le_pRelaxed
#check @pRelaxed_eq_Cstar
#print axioms pRelaxed_eq_Cstar
#check @smooth_subsolution
#print axioms smooth_subsolution

/-! ## (C) Conditional completeness (two explicit generic inputs) -/

#print ControlGeometry.CompactRegularLevelBallBox
#print EuclideanDirectedArcSuperposition
#print PolynomialGeometry.BoxC1PolynomialApproximation
#print PolynomialGeometry.MatrixPositivstellensatz

#check @polynomial_certificates
#print axioms polynomial_certificates
#check @stationary_completeness
#print axioms stationary_completeness
#check @fixed_partition_convergence
#print axioms fixed_partition_convergence

#check @BallBoxSteering.nonempty_pulse_of_ballBox
#print axioms BallBoxSteering.nonempty_pulse_of_ballBox
#check @Cstar_finite_of_ballBox
#print axioms Cstar_finite_of_ballBox
#check @polynomial_certificates_epsilon

#check @nonempty_physical_pulse
#print axioms nonempty_physical_pulse
#check @Cstar_finite_physical
#print axioms Cstar_finite_physical
#print axioms LocalSteeringConstruction.exists_repaired_faceBlock
#print axioms LocalSteeringConstruction.exists_closed_pulse

-- These contracts cannot accept a hidden extra controllability argument.
theorem physical_relaxed_equality (h : EuclideanDirectedArcSuperposition) :
    pRelaxed = Cstar := pRelaxed_eq_Cstar h

theorem physical_stationary_convergence
    (h : EuclideanDirectedArcSuperposition) :
    Filter.Tendsto Lunsplit Filter.atTop (nhds Cstar) :=
  (stationary_completeness h).2

-- Check dependencies transitively, rather than merely searching source for sorry.
run_cmd do
  for name in [``polynomial_certificates, ``stationary_completeness,
      ``fixed_partition_convergence, ``BallBoxSteering.exists_segment_along_curve,
      ``BallBoxSteering.nonempty_pulse_of_ballBox, ``Cstar_finite_of_ballBox,
      ``polynomial_certificates_epsilon, ``nonempty_physical_pulse,
      ``Cstar_finite_physical, ``physical_relaxed_equality,
      ``physical_stationary_convergence,
      ``LocalSteeringConstruction.exists_repaired_faceBlock,
      ``LocalSteeringConstruction.exists_closed_pulse] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

end CZExposure
