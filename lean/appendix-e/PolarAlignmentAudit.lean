import RequestProject.AppendixE.PolarAlignment
import RequestProject.AppendixE.ConcretePartitioned

open CZExposure

#print EuclideanCurrentArcData.CurrentIdentity
#check @EuclideanCurrentArcData.CurrentIdentity.isDirected
#check @EuclideanCurrentSuperposition.directed
#print axioms EuclideanCurrentArcData.CurrentIdentity.isDirected
#print axioms EuclideanCurrentSuperposition.directed

run_cmd do
  for name in [``EuclideanCurrentArcData.ae_length_eq_component_mass,
      ``EuclideanCurrentArcData.MeasurableArcs.of_continuous,
      ``EuclideanCurrentArcData.MeasurableArcs.pairing_measurable,
      ``EuclideanCurrentArcData.CurrentIdentity.of_measurableArcs,
      ``EuclideanCurrentArcData.length_integrable_and_integral,
      ``EuclideanCurrentArcData.mass_identity,
      ``EuclideanCurrentArcData.CurrentIdentity.pairing_integrable,
      ``EuclideanCurrentArcData.CurrentIdentity.isDirected,
      ``EuclideanCurrentSuperposition.directed] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- End-to-end interface: source identities, not directedness or a supplied
-- pulse, suffice for the real stationary epsilon conclusion.
theorem source_stationary_epsilon
    (hCurrent : EuclideanCurrentSuperposition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D,
      0 ≤ Cstar.toReal - (ConcreteStationary.optimum d).toReal ∧
        Cstar.toReal - (ConcreteStationary.optimum d).toReal < ε :=
  ConcreteStationary.optimum_epsilon hCurrent.directed hε

-- Partitioned upper bounds still require the original ceiling witness.
theorem source_partitioned_convergence
    (hCurrent : EuclideanCurrentSuperposition)
    (P : ExposurePartition) (U : ℝ) (hU : ∃ γ : Pulse, γ.exposure < U) :
    Filter.Tendsto (ConcretePartitioned.optimum P U) Filter.atTop (nhds Cstar) :=
  ConcretePartitioned.fixed_partition_convergence hCurrent.directed P U hU

run_cmd do
  for name in [``source_stationary_epsilon, ``source_partitioned_convergence] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
