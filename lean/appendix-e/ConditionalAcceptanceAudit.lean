import RequestProject.AppendixE.ConditionalAcceptance

open CZExposure

-- Inspect the entire external proposition and its component contracts.
#print EuclideanNormalCurrentData
#print EuclideanCurrentArcData
#print LocalizedMeasureDecomposition
#print EuclideanArc
#print EuclideanCurrentArcData.CurrentIdentity
#print EuclideanCurrentSuperposition
#print Pulse
#print Cstar
#print ExposurePartition

-- Fixed theorem types in ConditionalAcceptance prevent hidden extra inputs.
#check @ConditionalAcceptance.relaxed_equality
#check @ConditionalAcceptance.smooth_bounds
#check @ConditionalAcceptance.certificates
#check @ConditionalAcceptance.stationary
#check @ConditionalAcceptance.partitioned
#check @ConditionalAcceptance.concrete_stationary
#check @ConditionalAcceptance.concrete_partitioned

-- Transitive dependency audit: imported legacy axioms may exist in the
-- environment, but none may occur in any accepted proof's dependencies.
run_cmd do
  for name in [``ConditionalAcceptance.relaxed_equality,
      ``ConditionalAcceptance.smooth_bounds, ``ConditionalAcceptance.certificates,
      ``ConditionalAcceptance.stationary, ``ConditionalAcceptance.partitioned,
      ``ConditionalAcceptance.concrete_stationary,
      ``ConditionalAcceptance.concrete_partitioned,
      ``EuclideanCurrentSuperposition.directed,
      ``EuclideanCurrentArcData.CurrentIdentity.isDirected,
      ``Cstar_finite_physical, ``nonempty_physical_pulse,
      ``stationary_hierarchy_bounds, ``split_hierarchy_bounds,
      ``ConcretePartitioned.potentialOptimum_eq,
      ``ConcretePartitioned.stationary_le_optimum,
      ``ConcretePartitioned.optimum_mono,
      ``ConcretePartitioned.optimum_le_Cstar,
      ``sos_factors_vanish_on_face] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"PASS {name}: {axioms}"
