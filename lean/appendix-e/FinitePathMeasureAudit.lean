import RequestProject.AppendixE.FinitePathMeasure

open CZExposure.FiniteRouting

#check @Flow.integral_pathMeasure
#check @Flow.initial_integral
#check @Flow.terminal_integral
#check @Flow.duration_integral
#check @Flow.pathMeasure_probability

run_cmd do
  for name in [``Flow.integrable_pathMeasure, ``Flow.pathMeasure_finite,
      ``Flow.integral_pathMeasure, ``Flow.initial_integral,
      ``Flow.terminal_integral, ``Flow.duration_integral,
      ``Flow.pathMeasure_mass, ``Flow.pathMeasure_probability] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"PASS {name}: {axioms}"
