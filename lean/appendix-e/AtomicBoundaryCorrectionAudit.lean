import RequestProject.AppendixE.AtomicBoundaryCorrection

open CZExposure CZExposure.AtomicBoundaryCorrection
open MeasureTheory
open scoped BigOperators

#check @correction_boundary
#check @correctionAction_indicator
#check @correction_variation_le
#check @correction_mass_le
#check @correction_compact_support
#check @correction_mass_le_of_displacement
#check @correction_mass_tendsto_zero

-- Coincident endpoints require no fictitious positive-length arc.
example (x : ExposureEuclidean) : AtomicBoundaryCorrection.segment x x = 0 := by
  simp [AtomicBoundaryCorrection.segment]

-- Asymmetric signed weights and reversed orientation distinguish the
-- oriented vector current from its unsigned mass upper bound.
example (x y : ExposureEuclidean) :
    correction (fun i : Fin 2 => if i = 0 then 2 else -3)
      (fun i => if i = 0 then x else y)
      (fun i => if i = 0 then y else x) Set.univ = (5 : ℝ) • (y - x) := by
  simp [correction_apply, segment_univ, Fin.sum_univ_two]
  module

run_cmd do
  for name in [``segment_univ, ``segment_mass, ``segment_compact_support,
      ``segmentAction_indicator, ``segment_boundary,
      ``variation_smul_le, ``variation_sum_le,
      ``correction_apply, ``correctionAction_indicator, ``correction_boundary,
      ``correction_variation_le, ``correction_mass_le,
      ``correction_compact_support, ``correction_finite,
      ``correction_mass_le_of_displacement, ``correction_apply_le,
      ``correction_mass_tendsto_zero] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"PASS {name}: {axioms}"
