import RequestProject.AppendixE.ExposureRecordSelection

/-!
# Axiom audit: cutoff excursions and finite excursion selection

Expected: analytic/construction results use only
`[propext, Classical.choice, Quot.sound]`; the record-level wrapper also
depends on the single named `External.euclideanDirectedArcSuperposition`.
-/

open CZExposure

#check @IsCutoffExcursion
#check @retainedExcursionSet
#check @IsCutoffExcursion.cost_ge
#check @IsCutoffExcursion.eq_of_overlap
#check @IsCutoffExcursion.right_le_left_of_left_lt
#check @exists_cutoff_excursion_through
#check @retainedExcursionSet_pairwiseDisjoint
#check @exists_retainedExcursion_containing
#check @cost_lt_threshold_outside_retained
#check @retainedExcursionSet_finite
#check @FiniteExcursionSelection
#check @FiniteExcursionSelection.mk
#check @FiniteExcursionSelection.ofTrajectory
#check @FiniteExcursionSelection.cost_lt_outside
#check @FiniteExcursionSelection.right_le_left_of_start_lt
#check @FiniteExcursionSelection.exposure_le
#check @FiniteExcursionSelection.duration_le
#check @FiniteExcursionSelection.count_bound
#check @FiniteExcursionSelection.physical_endpoints_cost
#check @euclideanExposureCost_y0
#check @euclideanExposureCost_yPi
#check @exists_finite_excursion_selection
#check @exists_finite_excursion_selections_of_record_of_superposition
#check @exists_finite_excursion_selections_of_record

#print axioms IsCutoffExcursion.cost_ge
#print axioms IsCutoffExcursion.eq_of_overlap
#print axioms IsCutoffExcursion.right_le_left_of_left_lt
#print axioms exists_cutoff_excursion_through
#print axioms retainedExcursionSet_pairwiseDisjoint
#print axioms exists_retainedExcursion_containing
#print axioms cost_lt_threshold_outside_retained
#print axioms retainedExcursionSet_finite
#print axioms FiniteExcursionSelection.ofTrajectory
#print axioms FiniteExcursionSelection.cost_lt_outside
#print axioms FiniteExcursionSelection.right_le_left_of_start_lt
#print axioms FiniteExcursionSelection.exposure_le
#print axioms FiniteExcursionSelection.duration_le
#print axioms FiniteExcursionSelection.count_bound
#print axioms FiniteExcursionSelection.physical_endpoints_cost
#print axioms euclideanExposureCost_y0
#print axioms euclideanExposureCost_yPi
#print axioms exists_finite_excursion_selection
#print axioms exists_finite_excursion_selections_of_record_of_superposition
#print axioms exists_finite_excursion_selections_of_record
