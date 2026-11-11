import RequestProject.AppendixE.ExposureExcursions

/-!
# Axiom audit: cost growth and excursion accounting

#check / #print axioms for the public theorems of `CostGrowth.lean` and
`ExposureExcursions.lean`.  Expected: only `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no external axioms.
-/

open CZExposure

#check @costThreeHalves
#check @euclideanSquaredCostCLM
#check @continuous_costThreeHalves
#check @monotoneOn_costThreeHalves
#check @strictMonoOn_costThreeHalves
#check @abs_fderiv_cost_vf_le_sqrt
#check @euclideanSquaredCostCLM_nonneg
#check @abs_euclideanSquaredCostCLM_Bfield_le
#check @lipschitzOn_costThreeHalves_exposure
#check @cost_excursion_duration_lower_bound
#check @sum_disjoint_interval_lengths_le
#check @cost_excursion_count_bound
#check @cost_excursion_family_finite
#check @cost_excursion_count_bound_half_cutoff
#check @sum_retained_physicalExposure_le

#print axioms continuous_costThreeHalves
#print axioms monotoneOn_costThreeHalves
#print axioms strictMonoOn_costThreeHalves
#print axioms abs_fderiv_cost_vf_le_sqrt
#print axioms euclideanSquaredCostCLM_nonneg
#print axioms abs_euclideanSquaredCostCLM_Bfield_le
#print axioms lipschitzOn_costThreeHalves_exposure
#print axioms cost_excursion_duration_lower_bound
#print axioms sum_disjoint_interval_lengths_le
#print axioms cost_excursion_count_bound
#print axioms cost_excursion_family_finite
#print axioms cost_excursion_count_bound_half_cutoff
#print axioms sum_retained_physicalExposure_le
