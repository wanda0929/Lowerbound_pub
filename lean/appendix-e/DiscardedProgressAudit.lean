import RequestProject.AppendixE.DiscardedProgress

/-!
# Axiom audit: discarded-gap progress and angular-rate bounds

Expected: all results use only `[propext, Classical.choice, Quot.sound]`.
No geometry axiom is imported by this local analytic layer.
-/

open CZExposure

#check @euclideanProgressCLM
#check @exposureProgressPath
#check @exposureProgressVelocity
#check @euclideanAngularRate
#check @euclideanProgressCLM_Jmap
#check @euclideanProgressCLM_fderiv_Jmap
#check @norm_euclideanProgress_Bfield_le
#check @euclideanExposureCost_le_one
#check @norm_zObs_ge_one_sub_six_cost
#check @norm_euclideanProgress_ge_half
#check @abs_euclideanAngularRate_le
#check @measurable_exposureProgressVelocity
#check @measurable_exposureAngularRate
#check @integrableOn_exposureProgressVelocity
#check @ae_hasDerivAt_exposureProgressPath
#check @integral_exposureProgressVelocity
#check @low_cost_progress_increment_le
#check @sum_low_cost_progress_increments_le
#check @FiniteExcursionSelection.discardedTimes
#check @FiniteExcursionSelection.mem_discardedTimes_iff
#check @FiniteExcursionSelection.isCompact_discardedTimes
#check @FiniteExcursionSelection.cost_lt_on_discarded
#check @FiniteExcursionSelection.volume_real_discardedTimes_le
#check @FiniteExcursionSelection.discardedProgressSpeed
#check @FiniteExcursionSelection.discardedAngularIntegral
#check @FiniteExcursionSelection.discarded_progress_bounds

#print axioms euclideanProgressCLM_Jmap
#print axioms euclideanProgressCLM_fderiv_Jmap
#print axioms norm_euclideanProgress_Bfield_le
#print axioms euclideanExposureCost_le_one
#print axioms norm_zObs_ge_one_sub_six_cost
#print axioms norm_euclideanProgress_ge_half
#print axioms abs_euclideanAngularRate_le
#print axioms measurable_exposureProgressVelocity
#print axioms measurable_exposureAngularRate
#print axioms integrableOn_exposureProgressVelocity
#print axioms ae_hasDerivAt_exposureProgressPath
#print axioms integral_exposureProgressVelocity
#print axioms low_cost_progress_increment_le
#print axioms sum_low_cost_progress_increments_le
#print axioms FiniteExcursionSelection.mem_discardedTimes_iff
#print axioms FiniteExcursionSelection.isCompact_discardedTimes
#print axioms FiniteExcursionSelection.cost_lt_on_discarded
#print axioms FiniteExcursionSelection.volume_real_discardedTimes_le
#print axioms FiniteExcursionSelection.discarded_progress_bounds
