/-
Copyright (c) 2026 LowerBoundCZ authors.

Kernel audit entrypoint for the Appendix E formalization.

Compile from the `lean/` directory with:

    lake env lean AppendixEAudit.lean

It intentionally imports ONLY `LowerBoundCZ.AppendixE` (which does not pull in
the certificate-axiom modules `Upper`/`Results`/`Reductions`), then prints the
axiom dependencies of the principal theorem dependency roots. Expected output:
only `propext`, `Classical.choice`, and `Quot.sound` — no `sorryAx` and none
of the project's certificate axioms.
-/
import LowerBoundCZ.AppendixE

open LowerBoundCZ.AppendixE

-- Model.lean: conditional order-theoretic equivalence and patching lemmas.
#print axioms disk_infimum_eq_of_compression
#print axioms physicalInfimum_le_of_patching
#print axioms zero_gap_of_patching

-- Hierarchy.lean: order-theoretic completeness final step.
#print axioms ValueHierarchy.tendsto_of_finite_certificates
#print axioms stationary_and_split_complete_of_common_certificates
#print axioms physicalInfimum_stationary_and_split_complete_of_common_certificates
#print axioms stationary_interface_zero

-- Algebra.lean: augmentation, Schur scalar step, Gram contraction.
#print axioms augmentation_mulVec_self
#print axioms quadratic_augmentation
#print axioms quadratic_augmentation_nonneg
#print axioms quadratic_add_smul_augmentation
#print axioms schur_quadratic_pos
#print axioms gram_contraction
#print axioms gram_contraction_poly
#print axioms gram_contraction_eval_nonneg
#print axioms gram_contraction_eval_zero_on_face

-- Patching.lean: exponent identity, error limit, conditional bound.
#print axioms coupled_threshold_power
#print axioms patching_error_tendsto_zero
#print axioms threshold_eventually_valid
#print axioms physicalInfimum_le_of_threshold_family
