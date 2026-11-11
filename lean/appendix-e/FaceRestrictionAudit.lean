import RequestProject.AppendixE.FaceRestriction

noncomputable section
namespace CZExposure.FaceRestriction
open MvPolynomial ComplexConjugate

#print axioms character_injective
#print axioms characters_independent
#print axioms eq_zero_of_evaluate
#print axioms phase_norm
#print axioms faceState_mem
#print axioms evaluate_mode
#print axioms evaluate_realMode
#print axioms evaluate_imagMode
#print axioms evaluate_coordinate
#print axioms evaluate_restriction
#print axioms restriction_zero_of_physical_vanishing
#print axioms stationary_factors_restriction_zero
#print axioms normIdeal_restriction_zero
#print axioms mem_reduced_span_of_restriction_zero
#print axioms stationary_factor_mem_reduced_span
#check @stationary_factors_restriction_zero
#check @stationary_factor_mem_reduced_span

run_cmd do
  for name in [``character_injective, ``characters_independent, ``eq_zero_of_evaluate,
      ``phase_norm, ``faceState_mem, ``evaluate_mode, ``evaluate_realMode,
      ``evaluate_imagMode, ``evaluate_coordinate, ``evaluate_restriction,
      ``restriction_zero_of_physical_vanishing, ``stationary_factors_restriction_zero,
      ``normIdeal_restriction_zero, ``mem_reduced_span_of_restriction_zero,
      ``stationary_factor_mem_reduced_span] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- A single test point cannot distinguish u and g₁, but their full characters
-- are distinct. This tests the independent phase coordinates, not total charge.
example : character (0, ![1, 0, 0]) ≠ character (0, ![0, 1, 0]) := by
  intro h
  have e := congrArg (fun k : Index => k.2 0) (character_injective h)
  norm_num at e

-- The ξ exponent must also remain distinguishable, even with equal windings.
example : character (2, ![-1, 3, 0]) ≠ character (3, ![-1, 3, 0]) := by
  intro h
  have e := congrArg Prod.fst (character_injective h)
  norm_num at e

-- Preserve cell powers and kill an excited-coordinate factor.
example : restriction (X Var.xi ^ 3 + X (.st 2) * X (.st 4)) =
    AddMonoidAlgebra.single (3, 0) 1 := by
  simp [restriction, coordinate, AddMonoidAlgebra.single_pow]

-- Conjugation has negative winding. A wrong sign in imagMode fails this test.
example : restriction (X (.st 0) - C Complex.I * X (.st 1)) = mode 1 (-1) := by
  simp only [restriction, map_sub, map_mul, aeval_X, aeval_C]
  change realMode 1 - algebraMap ℂ FaceAlgebra Complex.I * imagMode 1 = _
  rw [← Algebra.smul_def]
  simp only [realMode, imagMode, smul_smul]
  have hc : Complex.I * (1 / (2 * Complex.I)) = (1/2 : ℂ) := by field_simp
  rw [hc]
  module

-- The control-circle relation is killed, including its nonzero constant.
example : restriction (MvPolynomial.map Complex.ofRealHom (ua^2 + ub^2 - 1)) = 0 := by
  apply normIdeal_restriction_zero
  exact Ideal.subset_span (by simp)

-- Exercise the bridge with an actual stationary SOS identity, W=0.
example : ∃ (N : ℕ) (h : Fin N → Poly),
    cpoly = ∑ l, h l ^ 2 ∧
      ∀ l, restriction (MvPolynomial.map Complex.ofRealHom (h l)) = 0 := by
  obtain ⟨N, h, _, heq⟩ := cpoly_isSOS (d := 1) le_rfl
  refine ⟨N, h, heq, fun l => stationary_factors_restriction_zero (W := 0) ?_ l⟩
  simp [lieDeriv_zero, heq]

end CZExposure.FaceRestriction
