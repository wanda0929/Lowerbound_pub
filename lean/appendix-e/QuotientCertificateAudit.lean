import RequestProject.AppendixE.QuotientCertificate

noncomputable section
namespace CZExposure.QuotientCertificate
open MvPolynomial QuotientNormalForm ComplexConjugate
open scoped Matrix ComplexOrder

#print axioms stationary_exact_gram
#check @stationary_exact_gram

run_cmd do
  for name in [``real_imag_square, ``embed_state_norm₁, ``embed_state_norm₂,
      ``embed_control_norm, ``embed_normIdeal, ``normalization_ideal_eq,
      ``factor_congr, ``normalized_squares, ``conjugate_coordinate,
      ``conjugate_embed, ``conjugate_relations, ``factor_conjugate_congr,
      ``gram_factors, ``factor_expansion_polynomial, ``normalized_gram,
      ``stationary_exact_gram, ``eval_conjugate, ``eval_gram] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- The ideal has exactly the original generators after coordinate conversion;
-- arbitrary polynomial multipliers are allowed, not just constant ones.
example : embed ((X Var.xi + 3 * ub) * (ua ^ 2 + ub ^ 2 - 1)) ∈ relations := by
  apply embed_normIdeal
  exact normIdeal.mul_mem_left _ (Ideal.subset_span (by simp))

-- Ideal membership is not literal polynomial equality. This generator is
-- nonzero away from the unit-control constraint.
example : eval (fun _ : Fin 11 => (2 : ℂ)) (embed (ua ^ 2 + ub ^ 2 - 1)) = 3 := by
  rw [embed_control_norm]
  norm_num

-- Conjugate the coefficient AND swap barred/unbarred coordinates, while
-- fixing the real cell coordinate.
example : conjugate (C (2 + 3 * Complex.I) * X 0 ^ 2 * X 1 * X 6) =
    C (2 - 3 * Complex.I) * X 0 ^ 2 * X 2 * X 5 := by
  simp only [map_mul, map_pow, conjugate_C, conjugate_X]
  dsimp [ConjugateGram.swap]
  simp only [map_add, map_mul, map_ofNat, Complex.conj_I, map_sub, map_neg]
  ring

-- Complex coefficients produce off-diagonal terms with opposite signs.
-- This is a polynomial identity with independent barred variables, not a
-- test restricted to physical/conjugate-valued assignments.
example : let A : Matrix (Fin 1) (Fin 2) ℂ := ![![1, Complex.I]]
    gram (Aᴴ * A) ![X 1, X 5] =
      X 2 * X 1 + C Complex.I * X 2 * X 5 - C Complex.I * X 6 * X 1 + X 6 * X 5 := by
  dsimp only
  rw [gram_factors]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp
  simp [map_mul, map_add, ConjugateGram.swap]
  ring_nf
  simp [← map_pow, Complex.I_sq]
  ring

example (z : Fin 0 → MixedPoly) (Q : Matrix (Fin 0) (Fin 0) ℂ) : gram Q z = 0 := by
  simp [gram]

-- Apply the exact identity to a known feasible certificate, retaining its
-- degree bound and positivity rather than assuming an arbitrary Gram input.
example : ∃ (s : Finset (Fin 11 →₀ ℕ)) (Q : Matrix s s ℂ),
    s ⊆ NormalFaceBasis.basis 1 ∧ Q.PosSemidef ∧
      embed cpoly - gram Q (fun i => term i.val 1) ∈ relations := by
  simpa [lieDeriv_zero] using stationary_exact_gram (stationaryFeasible_zero (d := 1) le_rfl)

end CZExposure.QuotientCertificate
