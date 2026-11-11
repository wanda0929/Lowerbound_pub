import RequestProject.AppendixE.QuotientNormalForm

noncomputable section
namespace CZExposure.QuotientNormalForm
open MvPolynomial

#print axioms normalTerm_congr
#print axioms term_degree
#print axioms normalTerm_degree
#print axioms term_degreeOf
#print axioms normalTerm_normal
#print axioms term_eq_monomial
#print axioms normalize_congr
#print axioms normalize_degree
#print axioms normalize_normal
#print axioms exists_normal_expansion
#print axioms toMixed_degree
#print axioms eval_toMixed
#print axioms eval_relations_zero
#print axioms eval_normalize
#print axioms factorExpansion_degree
#print axioms factorExpansion_normal
#print axioms eval_factorExpansion
#print axioms evaluate_mixedRestriction
#print axioms stationary_expansion_restriction_zero
#check @exists_normal_expansion
#check @eval_factorExpansion
#check @stationary_expansion_restriction_zero

run_cmd do
  for name in [``normalTerm_congr, ``term_degree, ``normalTerm_degree, ``term_degreeOf,
      ``normalTerm_normal, ``term_eq_monomial, ``normalize_congr, ``normalize_degree,
      ``normalize_normal, ``exists_normal_expansion, ``toMixed_degree, ``eval_toMixed,
      ``eval_relations_zero, ``eval_normalize, ``factorExpansion_degree,
      ``factorExpansion_normal, ``eval_factorExpansion, ``evaluate_mixedRestriction,
      ``stationary_expansion_restriction_zero] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- The polynomial-level normalizer uses the term algorithm, including c=0.
example (a : Fin 11 →₀ ℕ) (c : ℂ) :
    normalize (monomial a c) = normalTerm a c := by
  by_cases hc : c = 0
  · simp [hc, normalize, normalTerm, term]
  · simp [normalize, support_monomial, hc]

example : factorExpansion 0 = 0 := by simp [factorExpansion, normalize]

-- Repeated ground pairs expand with the correct binomial coefficient and sign.
example : normalTerm ![0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0] 1 =
    1 - 2 * X 5 * X 6 + X 5^2 * X 6^2 := by
  simp only [normalTerm, term, Fin.prod_univ_succ, Fin.prod_univ_zero]
  dsimp [trimmed]
  norm_num
  ring

-- Unequal powers in all three eliminated pairs; retain ξ, the surviving
-- orientations, excited powers, and a genuinely complex coefficient.
example : normalTerm ![2, 3, 1, 1, 3, 0, 2, 2, 1, 1, 0] (2*Complex.I) =
    C (2*Complex.I) * X 0^2 * X 1^2 * X 4^2 * X 6^2 * X 7 * X 9 *
      (1 - X 5 * X 6) * (1 - X 9 * X 10) := by
  simp only [normalTerm, term, Fin.prod_univ_succ, Fin.prod_univ_zero]
  dsimp [trimmed]
  norm_num
  ring_nf
  simp

-- Unit-control pair removal can strictly lower degree; it must not become
-- another (1-r̄r) correction, as the ground-state pairs do.
example : normalTerm ![0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0] 1 = 1 := by
  simp only [normalTerm, term, Fin.prod_univ_succ, Fin.prod_univ_zero]
  dsimp [trimmed]
  norm_num

-- Physical values: unequal sectors, imaginary amplitudes/control, and ξ<0.
example : eval (mixedPoint (-2) (mkState 0 Complex.I 1 0) Complex.I)
    (factorExpansion (3 * xs 3 + 7 * ub + 2 * X Var.xi)) = 6 := by
  rw [eval_factorExpansion _ _ (by norm_num [Xset]) (by simp)]
  norm_num [pt, mkState]
  dsimp
  norm_num

-- The actual stationary cost decomposition yields normal, degree-one
-- factors whose formal face restrictions are still zero.
example : ∃ (N : ℕ) (h : Fin N → Poly), cpoly = ∑ l, h l ^ 2 ∧
    ∀ l, (factorExpansion (h l)).totalDegree ≤ 1 ∧
      (∀ a ∈ (factorExpansion (h l)).support, Normal a) ∧
      mixedRestriction (factorExpansion (h l)) = 0 := by
  obtain ⟨N, h, hd, heq⟩ := cpoly_isSOS (d := 1) le_rfl
  refine ⟨N, h, heq, fun l => ⟨(factorExpansion_degree _).trans (hd l),
    fun _ => factorExpansion_normal _, ?_⟩⟩
  apply stationary_expansion_restriction_zero (W := 0) (h := h) _ l
  simp [lieDeriv_zero, heq]

end CZExposure.QuotientNormalForm
