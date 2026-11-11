import RequestProject.AppendixE.StationaryGram

noncomputable section
namespace CZExposure.StationaryGram
open MvPolynomial QuotientNormalForm SymmetryGram
open scoped Matrix ComplexOrder

#print axioms residual_rotate
#print axioms residual_reflection
#print axioms column_properties
#print axioms expansion_sum
#print axioms factor_matrix_represents
#print axioms columnValues_rotate
#print axioms columnValues_reflection
#print axioms stationary_matrix
#check @stationary_matrix

run_cmd do
  for name in [``residual_rotate, ``residual_reflection, ``column_properties,
      ``expansion_sum, ``factor_matrix_represents, ``columnValues_rotate,
      ``columnValues_reflection, ``stationary_matrix] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- No nonempty-factor assumption is hidden in the support construction.
example (h : Fin 0 → Poly) : columns h = ∅ := by simp [columns]

-- Different supports must be padded with zero coefficients. These linear
-- factors also test imaginary control/state coordinates and negative ξ.
example : let h : Fin 2 → Poly := ![xs 0 + 2 * ub, xs 3 - 3 * X Var.xi]
    (∑ i : columns h, coefficients h 0 i * eval (mixedPoint (-2)
      (mkState 0 Complex.I 1 0) Complex.I) (term i.val 1)) = 2 ∧
    (∑ i : columns h, coefficients h 1 i * eval (mixedPoint (-2)
      (mkState 0 Complex.I 1 0) Complex.I) (term i.val 1)) = 7 := by
  dsimp only
  rw [expansion_sum, expansion_sum]
  have hx : mkState 0 Complex.I 1 0 ∈ Xset := by norm_num [Xset]
  simp only [eval_factorExpansion _ (-2) hx (show ‖Complex.I‖ = 1 by simp)]
  norm_num [pt, mkState]
  dsimp
  norm_num

private def represented (s : Finset (Fin 11 →₀ ℕ)) (B : Matrix s s ℝ)
    (ξ : ℝ) (x : State) (u : ℂ) : ℂ :=
  value (fun i j => (B i j : ℂ)) (fun i =>
    rephaser (decide (Odd (i.val 1 + i.val 2))) * eval (mixedPoint ξ x u) (term i.val 1))

-- Apply the final theorem to an actual certificate, not an assumed matrix
-- representation. The same matrix must give the unequal sector costs 1/2
-- and 1/4, and zero on the initial face, for every cell coordinate.
example : ∃ (s : Finset (Fin 11 →₀ ℕ)) (B : Matrix s s ℝ),
    (∀ i : s, Normal i.val ∧ (term i.val 1).totalDegree ≤ 1) ∧ B.PosSemidef ∧
    (∀ i j : s, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
    ∀ ξ : ℝ,
      represented s B ξ (mkState 0 Complex.I 1 0) Complex.I = 1/2 ∧
      represented s B ξ (mkState 1 0 0 Complex.I) (-Complex.I) = 1/4 ∧
      represented s B ξ x0 1 = 0 := by
  obtain ⟨s, B, hd, hB, hb, he⟩ := stationary_matrix (stationaryFeasible_zero (d := 1) le_rfl)
  refine ⟨s, B, hd, hB, hb, fun ξ => ?_⟩
  have hv (x : State) (hx : x ∈ Xset) (u : ℂ) (hu : ‖u‖ = 1) :
      represented s B ξ x u = (cost x : ℂ) := by
    simpa [represented, lieDeriv_zero, eval_pt_cpoly] using he ξ x hx u hu
  rw [show x0 = mkState 1 0 1 0 by rfl]
  rw [hv _ (by norm_num [Xset]) _ (by simp),
    hv _ (by norm_num [Xset]) _ (by simp), hv _ (by norm_num [Xset]) _ (by simp)]
  norm_num [cost]

end CZExposure.StationaryGram
