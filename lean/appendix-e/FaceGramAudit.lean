import RequestProject.AppendixE.FaceGram

noncomputable section
namespace CZExposure.FaceGram
open MvPolynomial QuotientNormalForm SymmetryGram NormalFaceBasis
open scoped Matrix ComplexOrder

#print axioms stationary_face_matrix
#check @stationary_face_matrix

run_cmd do
  for name in [``key_injective, ``restriction_excited, ``restriction_unexcited,
      ``support_excited, ``restriction_zero_iff, ``stationary_factor_support,
      ``term_degree_exact, ``mem_basis, ``basis_restriction_zero, ``face_span_iff,
      ``StationaryGram.stationary_face_submatrix, ``pad_posSemidef,
      ``pad_blocks, ``pad_value, ``stationary_face_matrix] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- A single excited monomial lies exactly at the degree boundary.
example : Finsupp.single (5 : Fin 11) 2 ∈ basis 2 ∧
    Finsupp.single (5 : Fin 11) 2 ∉ basis 1 := by
  simp [mem_basis, term_degree_exact, QuotientNormalForm.Normal, Excited,
    Finsupp.single_apply]

-- Normality is essential: the control pair and the constant have the same
-- restriction label, although their exponents are different.
example : key (fun i => if i = 1 ∨ i = 2 then 1 else 0) = key (fun _ => 0) := by
  simp [key]

-- Padding preserves arbitrary quadratic forms, not merely their diagonals.
example (s t : Finset (Fin 11 →₀ ℕ)) (hs : s ⊆ t) (a b : s → ℝ) (v : t → ℂ) :
    value (fun i j => (pad (fun i j => a i * b j + b i * a j) i j : ℂ)) v =
      value (fun i j => ((a i * b j + b i * a j : ℝ) : ℂ))
        (fun i => v ⟨i.val, hs i.property⟩) := pad_value hs _ _

private def represented (B : Matrix (basis 1) (basis 1) ℝ)
    (ξ : ℝ) (x : State) (u : ℂ) : ℂ :=
  value (fun i j => (B i j : ℂ)) (fun i =>
    rephaser (decide (Odd (i.val 1 + i.val 2))) * eval (mixedPoint ξ x u) (term i.val 1))

-- One matrix on the fixed basis must reproduce unequal physical costs and
-- the zero-cost face, including imaginary amplitudes and both control signs.
example : ∃ B : Matrix (basis 1) (basis 1) ℝ, B.PosSemidef ∧
    (∀ i j, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
    ∀ ξ : ℝ,
      represented B ξ (mkState 0 Complex.I 1 0) Complex.I = 1/2 ∧
      represented B ξ (mkState 1 0 0 Complex.I) (-Complex.I) = 1/4 ∧
      represented B ξ x0 1 = 0 := by
  obtain ⟨B, hB, hb, he⟩ := stationary_face_matrix (stationaryFeasible_zero (d := 1) le_rfl)
  refine ⟨B, hB, hb, fun ξ => ?_⟩
  have hv (x : State) (hx : x ∈ Xset) (u : ℂ) (hu : ‖u‖ = 1) :
      represented B ξ x u = (cost x : ℂ) := by
    simpa [represented, lieDeriv_zero, eval_pt_cpoly] using he ξ x hx u hu
  rw [show x0 = mkState 1 0 1 0 by rfl]
  rw [hv _ (by norm_num [Xset]) _ (by simp),
    hv _ (by norm_num [Xset]) _ (by simp), hv _ (by norm_num [Xset]) _ (by simp)]
  norm_num [cost]

end CZExposure.FaceGram
