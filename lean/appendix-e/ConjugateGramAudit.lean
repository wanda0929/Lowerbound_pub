import RequestProject.AppendixE.ConjugateGram

noncomputable section
namespace CZExposure.ConjugateGram
open MvPolynomial QuotientNormalForm SymmetryGram NormalFaceBasis
open scoped Matrix ComplexOrder

#print axioms stationary_compressed
#check @stationary_compressed

run_cmd do
  for name in [``partner_partner, ``partner_degree, ``partner_mem, ``partner_charge,
      ``partner_column, ``real_conjugate_value, ``foldPair_posSemidef, ``foldPair_value,
      ``compressedBlock_posSemidef, ``oppositeBlock_value, ``compressedBlock_value,
      ``sum_blockValue, ``keep_neg, ``neg_mem_charges, ``retained_covers,
      ``retained_unique, ``sum_pairs, ``stationary_compressed] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Selection includes the zero sector and exactly one sign on either axis.
example : Keep (0,0) ∧ Keep (1,-3) ∧ ¬Keep (-1,3) ∧ Keep (0,2) ∧ ¬Keep (0,-2) := by
  norm_num [Keep]

-- The zero block is not doubled, even when its entries are nonzero.
example {d : ℕ} (B : Matrix (basis d) (basis d) ℝ) :
    compressedBlock B 0 = block B 0 := by simp [compressedBlock]

-- Unequal complex column values and a nonzero off-diagonal expose the sign
-- error in simply adding opposite blocks after reflection rephasing.
example : let A : Matrix (Fin 2) (Fin 2) ℝ := !![2,0;0,3]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;2,4]
    let v : Fin 2 → ℂ := ![1 + Complex.I, 2 + Complex.I]
    value ((foldPair ![1,-1] A B).map Complex.ofReal) v = 29 ∧
      value ((A + B).map Complex.ofReal) v = 53 := by
  norm_num [foldPair, value, Fin.sum_univ_succ, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Complex.ext_iff]

-- Conjugation keeps ξ and interchanges barred/unbarred coordinates.
example : partner (Finsupp.single (0 : Fin 11) 2 + Finsupp.single 1 3 + Finsupp.single 5 1) =
    Finsupp.single 0 2 + Finsupp.single 2 3 + Finsupp.single 6 1 := by
  ext i
  simp only [partner_apply, Finsupp.add_apply]
  fin_cases i <;> norm_num [swap, Finsupp.single_apply] <;> decide

private def represented (Q : (q : Charge) → Matrix (sector 1 q) (sector 1 q) ℝ)
    (ξ : ℝ) (x : State) (u : ℂ) : ℂ :=
  ∑ q ∈ retained 1, value ((Q q).map Complex.ofReal) (fun a => column a.val ξ x u)

-- The compressed family, not the pre-compression matrix, reproduces the
-- physical residual for all ξ with unequal sector costs and a zero face.
example : ∃ Q : (q : Charge) → Matrix (sector 1 q) (sector 1 q) ℝ,
    (∀ q, (Q q).PosSemidef) ∧ ∀ ξ : ℝ,
      represented Q ξ (mkState 0 Complex.I 1 0) Complex.I = 1/2 ∧
      represented Q ξ (mkState 1 0 0 Complex.I) (-Complex.I) = 1/4 ∧
      represented Q ξ x0 1 = 0 := by
  obtain ⟨Q, hQ, he⟩ := stationary_compressed (stationaryFeasible_zero (d := 1) le_rfl)
  refine ⟨Q, hQ, fun ξ => ?_⟩
  have hv (x : State) (hx : x ∈ Xset) (u : ℂ) (hu : ‖u‖ = 1) :
      represented Q ξ x u = (cost x : ℂ) := by
    simpa [represented, lieDeriv_zero, eval_pt_cpoly] using he ξ x hx u hu
  rw [show x0 = mkState 1 0 1 0 by rfl]
  rw [hv _ (by norm_num [Xset]) _ (by simp),
    hv _ (by norm_num [Xset]) _ (by simp), hv _ (by norm_num [Xset]) _ (by simp)]
  norm_num [cost]

end CZExposure.ConjugateGram
