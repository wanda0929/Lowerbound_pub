import RequestProject.AppendixE.SymmetryGram

noncomputable section
namespace CZExposure.SymmetryGram
open ComplexConjugate
open scoped Matrix ComplexOrder

#print axioms separate_posSemidef
#print axioms separate_value
#print axioms monomial_gram
#print axioms rotatePoint_physical
#print axioms rephased_monomial_reflection
#print axioms real_invariant_gram
#check @monomial_gram
#check @real_invariant_gram

run_cmd do
  for name in [``separate_posSemidef, ``chargeIndex_sub_eq_zero, ``evaluate_charge_single,
      ``phase_sub, ``phase_add, ``phase_sum, ``phase_nsmul, ``monomial_response,
      ``rotatePoint_physical, ``separate_value, ``invariant_gram, ``factor_gram_value,
      ``monomial_gram, ``rephaser_unit, ``rephaser_reflection, ``monomial_reflection,
      ``rephased_monomial_reflection, ``rephaser_degree, ``rephaseMatrix_apply,
      ``rephaseMatrix_posSemidef, ``rephaseMatrix_value, ``rephaseMatrix_blocks,
      ``realMatrix_posSemidef, ``realMatrix_value, ``reflection_gram, ``real_invariant_gram] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Both charge coordinates and conjugate signs matter. This asymmetric
-- monomial has optical charge 3 and qubit charge 0, not zero charge.
example : monomialCharge ![2, 3, 1, 1, 3, 0, 2, 2, 1, 1, 0] = (3, 0) := by
  simp only [monomialCharge, Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [variableCharge]
  norm_num

-- Retain within-charge off-diagonals; delete both directions of cross-charge
-- couplings. A diagonal-only implementation would fail this check.
example : separate ![(0,1), (0,1), (1,1)]
    (!![1, 2*Complex.I, 3; -2*Complex.I, 5, 6; 3, 6, 10] : Matrix (Fin 3) (Fin 3) ℂ) =
    !![1, 2*Complex.I, 0; -2*Complex.I, 5, 0; 0, 0, 10] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [separate]

-- Redundant columns allow genuine nonzero cross-charge entries before
-- averaging. Their cancellation is in the expression, not entrywise.
private def redundantA : Matrix (Fin 1) (Fin 3) ℂ := !![1, 2, -2]
private def redundantQ : Matrix (Fin 3) (Fin 3) ℂ := redundantAᴴ * redundantA
private def redundantCharges : Fin 3 → Charge := ![(0,0), (1,0), (1,0)]

example : redundantQ 0 1 = 2 ∧ separate redundantCharges redundantQ 0 1 = 0 := by
  norm_num [redundantQ, redundantA, redundantCharges, separate, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ]

example (z : ℂ) : value (separate redundantCharges redundantQ) ![1, z, z] = 1 := by
  apply separate_value
  intro t
  rw [redundantQ, factor_gram_value]
  simp [redundantA, redundantCharges, Fin.sum_univ_succ, phase]

example : (separate redundantCharges redundantQ).PosSemidef :=
  separate_posSemidef _ (Matrix.posSemidef_conjTranspose_mul_self redundantA)

-- Without invariance, deleting cross-charge entries does change the value.
example : value (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ) ![1, 1] = 4 ∧
    value (separate ![(0,0), (1,0)] !![1, 1; 1, 1]) ![1, 1] = 2 := by
  norm_num [value, separate, Fin.sum_univ_succ]

-- Rephasing odd columns must transform the matrix as well. The sign of
-- the real off-diagonal is sensitive to the direction of this transformation.
example : rephaseMatrix ![false, true]
    (!![1, Complex.I; -Complex.I, 1] : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rephaseMatrix_apply, rephaser]

-- Entrywise real part need not preserve an arbitrary expression. Here it
-- gives exactly the average of the values at v and conjugate(v): (0+4)/2.
example : value (!![1, Complex.I; -Complex.I, 1] : Matrix (Fin 2) (Fin 2) ℂ)
    ![1, Complex.I] = 0 ∧
    value (fun i j => (realMatrix (!![1, Complex.I; -Complex.I, 1]) i j : ℂ))
      ![1, Complex.I] = 2 := by
  norm_num [value, realMatrix, Fin.sum_univ_succ]

-- The combined construction produces a real PSD charge-block matrix even
-- with duplicate columns and nonzero discarded cross-charge entries.
example : ∃ B : Matrix (Fin 3) (Fin 3) ℝ, B.PosSemidef ∧
    (∀ i j, redundantCharges i ≠ redundantCharges j → B i j = 0) ∧
    ∀ z : ℂ, value (fun i j => (B i j : ℂ)) ![1, z, z] = 1 := by
  have hr : ∀ (z : ℂ) t, value redundantQ
      (fun i => phase (redundantCharges i) t * ![1, z, z] i) = 1 := by
    intro z t
    rw [redundantQ, factor_gram_value]
    simp [redundantA, redundantCharges, phase, Fin.sum_univ_succ]
  have hf : ∀ (z : ℂ) t, value redundantQ
      (fun i => phase (redundantCharges i) t * conj (![1, z, z] i)) = 1 := by
    intro z t
    rw [redundantQ, factor_gram_value]
    simp [redundantA, redundantCharges, phase, Fin.sum_univ_succ]
  simpa [rephaser] using real_invariant_gram redundantCharges (fun _ => false) redundantQ
    (Matrix.posSemidef_conjTranspose_mul_self redundantA) (fun z => ![1, z, z]) (fun _ => 1)
    (by simpa using hr) (by simpa using hf)

end CZExposure.SymmetryGram
