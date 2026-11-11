import RequestProject.AppendixE.QuotientSymmetry

noncomputable section
namespace CZExposure.QuotientSymmetry
open MvPolynomial QuotientNormalForm QuotientCertificate SymmetryGram
open scoped Matrix ComplexOrder

#print axioms stationary_projected_identity
#check @stationary_projected_identity

run_cmd do
  for name in [``chargePart_relations, ``chargePart_congr, ``term_homogeneous,
      ``conjugate_term, ``chargePart_gram, ``reflect_relations,
      ``reflectionAverage_relations, ``reflectionAverage_congr,
      ``conjugate_involutive, ``reflect_conjugate, ``reflect_gram,
      ``reflectionAverage_gram, ``separated_congr, ``real_averaged_congr,
      ``stationary_projected_identity] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Projection kills a charged term but retains a balanced pair. Hence it
-- must not be treated as a ring homomorphism.
example : chargePart 0 (X 1 : MixedPoly) = 0 ∧
    chargePart 0 (X 2 : MixedPoly) = 0 ∧
    chargePart 0 (X 1 * X 2 : MixedPoly) = X 1 * X 2 := by
  have h1 := isWeightedHomogeneous_X (R := ℂ) variableCharge (1 : Fin 11)
  have h2 := isWeightedHomogeneous_X (R := ℂ) variableCharge (2 : Fin 11)
  have h0 : IsWeightedHomogeneous variableCharge (X 1 * X 2 : MixedPoly) 0 := by
    convert h1.mul h2 using 1
  exact ⟨h1.weightedHomogeneousComponent_ne 0 (by decide),
    h2.weightedHomogeneousComponent_ne 0 (by decide), h0.weightedHomogeneousComponent_same⟩

-- Projection and reflection preserve nonconstant multiples of constraints.
example (q : Charge) : chargePart q ((X 1 + X 3 ^ 2) * (X 1 * X 2 - 1)) ∈ relations := by
  apply chargePart_relations
  exact relations.mul_mem_left _ (Ideal.subset_span (by simp))

example : reflectionAverage ((X 1 + X 3 ^ 2) * (X 1 * X 2 - 1)) ∈ relations := by
  apply reflectionAverage_relations
  exact relations.mul_mem_left _ (Ideal.subset_span (by simp))

-- Reflection changes the control sign but does not conjugate coefficients.
example : reflect (C Complex.I * X 1 + X 3 : MixedPoly) = -C Complex.I * X 2 + X 4 := by
  simp [map_add, map_mul, reflectCoordinate, ConjugateGram.swap]

-- Rephasing an odd-control column is necessary for the real-part theorem.
example : reflect (C Complex.I * X 1 * X 5 : MixedPoly) =
    conjugate (C Complex.I * X 1 * X 5) := by
  simp only [map_mul, reflect_C, reflect_X, conjugate_C, conjugate_X]
  dsimp [reflectCoordinate, ConjugateGram.swap]
  simp

-- A Hermitian off-diagonal imaginary coefficient disappears under the
-- formal reflection average, without evaluating on physical states.
example : let Q : Matrix (Fin 2) (Fin 2) ℂ := !![2,Complex.I;-Complex.I,3]
    let z : Fin 2 → MixedPoly := ![X 3, X 7]
    reflectionAverage (gram Q z) = gram (!![2,0;0,3]) z := by
  dsimp only
  have hQ : (!![2,Complex.I;-Complex.I,3] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  rw [reflectionAverage_gram _ hQ _ (by
    intro i; fin_cases i <;> simp [reflectCoordinate, ConjugateGram.swap])]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realMatrix]

end CZExposure.QuotientSymmetry
