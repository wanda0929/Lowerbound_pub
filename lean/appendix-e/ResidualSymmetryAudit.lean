import RequestProject.AppendixE.ResidualSymmetry

noncomputable section
namespace CZExposure.ResidualSymmetry
open MvPolynomial QuotientNormalForm QuotientCertificate QuotientSymmetry SymmetryGram
open scoped Matrix ComplexOrder

#print axioms residual_projections
#print axioms stationary_identity
#check @mixedPoint_ext
#check @residual_chargePart
#check @residual_reflectionAverage
#check @stationary_identity
#print axioms reflect_rephased_term
#print axioms reflectionAverage_rephased_gram
#print axioms rephaseMatrix_gram
#print axioms stationary_real_identity
#check @stationary_real_identity
#print axioms pad_gram
#print axioms stationary_fixed_identity
#check @stationary_fixed_identity
#print axioms compressed_gram
#print axioms stationary_compressed_identity
#check @stationary_compressed_identity

run_cmd do
  for name in [``mixedPoint_ext, ``eval_embed, ``eval_reflect, ``residual_reflect,
      ``residual_reflectionAverage, ``eval_chargePart_of_invariant,
      ``residual_chargePart, ``residual_projections, ``stationary_identity,
      ``reflect_rephased_term, ``reflectionAverage_rephased_gram,
      ``rephaseMatrix_gram, ``stationary_real_identity,
      ``pad_gram, ``stationary_fixed_identity,
      ``compressed_gram, ``stationary_compressed_identity] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- A nonconstant W exercises the drift, not just the invariant cost term.
private def costState : StatePoly :=
  C (1/4) * (2 * (X 2 ^ 2 + X 3 ^ 2) + (X 6 ^ 2 + X 7 ^ 2))

private theorem costState_eval (x : State) : eval x costState = cost x := by
  simp [costState, cost, r1, r2, Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem costState_invariant : IsGInvariant (fun x => eval x costState) := by
  intro x θ α
  simp only [costState_eval, PolynomialSymmetry.cost_opticalGauge,
    PolynomialSymmetry.cost_qubitGauge, PolynomialSymmetry.cost_reflection,
    and_self]

example : chargePart 0 (embed (cpoly + lieDeriv costState)) =
    embed (cpoly + lieDeriv costState) ∧
    reflectionAverage (embed (cpoly + lieDeriv costState)) =
      embed (cpoly + lieDeriv costState) :=
  ⟨residual_chargePart costState_invariant, residual_reflectionAverage costState_invariant⟩

-- The new integration theorem needs no matrix supplied by its caller.
example : ∃ Q : (q : Charge) → Matrix
    (ConjugateGram.sector 1 q) (ConjugateGram.sector 1 q) ℝ,
    (∀ q, (Q q).PosSemidef) ∧
      embed cpoly - (∑ q ∈ ConjugateGram.retained 1,
        gram ((Q q).map Complex.ofReal) (fun i =>
          C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1)) ∈ relations := by
  simpa [lieDeriv_zero] using stationary_compressed_identity
    (stationaryFeasible_zero (d := 1) le_rfl)

-- Unit-control vanishing must not be substituted for unrestricted equality.
example : eval (mixedPoint 0 (fun _ => 0) 0) (X 1 * X 2 - 1 : MixedPoly) = -1 := by
  simp [mixedPoint]

-- Reflection is complex-linear, whereas conjugation changes coefficients.
example (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) (reflect (C Complex.I * X 1)) =
      -Complex.I * starRingEnd ℂ u := by
  simp [map_mul, reflectCoordinate, ConjugateGram.swap, mixedPoint]

-- Odd total control degree despite an even unbarred-control exponent.
-- This would fail if parity counted only the unbarred control coordinate.
example : reflect (C Complex.I * (X 0 ^ 2 * X 1 ^ 2 * X 2 * X 5) : MixedPoly) =
    conjugate (C Complex.I * (X 0 ^ 2 * X 1 ^ 2 * X 2 * X 5)) := by
  simpa [term, rephaser, Fin.prod_univ_succ, mul_assoc,
    show Odd (3 : ℕ) from ⟨1, rfl⟩] using
    reflect_rephased_term ![2, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0]

-- Two odd control exponents have even total degree: no factor i.
example : reflect (X 1 * X 2 * X 9 ^ 3 : MixedPoly) =
    conjugate (X 1 * X 2 * X 9 ^ 3) := by
  simpa [term, rephaser, Fin.prod_univ_succ, mul_assoc,
    show ¬Odd (2 : ℕ) by decide] using
    reflect_rephased_term ![0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0]

-- The corresponding raw odd-control column does not satisfy the identity.
example : reflect (X 2 : MixedPoly) ≠ conjugate (X 2) := by
  intro h
  have he := congrArg (eval (fun _ : Fin 11 => (1 : ℂ))) h
  norm_num [reflectCoordinate, ConjugateGram.swap] at he

-- Mixed column parity must rotate imaginary off-diagonal coefficients with
-- the correct sign; rephasing only the columns would change the polynomial.
example : gram (!![2,-1;-1,3] : Matrix (Fin 2) (Fin 2) ℂ)
      ![C Complex.I * X 1, X 5] =
    gram (!![2,Complex.I;-Complex.I,3]) ![X 1, X 5] := by
  have hm : rephaseMatrix ![true, false]
      (!![2,Complex.I;-Complex.I,3] : Matrix (Fin 2) (Fin 2) ℂ) = !![2,-1;-1,3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rephaseMatrix_apply, rephaser]
    ring_nf
    simp
  have hz : (fun i : Fin 2 => C (rephaser (![true, false] i)) *
      (![X 1, X 5] i : MixedPoly)) = ![C Complex.I * X 1, X 5] := by
    funext i
    fin_cases i <;> simp [rephaser]
  have h := rephaseMatrix_gram ![true, false]
    (!![2,Complex.I;-Complex.I,3]) (![X 1, X 5] : Fin 2 → MixedPoly)
  rw [hm, hz] at h
  exact h

-- Empty source columns contribute zero even after embedding into a nonempty basis.
example (t : Finset (Fin 11 →₀ ℕ)) (z : t → MixedPoly)
    (B : Matrix (∅ : Finset (Fin 11 →₀ ℕ)) (∅ : Finset (Fin 11 →₀ ℕ)) ℝ) :
    gram ((FaceGram.pad B).map Complex.ofReal) z = 0 := by
  rw [pad_gram (Finset.empty_subset t)]
  simp [gram]

-- Added coordinates may contain arbitrary polynomials; only the included
-- source column contributes, with its original coefficient (not rescaled).
example (t : Finset (Fin 11 →₀ ℕ)) (h0 : 0 ∈ t) (z : t → MixedPoly) :
    gram ((FaceGram.pad (s := {0}) (t := t) (fun _ _ => 3)).map Complex.ofReal) z =
      conjugate (z ⟨0, h0⟩) * C 3 * z ⟨0, h0⟩ := by
  rw [pad_gram (Finset.singleton_subset_iff.mpr h0)]
  simp [gram]

end CZExposure.ResidualSymmetry
