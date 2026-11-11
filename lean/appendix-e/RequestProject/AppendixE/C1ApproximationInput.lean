module

public import Mathlib

/-!
# Generic `C¹` polynomial approximation input

This file preserves the proposition originally used as a generic input.
`BernsteinApproximation.lean` proves `boxC1PolynomialApproximation` in the
namespace `CZExposure.PolynomialGeometry`, using tensor Bernstein
approximation, a common approximation order, and affine box rescaling.
The downstream completeness API no longer requires this hypothesis.
Veretennikov and Veretennikova, arXiv:1507.05235v2, Theorems 3 and 4,
provide the corresponding classical result; the Lean proof does not assume it.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PolynomialGeometry

open MvPolynomial Set

/-- Closed symmetric coordinate box. -/
def coordinateBox (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, |x i| ≤ R}

/-- Simultaneous approximation contract, proved by `boxC1PolynomialApproximation`.
Coordinate errors are ordinary partial-derivative errors; conversion to the
operator norm is proved separately. The original dimension restriction is retained. -/
def BoxC1PolynomialApproximation : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (R : ℝ), 0 < R →
  ∀ (φ : (Fin n → ℝ) → ℝ), ContDiff ℝ 1 φ →
  ∀ (δ : ℝ), 0 < δ →
  ∃ P : MvPolynomial (Fin n) ℝ,
    (∀ x ∈ coordinateBox n R, |eval x P - φ x| ≤ δ) ∧
    (∀ x ∈ coordinateBox n R, ∀ i : Fin n,
      |eval x (pderiv i P) - fderiv ℝ φ x (Pi.single i 1)| ≤ δ)

end CZExposure.PolynomialGeometry
