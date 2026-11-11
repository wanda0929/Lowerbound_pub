module

public import RequestProject.AppendixE.Hierarchy

/-!
# Generic matrix Positivstellensatz input

This proposition is proved by `matrixPositivstellensatz` in
`MatrixSOSTheorem.lean`; it is not an axiom or a remaining input. It is the equality-
ideal specialization of Hol--Scherer (2006), Corollary 1; see also Klep--
Schweighofer, arXiv:0907.2260, Lemma 8, Theorem 13 and Proposition 17.
The scalar Archimedean witness lifts to the matrix quadratic module.
Equality constraints are encoded with both signs, so their multipliers
disappear modulo the ideal. Stacking the finitely many square-matrix rows
gives the rectangular Gram representation below. No degree bound is assumed.
-/

@[expose] public section
noncomputable section

namespace CZExposure.PolynomialGeometry

open MvPolynomial Matrix

/-- A constant minus the squared coordinate norm is SOS modulo the ideal. -/
def IdealArchimedean {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℝ)) : Prop :=
  ∃ (N : ℕ) (d : ℕ) (s : MvPolynomial σ ℝ), IsSOS d s ∧
    C (N : ℝ) - ∑ i : σ, X i ^ 2 - s ∈ I

/-- Generic representation statement, proved in `MatrixSOSTheorem.lean`. -/
def MatrixPositivstellensatz : Prop :=
  ∀ (σ : Type) [Fintype σ] (k : ℕ), 0 < k →
  ∀ (I : Ideal (MvPolynomial σ ℝ)), IdealArchimedean I →
  ∀ (A : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ)), A.IsSymm →
    (∀ y : σ → ℝ, (∀ p ∈ I, eval y p = 0) → (A.map (eval y)).PosDef) →
    ∃ (m : ℕ) (H : Matrix (Fin m) (Fin k) (MvPolynomial σ ℝ)),
      ∀ i j, A i j - ∑ l, H l i * H l j ∈ I

end CZExposure.PolynomialGeometry
