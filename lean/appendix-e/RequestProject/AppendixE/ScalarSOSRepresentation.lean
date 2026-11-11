module
public import RequestProject.AppendixE.SOSStates

/-! M2: exact scalar Archimedean positivity representation modulo an ideal.
Strict positivity is essential; no uniform margin or degree bound is assumed. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry
open MvPolynomial

variable {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℝ))

omit [Fintype σ] in
/-- Every real character of the quotient is evaluation at its coordinate
values, and those coordinates annihilate every polynomial in the ideal. -/
theorem quotient_character_evaluation
    (φ : (MvPolynomial σ ℝ) ⧸ I →ₐ[ℝ] ℝ) :
    ∃ y : σ → ℝ, (∀ q ∈ I, eval y q = 0) ∧
      ∀ p, φ (Ideal.Quotient.mk I p) = eval y p := by
  let ψ : MvPolynomial σ ℝ →ₐ[ℝ] ℝ := φ.comp (Ideal.Quotient.mkₐ ℝ I)
  let y : σ → ℝ := fun i => ψ (X i)
  have he (p : MvPolynomial σ ℝ) : ψ p = eval y p := by
    induction p using MvPolynomial.induction_on with
    | C r => rw [eval_C]; exact ψ.commutes r
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, eval_X]; rfl
  refine ⟨y, ?_, he⟩
  intro q hq
  rw [← he]
  change φ (Ideal.Quotient.mk I q) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]

/-- Scalar Archimedean Positivstellensatz: a polynomial strictly positive
on the real zero set of the ideal is a finite sum of squares modulo that
ideal. The zero set may be empty, and the ideal need not be proper. -/
theorem IdealArchimedean.scalar_representation (hI : IdealArchimedean I)
    (p : MvPolynomial σ ℝ)
    (hp : ∀ y : σ → ℝ, (∀ q ∈ I, eval y q = 0) → 0 < eval y p) :
    ∃ d s, CZExposure.IsSOS d s ∧ p-s ∈ I := by
  apply (isSumSq_quotient_iff I p).mp
  apply isSumSq_of_pos_characters (hI.quotient_order_bounds I)
  intro φ
  obtain ⟨y, hy, he⟩ := quotient_character_evaluation I φ
  rw [he]
  exact hp y hy

end CZExposure.PolynomialGeometry
