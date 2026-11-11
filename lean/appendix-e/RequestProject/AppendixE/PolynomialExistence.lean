module

public import RequestProject.AppendixE.BernsteinApproximation
public import RequestProject.AppendixE.PolynomialApproximation
public import RequestProject.AppendixE.BallBoxSteering
public import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Conditional existence of `C¹` approximants and strict candidates

Applies the proved Bernstein theorem `boxC1PolynomialApproximation`
to produce a
polynomial `P` satisfying `C1ApproxOnY`, and then the previously
checked normalization and tolerance construction to produce a strict
polynomial candidate in the representation `W = strictPolynomial P η α`.

PROVED here: the operator-norm conversion `‖L‖ ≤ nδ` from
coordinatewise derivative errors (with no lost dimension factor for
the sup norm), the existence of a coordinate box containing `Yset`,
and the existence theorems below. NOT proved in this module: `G`-symmetry
averaging, any SOS representation, or `StationaryFeasible`. The
strict-candidate theorem below `Cstar` additionally takes
`EuclideanDirectedArcSuperposition` explicitly; local steering is constructed.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PolynomialGeometry

open MvPolynomial Set

/-- A continuous linear form on `ℝⁿ` (sup norm) applied to `v`
equals the sum of its coordinate values weighted by `v`. -/
theorem linearForm_apply_eq_sum {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

/-- Coordinate bounds `|L(eᵢ)| ≤ δ` give `‖L‖ ≤ nδ` for the sup-norm
operator norm. Holds at `n = 0` as well. -/
theorem linearForm_norm_le {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoord : ∀ i : Fin n, |L (Pi.single i 1)| ≤ δ) :
    ‖L‖ ≤ (n : ℝ) * δ := by
  apply ContinuousLinearMap.opNorm_le_bound L
    (mul_nonneg (Nat.cast_nonneg n) hδ)
  intro v
  rw [Real.norm_eq_abs, linearForm_apply_eq_sum]
  calc |∑ i, v i * L (Pi.single i 1)|
      ≤ ∑ i, |v i * L (Pi.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖v‖ * δ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul
          ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i) :
            |v i| ≤ ‖v‖)
          (hcoord i) (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * δ * ‖v‖ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- Evaluating a polynomial's derivative on the `i`-th basis vector
equals evaluating its `i`-th formal partial derivative. -/
theorem fderiv_eval_basis {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun y => eval y P) x (Pi.single i 1) = eval x (pderiv i P) := by
  rw [fderiv_eval_apply]
  simp [Pi.single_apply]

/-- Coordinatewise derivative errors at most `δ` give derivative
operator-norm error at most `nδ`. -/
theorem fderiv_difference_norm_le {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (φ : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoord : ∀ i : Fin n,
      |eval x (pderiv i P) - fderiv ℝ φ x (Pi.single i 1)| ≤ δ) :
    ‖fderiv ℝ (fun y => eval y P) x - fderiv ℝ φ x‖ ≤ (n : ℝ) * δ := by
  apply linearForm_norm_le _ hδ
  intro i
  rw [ContinuousLinearMap.sub_apply, fderiv_eval_basis]
  exact hcoord i

end CZExposure.PolynomialGeometry

namespace CZExposure.PolynomialApproximation

open PolynomialGeometry MvPolynomial Set

/-- Compactness of `Yset` supplies a positive-radius coordinate box
containing it. -/
theorem exists_box_for_Yset :
    ∃ R : ℝ, 0 < R ∧ Yset ⊆ coordinateBox 11 R := by
  obtain ⟨R, hR, hbound⟩ := isCompact_Yset.isBounded.exists_pos_norm_le
  refine ⟨R, hR, fun y hy i => ?_⟩
  exact ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i) :
      |y i| ≤ ‖y‖).trans (hbound y hy)

/-- Existence of a `C¹` approximating polynomial on `Yset` by Bernstein approximation. -/
theorem exists_C1ApproxOnY
    {φ : (Fin 11 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : ExposurePoly, C1ApproxOnY φ P η := by
  obtain ⟨R, hR, hbox⟩ := exists_box_for_Yset
  have hδ : (0 : ℝ) < η / 11 := div_pos hη (by norm_num)
  obtain ⟨P, hval, hpart⟩ := boxC1PolynomialApproximation 11 (by norm_num) R hR φ hφ _ hδ
  have hδη : η / 11 ≤ η := div_le_self hη.le (by norm_num)
  refine ⟨P, fun y hy => (hval y (hbox hy)).trans hδη, fun y hy => ?_⟩
  refine (fderiv_difference_norm_le P φ y hδ.le
    (fun i => hpart y (hbox hy) i)).trans_eq ?_
  field_simp
  ring

/-- Conditional existence retaining the exact polynomial form needed
by the later SOS construction. -/
theorem exists_strict_candidate
    {φ : (Fin 11 → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hbound : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
      |fderiv ℝ (centeredPullback φ) x (vf x u)| ≤ cost x)
    (a : ℝ) (ha : a < φ y0 - φ yPi) :
    ∃ (P : ExposurePoly) (η α : ℝ),
      0 < η ∧ 0 < α ∧ α < 1 ∧ C1ApproxOnY φ P η ∧
      a < eval x0 (strictPolynomial P η α) ∧
      (∀ x ∈ XCZ, eval x (strictPolynomial P η α) = 0) ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
        α*cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α))) := by
  obtain ⟨α, η, hα0, hα1, hη0, hforall⟩ :=
    exists_tolerance_for_strict_candidate (hφ.differentiable (by simp)) hbound a ha
  obtain ⟨P, hP⟩ := exists_C1ApproxOnY hφ hη0
  obtain ⟨hval, hzero, hres⟩ := hforall P hP
  exact ⟨P, η, α, hη0, hα0, hα1, hP, hval, hzero, hres⟩

/-- Conditional existence of a strict polynomial candidate below the
physical optimum, under the superposition input. -/
theorem exists_strict_candidate_below_Cstar
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ (P : ExposurePoly) (η α : ℝ),
      0 < η ∧ 0 < α ∧ α < 1 ∧
      a < eval x0 (strictPolynomial P η α) ∧
      (∀ x ∈ XCZ, eval x (strictPolynomial P η α) = 0) ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
        α*cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α))) := by
  obtain ⟨φ, hφ, _hcs, hrate, _hzero, hval⟩ :=
    CZExposure.smooth_subsolution_of_realization
      (LocalSteeringConstruction.physicalLocalSteering.Cstar_le_pRelaxed_of_superposition
        hSuperposition) a ha
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  rw [Jmap_x0] at hval
  obtain ⟨P, η, α, hη0, hα0, hα1, _hP, hv, hz, hr⟩ :=
    exists_strict_candidate hφ1 hrate a hval
  exact ⟨P, η, α, hη0, hα0, hα1, hv, hz, hr⟩

end CZExposure.PolynomialApproximation
