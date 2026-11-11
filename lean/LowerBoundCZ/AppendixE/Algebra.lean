/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Appendix E — unconditional algebraic pieces

Kernel-checked algebra used by the completeness argument of Appendix E:

* the cone augmentation `‖r‖² I − r rᵀ` and its annihilation of `r`
  (used in the scalar Schur step of the positivity argument);
* the scalar Schur positivity step, proved by completing the square;
* the Gram contraction turning a matrix factor `H` into a sum of squares of
  row factors that vanish on the Rydberg-free face `F`.

These are the exact algebraic cores only. No compactness, norm bounds, matrix
Putinar representation, or existence of the factor `H` is claimed — those
remain hypotheses to be supplied later (see `AppendixE.md`).
-/

noncomputable section

namespace LowerBoundCZ.AppendixE

section Quadratic

variable {n : ℕ}

/-- Quadratic form `vᵀAv` on a finite-dimensional real space. -/
def quadratic (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

/-- The augmentation `‖r‖² I − r rᵀ` used to make the Schur complement
block positive without changing the value on the kernel direction `r`. -/
def augmentation (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (∑ k, (r k) ^ 2) * (if i = j then 1 else 0) - r i * r j

theorem quadratic_eq_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadratic A v = ∑ i, v i * (A.mulVec v) i := by
  simp only [quadratic, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem augmentation_mulVec (r v : Fin n → ℝ) (i : Fin n) :
    (augmentation r).mulVec v i
      = (∑ k, r k ^ 2) * v i - r i * (∑ j, r j * v j) := by
  simp only [Matrix.mulVec, dotProduct, augmentation]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · have e : ∀ j : Fin n,
        (∑ k, r k ^ 2) * (if i = j then (1 : ℝ) else 0) * v j
          = if i = j then (∑ k, r k ^ 2) * v j else 0 := fun j => by
      split_ifs <;> ring
    simp_rw [e]
    simp
  · simp_rw [mul_assoc]
    exact Finset.mul_sum _ _ _ |>.symm

/-- The augmentation matrix annihilates its defining direction. -/
theorem augmentation_mulVec_self (r : Fin n → ℝ) :
    (augmentation r).mulVec r = 0 := by
  ext i
  rw [augmentation_mulVec, Pi.zero_apply]
  have h : (∑ j : Fin n, r j * r j) = ∑ j, r j ^ 2 :=
    Finset.sum_congr rfl fun j _ => (sq (r j)).symm
  rw [h]
  ring

/-- `vᵀ (‖r‖² I − r rᵀ) v = ‖r‖²‖v‖² − (r·v)²`. -/
theorem quadratic_augmentation (r v : Fin n → ℝ) :
    quadratic (augmentation r) v
      = (∑ i, r i ^ 2) * (∑ i, v i ^ 2) - (∑ i, r i * v i) ^ 2 := by
  rw [quadratic_eq_mulVec]
  simp_rw [augmentation_mulVec, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · have e : ∀ i : Fin n, v i * ((∑ k, r k ^ 2) * v i)
        = (∑ k, r k ^ 2) * (v i * v i) := fun i => by ring
    simp_rw [e, ← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [sq]
  · have e : ∀ i : Fin n, v i * (r i * (∑ j, r j * v j))
        = (v i * r i) * (∑ j, r j * v j) := fun i => by ring
    simp_rw [e, ← Finset.sum_mul]
    rw [sq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Cauchy–Schwarz: the augmentation is positive semidefinite. -/
theorem quadratic_augmentation_nonneg (r v : Fin n → ℝ) :
    0 ≤ quadratic (augmentation r) v := by
  rw [quadratic_augmentation]
  exact sub_nonneg.mpr (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r v)

theorem quadratic_add_smul (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (v : Fin n → ℝ) :
    quadratic (A + c • B) v = quadratic A v + c * quadratic B v := by
  simp only [quadratic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have e : ∀ i j : Fin n,
      v i * (A i j + c * B i j) * v j
        = v i * A i j * v j + c * (v i * B i j * v j) := fun i j => by ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem quadratic_augmentation_self (r : Fin n → ℝ) :
    quadratic (augmentation r) r = 0 := by
  rw [quadratic_augmentation]
  have h : (∑ i : Fin n, r i * r i) = ∑ i, r i ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq (r i)).symm
  rw [h]
  ring

/-- Augmenting `A` by any scalar multiple of `‖r‖²I − rrᵀ` does not change the
quadratic form on `r` — the algebraic core of the sharp Schur bound. -/
theorem quadratic_add_smul_augmentation (A : Matrix (Fin n) (Fin n) ℝ)
    (Λ : ℝ) (r : Fin n → ℝ) :
    quadratic (A + Λ • augmentation r) r = quadratic A r := by
  rw [quadratic_add_smul, quadratic_augmentation_self, mul_zero, add_zero]

end Quadratic

/-- Scalar Schur step: if `a > 0` and `a(d + t) − b² > 0`, the quadratic form
`ax² + 2bxy + (d + t)y²` is positive on every nonzero `(x, y)`. Proved by
completing the square; this is *not* the full uniform matrix positivity
lemma of the paper, which additionally needs compactness and norm bounds. -/
theorem schur_quadratic_pos {a b d t x y : ℝ}
    (ha : 0 < a) (hschur : 0 < a * (d + t) - b ^ 2) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < a * x ^ 2 + 2 * b * x * y + (d + t) * y ^ 2 := by
  have key : a * x ^ 2 + 2 * b * x * y + (d + t) * y ^ 2
      = a ⁻¹ * ((a * x + b * y) ^ 2 + (a * (d + t) - b ^ 2) * y ^ 2) := by
    field_simp
    ring
  rw [key]
  apply mul_pos (inv_pos.mpr ha)
  rcases hxy with hx | hy
  · rcases eq_or_ne y 0 with rfl | hy0
    · simpa using sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hschur (sq_pos_of_ne_zero hy0))
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos hschur (sq_pos_of_ne_zero hy))

section Polynomials

/-- Real polynomial ring in the ten ambient coordinates of Appendix E:
`Re/Im g₁, Re/Im r₁, Re/Im g₂, Re/Im r₂, Re/Im u`. -/
abbrev Poly := MvPolynomial (Fin 10) ℝ

open MvPolynomial

/-- The four Rydberg real coordinates, as polynomials. -/
def rydbergVar : Fin 4 → Poly := ![X 2, X 3, X 6, X 7]

/-- Ambient vanishing of all four Rydberg coordinates (no sphere restriction;
the algebra does not need one). Vanishing on this ambient coordinate plane
implies vanishing on the paper's normalized face `F`. -/
def OnFace (x : Fin 10 → ℝ) : Prop :=
  x 2 = 0 ∧ x 3 = 0 ∧ x 6 = 0 ∧ x 7 = 0

/-- The `k`-th row factor `∑ᵢ H_{ki} · (rydberg coordinateᵢ)`. -/
def rowFactor {m : ℕ} (H : Matrix (Fin m) (Fin 4) Poly) (k : Fin m) : Poly :=
  ∑ i, H k i * rydbergVar i

theorem eval_rydbergVar {x : Fin 10 → ℝ} (hx : OnFace x) (i : Fin 4) :
    eval x (rydbergVar i) = 0 := by
  obtain ⟨h2, h3, h6, h7⟩ := hx
  fin_cases i <;> simp [rydbergVar, h2, h3, h6, h7]

/-- Every row factor vanishes on the Rydberg-free face. -/
theorem rowFactor_eval_zero_on_face {m : ℕ} (H : Matrix (Fin m) (Fin 4) Poly)
    (k : Fin m) {x : Fin 10 → ℝ} (hx : OnFace x) :
    eval x (rowFactor H k) = 0 := by
  simp only [rowFactor, map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [eval_rydbergVar hx i, mul_zero]

/-- Generic Gram contraction over any commutative ring:
`∑ᵢⱼ vᵢ (HᵀH)ᵢⱼ vⱼ = ∑ₖ (∑ᵢ H_{ki} vᵢ)²`. -/
theorem gram_contraction {R : Type*} [CommRing R] {m n : ℕ}
    (v : Fin n → R) (H : Matrix (Fin m) (Fin n) R) :
    (∑ i, ∑ j, v i * (∑ k, H k i * H k j) * v j)
      = ∑ k, (∑ i, H k i * v i) ^ 2 := by
  have hrhs : (∑ k, (∑ i, H k i * v i) ^ 2)
      = ∑ i, ∑ j, ∑ k, v i * (H k i * H k j) * v j := by
    calc ∑ k, (∑ i, H k i * v i) ^ 2
        = ∑ k, ∑ i, ∑ j, (H k i * v i) * (H k j * v j) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ i, ∑ k, ∑ j, (H k i * v i) * (H k j * v j) := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, (H k i * v i) * (H k j * v j) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, v i * (H k i * H k j) * v j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          ring
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Specialization to the ten-variable Rydberg polynomials:
`∑ᵢⱼ (r-coordᵢ)(HᵀH)ᵢⱼ(r-coordⱼ) = ∑ₖ (rowFactor H k)²`.
This is the identity that turns a matrix-Putinar factor `H` into a sum of
squares vanishing on the face `F`. Existence of `H` is *not* asserted. -/
theorem gram_contraction_poly {m : ℕ} (H : Matrix (Fin m) (Fin 4) Poly) :
    (∑ i, ∑ j, rydbergVar i * (∑ k, H k i * H k j) * rydbergVar j)
      = ∑ k, rowFactor H k ^ 2 :=
  gram_contraction rydbergVar H

/-- The Gram right-hand side is a sum of squares, hence evaluates nonnegative
on every real assignment. -/
theorem gram_contraction_eval_nonneg {m : ℕ} (H : Matrix (Fin m) (Fin 4) Poly)
    (x : Fin 10 → ℝ) :
    0 ≤ eval x (∑ k, rowFactor H k ^ 2) := by
  rw [map_sum]
  apply Finset.sum_nonneg
  intro k _
  rw [map_pow]
  exact sq_nonneg _

/-- On the Rydberg-free face the whole contracted polynomial vanishes,
because every row factor does. -/
theorem gram_contraction_eval_zero_on_face {m : ℕ}
    (H : Matrix (Fin m) (Fin 4) Poly) {x : Fin 10 → ℝ} (hx : OnFace x) :
    eval x (∑ i, ∑ j,
        rydbergVar i * (∑ k, H k i * H k j) * rydbergVar j) = 0 := by
  rw [gram_contraction_poly, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [map_pow, rowFactor_eval_zero_on_face H k hx]
  simp

end Polynomials

end LowerBoundCZ.AppendixE
