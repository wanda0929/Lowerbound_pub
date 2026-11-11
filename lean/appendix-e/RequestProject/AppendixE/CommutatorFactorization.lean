module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.Abel

/-!
Exact factorization for the short pulse commutator V⁻¹ U⁻¹ V U.
The inverse paths are explicit inputs (reverse pulse words), not an
assumption of controllability. This module proves the vanishing-order
step only; it does not assert physical realization or local steering.
-/

@[expose] public section

namespace CZExposure.PulseCommutator

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The order is chosen to give BA − AB, matching the vector-field
bracket convention used in `ControlLieAlgebra`. -/
def word (U V Ui Vi : A) : A := Vi * Ui * V * U

omit [NormedAlgebra ℝ A] in
theorem word_sub_one (U V Ui Vi : A)
    (hU : Ui * U = 1) (hV : Vi * V = 1) :
    word U V Ui Vi - 1 = Vi * Ui * (V * U - U * V) := by
  have h : Vi * Ui * U * V = 1 := by
    calc
      Vi * Ui * U * V = Vi * (Ui * U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hU, mul_one, hV]
  rw [word, mul_sub, ← mul_assoc, ← mul_assoc, h]

/-- Exact extraction of the combined order, with no asymptotic
division at zero. It applies recursively to nested pulse words. -/
theorem factor (t : ℝ) (a b : ℕ) (P Q Ui Vi : A)
    (hU : Ui * (1 + t ^ a • P) = 1)
    (hV : Vi * (1 + t ^ b • Q) = 1) :
    word (1 + t ^ a • P) (1 + t ^ b • Q) Ui Vi =
      1 + t ^ (a + b) • (Vi * Ui * (Q * P - P * Q)) := by
  have hswap :
      (1 + t ^ b • Q) * (1 + t ^ a • P) -
        (1 + t ^ a • P) * (1 + t ^ b • Q) =
      t ^ (a + b) • (Q * P - P * Q) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul, pow_add, smul_sub]
    rw [mul_comm (t ^ b) (t ^ a)]
    abel
  have h := word_sub_one (1 + t ^ a • P) (1 + t ^ b • Q) Ui Vi hU hV
  rw [hswap, mul_smul_comm] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Smooth normalized coefficient. This retains derivative information
needed for signed-root reparameterization; a pointwise little-o bound
alone would not suffice. -/
theorem coefficient_contDiff {n : WithTop ℕ∞}
    {P Q Ui Vi : ℝ → A}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q)
    (hUi : ContDiff ℝ n Ui) (hVi : ContDiff ℝ n Vi) :
    ContDiff ℝ n (fun t => Vi t * Ui t * (Q t * P t - P t * Q t)) :=
  (hVi.mul hUi).mul ((hQ.mul hP).sub (hP.mul hQ))

omit [NormedAlgebra ℝ A] in
theorem coefficient_zero (P Q Ui Vi : ℝ → A)
    (hUi : Ui 0 = 1) (hVi : Vi 0 = 1) :
    Vi 0 * Ui 0 * (Q 0 * P 0 - P 0 * Q 0) = Q 0 * P 0 - P 0 * Q 0 := by
  rw [hUi, hVi, one_mul, one_mul]

end CZExposure.PulseCommutator
