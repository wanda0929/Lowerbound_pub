module
public import RequestProject.AppendixE.C1ApproximationInput

/-! Bernstein polynomial identities for simultaneous value/derivative approximation.
No approximation-existence input is asserted here. -/
@[expose] public section
noncomputable section
namespace CZExposure.BernsteinC1
open Polynomial Finset

/-- Samples are arbitrary; applications use values on the equally spaced grid. -/
def sampled (N : ℕ) (f : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ range (N + 1), C (f k) * bernsteinPolynomial ℝ N k

theorem shifted_sum (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ range (n + 1), C (f (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) +
      C (f 0) * bernsteinPolynomial ℝ n 0 = sampled n f := by
  calc
    _ = ∑ k ∈ range (n + 2), C (f k) * bernsteinPolynomial ℝ n k :=
      (sum_range_succ' _ _).symm
    _ = sampled n f := by
      rw [sum_range_succ]
      simp [sampled, bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n)]

/-- The derivative uses forward differences of the same samples, not independent
approximants of the partial derivatives. This preserves their compatibility. -/
theorem derivative_sampled (n : ℕ) (f : ℕ → ℝ) :
    derivative (sampled (n + 1) f) =
      C (n + 1 : ℝ) * sampled n (fun k => f (k + 1) - f k) := by
  have hz := bernsteinPolynomial.derivative_zero (R := ℝ) (n + 1)
  have hs := shifted_sum n f
  unfold sampled at hs ⊢
  rw [sum_range_succ']
  simp only [derivative_add, derivative_sum, derivative_mul, derivative_C, zero_mul,
    zero_add, bernsteinPolynomial.derivative_succ_aux, hz, Nat.add_sub_cancel]
  simp only [map_sub, mul_sub, sub_mul, sum_sub_distrib, Nat.cast_add, Nat.cast_one]
  simp_rw [← mul_assoc, mul_comm (C (f _)) (↑n + 1)]
  simp only [mul_assoc, ← mul_sum]
  simp only [map_add, map_natCast, map_one]
  linear_combination -(n + 1 : Polynomial ℝ) * hs

/-- The univariate derivative identity embedded in any chosen coordinate. -/
theorem pderiv_sampled {d : ℕ} (i : Fin d) (n : ℕ) (f : ℕ → ℝ) :
    MvPolynomial.pderiv i
      (aeval (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) (sampled (n + 1) f)) =
    MvPolynomial.C (n + 1 : ℝ) *
      aeval (MvPolynomial.X i) (sampled n (fun k => f (k + 1) - f k)) := by
  rw [Derivation.map_aeval, derivative_sampled]
  simp

def coordinateBasis {d : ℕ} (i : Fin d) (N k : ℕ) : MvPolynomial (Fin d) ℝ :=
  aeval (MvPolynomial.X i) (bernsteinPolynomial ℝ N k)

theorem pderiv_coordinateBasis {d : ℕ} (i j : Fin d) (N k : ℕ) :
    MvPolynomial.pderiv i (coordinateBasis j N k) =
      if i = j then aeval (MvPolynomial.X j) (derivative (bernsteinPolynomial ℝ N k))
      else 0 := by
  unfold coordinateBasis
  rw [Derivation.map_aeval]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- Tensor-product Bernstein basis; each coordinate can have its own degree. -/
def tensorBasis {d : ℕ} (N k : Fin d → ℕ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, coordinateBasis i (N i) (k i)

theorem pderiv_tensorBasis {d : ℕ} (N k : Fin d → ℕ) (i : Fin d) :
    MvPolynomial.pderiv i (tensorBasis N k) =
      aeval (MvPolynomial.X i) (derivative (bernsteinPolynomial ℝ (N i) (k i))) *
        ∏ j ∈ univ.erase i, coordinateBasis j (N j) (k j) := by
  classical
  unfold tensorBasis
  rw [← prod_erase_mul _ _ (mem_univ i), Derivation.leibniz]
  have hz : MvPolynomial.pderiv i
      (∏ j ∈ univ.erase i, coordinateBasis j (N j) (k j)) = 0 := by
    have aux (s : Finset (Fin d)) (hs : i ∉ s) : MvPolynomial.pderiv i
        (∏ j ∈ s, coordinateBasis j (N j) (k j)) = 0 := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
        rw [prod_insert hj, Derivation.leibniz]
        simp only [mem_insert, not_or] at hs
        simp [pderiv_coordinateBasis, hs.1, ih hs.2]
    exact aux _ (by simp)
  rw [hz]
  simp [pderiv_coordinateBasis, mul_comm]

def tensorSampled {d : ℕ} (N : Fin d → ℕ)
    (f : (∀ i, Fin (N i + 1)) → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ k, MvPolynomial.C (f k) * tensorBasis N (fun i => k i)

theorem eval_tensorBasis {d : ℕ} (N k : Fin d → ℕ) (x : Fin d → ℝ) :
    MvPolynomial.eval x (tensorBasis N k) =
      ∏ i, (bernsteinPolynomial ℝ (N i) (k i)).eval (x i) := by
  simp [tensorBasis, coordinateBasis, bernsteinPolynomial]

theorem tensorBasis_nonneg {d : ℕ} (N k : Fin d → ℕ)
    (x : Fin d → unitInterval) :
    0 ≤ MvPolynomial.eval (fun i => (x i : ℝ)) (tensorBasis N k) := by
  rw [eval_tensorBasis]
  apply prod_nonneg
  intro i _
  exact bernstein_nonneg (n := N i) (ν := k i) (x := x i)

theorem tensorBasis_sum {d : ℕ} (N : Fin d → ℕ) (x : Fin d → unitInterval) :
    (∑ k : ∀ i, Fin (N i + 1),
      MvPolynomial.eval (fun i => (x i : ℝ)) (tensorBasis N (fun i => k i))) = 1 := by
  simp only [eval_tensorBasis]
  rw [← Fintype.prod_sum (fun (i : Fin d) (k : Fin (N i + 1)) =>
    (bernsteinPolynomial ℝ (N i) k).eval (x i : ℝ))]
  have hb (i : Fin d) : (∑ k : Fin (N i + 1),
      (bernsteinPolynomial ℝ (N i) k).eval (x i : ℝ)) = 1 := bernstein.probability _ _
  simp_rw [hb]
  simp

/-- Stability on the whole closed cube, including its boundary. -/
theorem tensorSampled_error {d : ℕ} (N : Fin d → ℕ)
    (f : (∀ i, Fin (N i + 1)) → ℝ) (x : Fin d → unitInterval) (v ε : ℝ)
    (h : ∀ k, |f k - v| ≤ ε) :
    |MvPolynomial.eval (fun i => (x i : ℝ)) (tensorSampled N f) - v| ≤ ε := by
  let w := fun k : ∀ i, Fin (N i + 1) =>
    MvPolynomial.eval (fun i => (x i : ℝ)) (tensorBasis N (fun i => k i))
  have hw : ∑ k, w k = 1 := tensorBasis_sum N x
  have hn (k) : 0 ≤ w k := tensorBasis_nonneg _ _ x
  have he : MvPolynomial.eval (fun i => (x i : ℝ)) (tensorSampled N f) - v =
      ∑ k, (f k - v) * w k := by
    simp [tensorSampled, w, sub_mul, sum_sub_distrib, ← mul_sum, hw]
  rw [he]
  calc
    _ ≤ ∑ k, |(f k - v) * w k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ε * w k := sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (hn k)]
      exact mul_le_mul_of_nonneg_right (h k) (hn k)
    _ = ε := by rw [← mul_sum, hw, mul_one]

/-- Mean-value control of the forward difference. This needs only one
derivative, not a second derivative or an assumed Lipschitz derivative. -/
theorem forwardDifference_error (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (a h v ε : ℝ) (hh : 0 < h)
    (hv : ∀ t ∈ Set.Icc a (a + h), |deriv f t - v| ≤ ε) :
    |(f (a + h) - f a) / h - v| ≤ ε := by
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope f (by linarith : a < a + h)
    hf.continuous.continuousOn
    ((hf.differentiable (by decide)).differentiableOn)
  have ht' : t ∈ Set.Icc a (a + h) := ⟨ht.1.le, ht.2.le⟩
  simpa only [add_sub_cancel_left, he] using hv t ht'

/-- Derivative of the sampled polynomial as a positive weighted average of
grid slopes, with the correct mesh factor `n+1`. -/
theorem derivative_grid (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (derivative (sampled (n + 1) (fun k => f (k / (n + 1))))).eval x =
      ∑ k ∈ range (n + 1),
        ((f ((k + 1) / (n + 1)) - f (k / (n + 1))) / (1 / (n + 1))) *
          (bernsteinPolynomial ℝ n k).eval x := by
  rw [derivative_sampled]
  simp [sampled, eval_finset_sum, mul_sum, mul_comm, mul_left_comm, mul_assoc]

end CZExposure.BernsteinC1
