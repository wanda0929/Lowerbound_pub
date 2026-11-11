module
public import RequestProject.AppendixE.BernsteinC1

/-! Moment estimates and uniform convergence of tensor Bernstein averages. -/
@[expose] public section
noncomputable section
namespace CZExposure.BernsteinC1
open Polynomial Finset Filter
open scoped Topology

abbrev Cube (d : ℕ) := Fin d → unitInterval
abbrev Grid {d : ℕ} (N : Fin d → ℕ) := ∀ i, Fin (N i + 1)

def weight {d : ℕ} (N : Fin d → ℕ) (x : Cube d) (k : Grid N) : ℝ :=
  ∏ i, bernstein (N i) (k i) (x i)

def node {d : ℕ} {N : Fin d → ℕ} (k : Grid N) : Cube d := fun i => bernstein.z (k i)

theorem weight_nonneg {d : ℕ} {N : Fin d → ℕ} (x : Cube d) (k : Grid N) : 0 ≤ weight N x k :=
  prod_nonneg fun _ _ => bernstein_nonneg

theorem weight_sum {d : ℕ} (N : Fin d → ℕ) (x : Cube d) : ∑ k, weight N x k = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun (i : Fin d) (k : Fin (N i + 1)) => bernstein (N i) k (x i))]
  simp [bernstein.probability]

theorem weight_marginal {d : ℕ} (N : Fin d → ℕ) (x : Cube d) (i : Fin d)
    (q : ℕ → ℝ) :
    ∑ k : Grid N, q (k i) * weight N x k =
      ∑ j : Fin (N i + 1), q j * bernstein (N i) j (x i) := by
  classical
  have hp (k : Grid N) :
      (∏ j, (if j = i then q (k j) else 1) * bernstein (N j) (k j) (x j)) =
        q (k i) * weight N x k := by
    rw [prod_mul_distrib]
    simp [weight]
  simp_rw [← hp]
  rw [← Fintype.prod_sum
    (fun (j : Fin d) (k : Fin (N j + 1)) => (if j = i then q k else 1) * bernstein (N j) k (x j))]
  have he (j : Fin d) :
      (∑ k : Fin (N j + 1), (if j = i then q k else 1) * bernstein (N j) k (x j)) =
        if j = i then ∑ k : Fin (N i + 1), q k * bernstein (N i) k (x i) else 1 := by
    by_cases h : j = i
    · subst j; simp
    · simp [h, bernstein.probability]
  simp_rw [he]
  simp

def squaredDistance {d : ℕ} (x y : Cube d) : ℝ :=
  ∑ i, ((x i : ℝ) - y i)^2

theorem squaredDistance_nonneg {d : ℕ} (x y : Cube d) : 0 ≤ squaredDistance x y :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem weight_variance {d : ℕ} {N : Fin d → ℕ} (hN : ∀ i, N i ≠ 0) (x : Cube d) :
    ∑ k : Grid N, squaredDistance x (node k) * weight N x k =
      ∑ i, (x i : ℝ) * (1 - x i) / N i := by
  simp only [squaredDistance, sum_mul, node]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [bernstein.z]
  rw [weight_marginal N x i (fun k => ((x i : ℝ) - k / N i)^2)]
  exact bernstein.variance (hN i) (x i)

theorem weight_variance_le {d : ℕ} {N : Fin d → ℕ} (hN : ∀ i, N i ≠ 0) (x : Cube d) :
    ∑ k : Grid N, squaredDistance x (node k) * weight N x k ≤ ∑ i, (1 : ℝ) / N i := by
  rw [weight_variance hN]
  apply sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (N i))
  nlinarith [sq_nonneg ((x i : ℝ) - 1/2)]

theorem dist_sq_le_squaredDistance {d : ℕ} (x y : Cube d) :
    dist x y ^ 2 ≤ squaredDistance x y := by
  have hs := squaredDistance_nonneg x y
  have hd : dist x y ≤ Real.sqrt (squaredDistance x y) := by
    apply (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Subtype.dist_eq, Real.dist_eq]
    apply (Real.le_sqrt (abs_nonneg _) hs).mpr
    rw [sq_abs]
    exact single_le_sum (fun j _ => sq_nonneg ((x j : ℝ) - y j)) (mem_univ i)
  calc
    _ ≤ (Real.sqrt (squaredDistance x y))^2 :=
      pow_le_pow_left₀ (dist_nonneg) hd 2
    _ = _ := Real.sq_sqrt hs

def average {d : ℕ} (N : Fin d → ℕ) (f : Cube d → ℝ) (x : Cube d) : ℝ :=
  ∑ k : Grid N, f (node k) * weight N x k

theorem average_polynomial {d : ℕ} (N : Fin d → ℕ) (f : Cube d → ℝ) (x : Cube d) :
    average N f x = MvPolynomial.eval (fun i => (x i : ℝ))
      (tensorSampled N (fun k => f (node k))) := by
  simp [average, tensorSampled, eval_tensorBasis, weight, bernstein_apply, bernsteinPolynomial]

/-- A uniform modulus bound converted to a quadratic error majorant. -/
theorem quadratic_majorant {d : ℕ} (f : Cube d → ℝ) {η δ C : ℝ}
    (hη : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ x y, |f y - f x| ≤ C)
    (hclose : ∀ x y, dist y x < δ → |f y - f x| ≤ η) (x y : Cube d) :
    |f y - f x| ≤ η + (C / δ^2) * squaredDistance x y := by
  by_cases h : dist y x < δ
  · exact (hclose x y h).trans (le_add_of_nonneg_right
      (mul_nonneg (div_nonneg hC (sq_nonneg _)) (squaredDistance_nonneg _ _)))
  · have hd : δ^2 ≤ squaredDistance x y := by
      have hl : δ ≤ dist x y := by simpa [dist_comm] using le_of_not_gt h
      exact (pow_le_pow_left₀ hδ.le hl 2).trans (dist_sq_le_squaredDistance x y)
    have hc : C ≤ (C / δ^2) * squaredDistance x y := by
      calc
        C = (C / δ^2) * δ^2 := (div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hδ))).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hd (div_nonneg hC (sq_nonneg _))
    exact (hbound x y).trans (hc.trans (le_add_of_nonneg_left hη))

theorem average_error_bound {d : ℕ} {N : Fin d → ℕ} (hN : ∀ i, N i ≠ 0) (f : Cube d → ℝ)
    {η δ C : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ x y, |f y - f x| ≤ C)
    (hclose : ∀ x y, dist y x < δ → |f y - f x| ≤ η) (x : Cube d) :
    |average N f x - f x| ≤ η + (C / δ^2) * ∑ i, (1 : ℝ) / N i := by
  have he : average N f x - f x =
      ∑ k : Grid N, (f (node k) - f x) * weight N x k := by
    simp [average, sub_mul, sum_sub_distrib, ← mul_sum, weight_sum]
  rw [he]
  calc
    _ ≤ ∑ k : Grid N, |(f (node k) - f x) * weight N x k| := abs_sum_le_sum_abs _ _
    _ = ∑ k : Grid N, |f (node k) - f x| * weight N x k := by
      simp [abs_mul, abs_of_nonneg (weight_nonneg x _)]
    _ ≤ ∑ k : Grid N, (η + (C / δ^2) * squaredDistance x (node k)) * weight N x k :=
      sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
        (quadratic_majorant f hη hδ hC hbound hclose x (node k)) (weight_nonneg _ _)
    _ = η + (C / δ^2) *
        ∑ k : Grid N, squaredDistance x (node k) * weight N x k := by
      simp [add_mul, sum_add_distrib, mul_assoc, ← mul_sum, weight_sum]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (weight_variance_le hN x)
      (div_nonneg hC (sq_nonneg _))) _

/-- Uniform convergence on the entire closed cube, for arbitrary finite dimension. -/
theorem average_uniform {d : ℕ} (D : ℕ → Fin d → ℕ)
    (hD : ∀ i, Tendsto (fun n => D n i) atTop atTop)
    (f : Cube d → ℝ) (hf : Continuous f) :
    TendstoUniformly (fun n => average (D n) f) f atTop := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x y, |f y - f x| ≤ C := by
    have hc : Continuous (fun p : Cube d × Cube d => |f p.2 - f p.1|) := by fun_prop
    simpa only [BddAbove, Set.Nonempty, mem_upperBounds, Set.forall_mem_range, Prod.forall]
      using (isCompact_range hc).bddAbove
  have hC0 : 0 ≤ C := by simpa using hC (fun _ => 0) (fun _ => 0)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) (ε/2) (half_pos hε)
  have ht : Tendsto (fun n => (C / δ^2) * ∑ i, (1 : ℝ) / D n i) atTop (𝓝 0) := by
    have hh := tendsto_finset_sum univ (fun i _ =>
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (hD i))
    simpa using tendsto_const_nhds.mul hh
  have hn : ∀ᶠ n in atTop, ∀ i, D n i ≠ 0 :=
    eventually_all.mpr (fun i => (hD i).eventually (eventually_ne_atTop 0))
  filter_upwards [ht.eventually_lt_const (half_pos hε), hn] with N hN hn x
  have hb := average_error_bound hn f (half_pos hε).le hδ hC0 hC
    (fun x y hxy => by simpa [Real.dist_eq] using (hclose hxy).le) x
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- Uniform perturbations of the grid coefficients survive Bernstein averaging.
This is the estimate needed when coefficients are forward differences rather
than exact samples of a partial derivative. -/
theorem sampled_average_error {d : ℕ} (N : Fin d → ℕ) (f : Cube d → ℝ)
    (a : Grid N → ℝ) {η : ℝ} (ha : ∀ k, |a k - f (node k)| ≤ η) (x : Cube d) :
    |(∑ k, a k * weight N x k) - average N f x| ≤ η := by
  have he : (∑ k, a k * weight N x k) - average N f x =
      ∑ k, (a k - f (node k)) * weight N x k := by
    simp [average, sub_mul, sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ k, |(a k - f (node k)) * weight N x k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, η * weight N x k := sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (weight_nonneg _ _)]
      exact mul_le_mul_of_nonneg_right (ha k) (weight_nonneg _ _)
    _ = η := by rw [← mul_sum, weight_sum, mul_one]

theorem sampled_uniform {d : ℕ} (D : ℕ → Fin d → ℕ)
    (hD : ∀ i, Tendsto (fun n => D n i) atTop atTop)
    (f : Cube d → ℝ) (hf : Continuous f) (a : ∀ n, Grid (D n) → ℝ)
    (ha : ∀ η > 0, ∀ᶠ n in atTop, ∀ k, |a n k - f (node k)| ≤ η) :
    TendstoUniformly (fun n x => ∑ k, a n k * weight (D n) x k) f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hu := Metric.tendstoUniformly_iff.mp (average_uniform D hD f hf)
    (ε/2) (half_pos hε)
  filter_upwards [ha (ε/2) (half_pos hε), hu] with n hn hu x
  have hb := sampled_average_error (D n) f (a n) hn x
  have hc := hu x
  rw [Real.dist_eq, abs_sub_comm] at hc ⊢
  calc
    _ ≤ |(∑ k, a n k * weight (D n) x k) - average (D n) f x| +
        |average (D n) f x - f x| := abs_sub_le _ _ _
    _ < ε := by linarith

end CZExposure.BernsteinC1
