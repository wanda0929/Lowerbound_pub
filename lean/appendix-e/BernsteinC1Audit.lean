import RequestProject.AppendixE.BernsteinC1
import RequestProject.AppendixE.BernsteinConvergence
import RequestProject.AppendixE.BernsteinDerivatives
import RequestProject.AppendixE.BernsteinApproximation

open CZExposure.BernsteinC1 Polynomial

-- A nonconstant quadratic detects both the mesh factor and forward-difference sign.
example : derivative (sampled 2 (fun k => (k : ℝ)^2)) =
    2 + 4 * X := by
  norm_num [sampled, bernsteinPolynomial, Finset.sum_range_succ]
  norm_num only [map_ofNat]
  ring

-- Endpoints must be included in the derivative formula, not only the open cube.
example : (derivative (sampled 2 (fun k => (k : ℝ)^2))).eval 0 = 2 := by
  norm_num [sampled, bernsteinPolynomial, Finset.sum_range_succ, eval_finset_sum]

example : (derivative (sampled 2 (fun k => (k : ℝ)^2))).eval 1 = 6 := by
  norm_num [sampled, bernsteinPolynomial, Finset.sum_range_succ, eval_finset_sum]

-- Asymmetric two-coordinate data checks cross-coordinate differentiation.
example : MvPolynomial.pderiv (0 : Fin 2) (tensorBasis ![2, 1] ![1, 1]) =
    2 * (1 - 2 * MvPolynomial.X 0) * MvPolynomial.X 1 := by
  have hz : MvPolynomial.pderiv (0 : Fin 2) (2 : MvPolynomial (Fin 2) ℝ) = 0 :=
    Derivation.map_natCast _ 2
  simp [tensorBasis, coordinateBasis, bernsteinPolynomial, Fin.prod_univ_succ,
    Derivation.leibniz, hz]
  ring

-- Constant reproduction includes all boundary points and degree-zero coordinates.
example {d : ℕ} (N : Fin d → ℕ) (x : Fin d → unitInterval) (v : ℝ) :
    MvPolynomial.eval (fun i => (x i : ℝ)) (tensorSampled N (fun _ => v)) = v := by
  have h := tensorSampled_error N (fun _ => v) x v 0 (by simp)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

run_cmd do
  for name in [``derivative_sampled, ``pderiv_sampled,
      ``pderiv_tensorBasis, ``tensorBasis_nonneg, ``tensorBasis_sum,
      ``tensorSampled_error, ``forwardDifference_error, ``derivative_grid] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Unequal degrees retain their own variance denominators.
example (x : Cube 2) :
    (∑ k : Grid ![2, 4], squaredDistance x (node k) * weight ![2, 4] x k) =
      (x 0 : ℝ) * (1 - x 0) / 2 + (x 1 : ℝ) * (1 - x 1) / 4 := by
  rw [weight_variance (by intro i; fin_cases i <;> norm_num)]
  simp [Fin.sum_univ_succ]

-- In particular, the degrees needed after one coordinate derivative may differ.
example {d : ℕ} (i : Fin d) (f : Cube d → ℝ) (hf : Continuous f) :
    TendstoUniformly (fun n => average (fun j => if j = i then n else n + 1) f)
      f Filter.atTop := by
  apply average_uniform _ _ f hf
  intro j
  by_cases h : j = i
  · simpa [h] using (Filter.tendsto_id : Filter.Tendsto (fun n : ℕ => n) _ _)
  · simpa [h] using Filter.tendsto_add_atTop_nat 1

-- Value convergence is for the actual multivariate polynomial evaluation.
example {d : ℕ} (f : Cube d → ℝ) (hf : Continuous f) :
    TendstoUniformly (fun n x => MvPolynomial.eval (fun i => (x i : ℝ))
      (tensorSampled (fun _ : Fin d => n) (fun k => f (node k)))) f Filter.atTop := by
  simp_rw [← average_polynomial]
  exact average_uniform (fun n _ => n) (fun _ => Filter.tendsto_id) f hf

run_cmd do
  for name in [``weight_marginal, ``weight_variance, ``weight_variance_le,
      ``dist_sq_le_squaredDistance, ``average_error_bound, ``average_uniform,
      ``sampled_average_error, ``sampled_uniform, ``average_polynomial] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Last cell touches the boundary, and only the differentiated degree is lowered.
example : differenceCoefficient (fun x : Fin 2 → ℝ => x 0 ^ 2 + 3 * x 1) 2 0
    (fun j => if h : j = 0 then ⟨2, by simp [derivativeDegrees, h]⟩
      else ⟨1, by simp [derivativeDegrees, h]⟩) = 5 / 3 := by
  norm_num [differenceCoefficient, cellBase, realPoint, Function.update]

example : differenceCoefficient (fun x : Fin 2 → ℝ => x 0 ^ 2 + 3 * x 1) 0 0
    (fun _ => ⟨0, by simp [derivativeDegrees]⟩) = 1 := by
  norm_num [differenceCoefficient, cellBase, realPoint, Function.update]

run_cmd do
  for name in [``tensorBasis_insert, ``tensorSampled_slices, ``pderiv_restBasis,
      ``pderiv_tensorSampled_slices, ``partialValue_continuous, ``uniform_secant,
      ``cellBase_end, ``cellBase_distance, ``differenceCoefficient_uniform,
      ``differenceAverage_uniform] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- The old input is now inhabited without supplying any additional proposition.
example : CZExposure.PolynomialGeometry.BoxC1PolynomialApproximation :=
  CZExposure.PolynomialGeometry.boxC1PolynomialApproximation

-- An asymmetric polynomial at the R=3 box boundary detects the 1/(2R) factor.
example : MvPolynomial.eval ![3, -3]
    (MvPolynomial.pderiv 0 (affineSubst (1/6) (1/2)
      ((MvPolynomial.X (0 : Fin 2))^2 + 3 * MvPolynomial.X 1))) = 1/3 := by
  rw [pderiv_affineSubst]
  norm_num [eval_affineSubst, Derivation.leibniz]

-- R=1/4 magnifies rather than shrinks derivative errors.
example : MvPolynomial.eval ![0, 1/4]
    (MvPolynomial.pderiv 1 (affineSubst 2 (1/2)
      ((MvPolynomial.X (0 : Fin 2))^2 + 3 * MvPolynomial.X 1))) = 6 := by
  have h3 : MvPolynomial.pderiv (1 : Fin 2) (3 : MvPolynomial (Fin 2) ℝ) = 0 :=
    Derivation.map_natCast _ 3
  rw [pderiv_affineSubst]
  norm_num [eval_affineSubst, Derivation.leibniz, h3]

run_cmd do
  for name in [``pderiv_tensorSampled_update, ``pderiv_approximant,
      ``eval_approximant_uniform, ``eval_pderiv_approximant_uniform,
      ``exists_cube_C1, ``eval_affineSubst, ``pderiv_affineSubst,
      ``partial_affine, ``CZExposure.PolynomialGeometry.boxC1PolynomialApproximation] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
