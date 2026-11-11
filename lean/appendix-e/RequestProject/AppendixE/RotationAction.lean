module

public import RequestProject.AppendixE.PolynomialIntegration

/-!
# The two continuous phase rotations

The compact group `Circle × Circle` carries the optical and qubit phases.
Its action is real linear, preserves the physical domain, cost and target,
and transforms the control by its optical phase. Its polynomial pullback
has continuous coefficients and does not increase degree.
-/

@[expose] public section
noncomputable section

namespace CZExposure.RotationAction

open MvPolynomial ComplexConjugate PolynomialSymmetry PolynomialIntegration

abbrev Rotations := Circle × Circle

/-- The four unit complex multipliers, in amplitude order. -/
def phases (g : Rotations) : Fin 4 → ℂ :=
  ![(g.2 : ℂ), (g.2 : ℂ) * (g.1 : ℂ)⁻¹,
    (g.2 : ℂ)^2, (g.2 : ℂ)^2 * (g.1 : ℂ)⁻¹]

def rotate (g : Rotations) (x : State) : State :=
  mkState (phases g 0 * g1 x) (phases g 1 * r1 x)
    (phases g 2 * g2 x) (phases g 3 * r2 x)

theorem phases_unit (g : Rotations) (i : Fin 4) : ‖phases g i‖ = 1 := by
  fin_cases i <;> simp [phases, norm_pow]

theorem phases_mul (g h : Rotations) (i : Fin 4) :
    phases (g*h) i = phases g i * phases h i := by
  fin_cases i <;> simp [phases, mul_pow] <;> ring

theorem rotate_mul (g h : Rotations) (x : State) :
    rotate (g*h) x = rotate g (rotate h x) := by
  apply state_ext <;> simp [rotate, phases_mul, mul_assoc]

theorem rotate_mem_Xset (g : Rotations) {x : State} (hx : x ∈ Xset) :
    rotate g x ∈ Xset := by
  simpa [Xset, rotate, norm_mul, phases_unit] using hx

theorem cost_rotate (g : Rotations) (x : State) : cost (rotate g x) = cost x := by
  simp [cost, rotate, phases_unit]

theorem rotate_mem_XCZ (g : Rotations) {x : State} (hx : x ∈ XCZ) :
    rotate g x ∈ XCZ := by
  obtain ⟨hX, h1, h2, hg⟩ := hx
  refine ⟨rotate_mem_Xset g hX, ?_, ?_, ?_⟩
  · simp [rotate, h1]
  · simp [rotate, h2]
  · simp [rotate, phases, hg, mul_pow]

theorem zObs_rotate (g : Rotations) (x : State) : zObs (rotate g x) = zObs x := by
  simp only [zObs, rotate, g1_mkState, r1_mkState, g2_mkState, r2_mkState,
    map_mul]
  simp only [phases, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul, map_pow, map_inv₀,
    ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  field_simp

theorem rotate_initial_fibre (g : Rotations) {x : State} (hx : Jmap x = y0) :
    Jmap (rotate g x) = y0 := by
  obtain ⟨hc, hz⟩ := (Jmap_eq_y0_iff x).mp hx
  exact (Jmap_eq_y0_iff _).mpr ⟨by simpa [cost_rotate] using hc,
    by simpa [zObs_rotate] using hz⟩

/-- The action as a continuous real linear map. -/
def rotateCLM (g : Rotations) : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap
    { toFun := rotate g
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [rotate, mkState, g1, r1, g2, r2,
          Complex.mul_re, Complex.mul_im] <;> ring
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp [rotate, mkState, g1, r1, g2, r2,
          Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring }

@[simp] theorem rotateCLM_apply (g : Rotations) (x : State) :
    rotateCLM g x = rotate g x := rfl

theorem rotate_vf (g : Rotations) (x : State) (u : ℂ) :
    rotate g (vf x u) = vf (rotate g x) ((g.1 : ℂ) * u) := by
  have h1 : ∀ x u, g1 (vf x u) = fC x u 0 := fun _ _ => Complex.ext rfl rfl
  have h2 : ∀ x u, r1 (vf x u) = fC x u 1 := fun _ _ => Complex.ext rfl rfl
  have h3 : ∀ x u, g2 (vf x u) = fC x u 2 := fun _ _ => Complex.ext rfl rfl
  have h4 : ∀ x u, r2 (vf x u) = fC x u 3 := fun _ _ => Complex.ext rfl rfl
  apply state_ext <;>
    simp only [rotate, g1_mkState, r1_mkState, g2_mkState, r2_mkState, h1, h2, h3, h4,
      fC, phases, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      ← Circle.coe_inv_eq_conj, Circle.coe_inv] <;>
    field_simp

theorem rotate_exp (θ α : ℝ) (x : State) :
    rotate (Circle.exp θ, Circle.exp α) x = opticalGauge θ (qubitGauge α x) := by
  have h2 : Complex.exp ((α : ℂ) * Complex.I)^2 =
      Complex.exp (2*(α : ℂ)*Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  apply state_ext <;>
    simp [rotate, phases, opticalGauge, qubitGauge, ← Complex.exp_neg, h2] <;> ring

/-- Coordinate substitution for a real linear map. -/
def linearVars {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    Fin n → MvPolynomial (Fin n) ℝ :=
  fun i => ∑ j : Fin n, C (L (Pi.single j 1) i) * X j

theorem linearVars_degree {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (i : Fin n) :
    (linearVars L i).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

theorem eval_linearVars {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (x : Fin n → ℝ) (i : Fin n) : eval x (linearVars L i) = L x i := by
  have hx : x = ∑ j : Fin n, x j • (Pi.single j 1 : Fin n → ℝ) := by
    simpa [← Pi.single_smul] using (Finset.univ_sum_single x).symm
  conv_rhs => rw [hx]
  simp [linearVars, map_sum, map_smul, Finset.sum_apply, mul_comm]

theorem eval_aeval_linearVars {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (aeval (linearVars L) P) = eval (L x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp, eval_linearVars]

def rotatePoly (g : Rotations) (W : StatePoly) : StatePoly :=
  aeval (linearVars (rotateCLM g).toLinearMap) W

@[simp] theorem eval_rotatePoly (g : Rotations) (W : StatePoly) (x : State) :
    eval x (rotatePoly g W) = eval (rotate g x) W :=
  eval_aeval_linearVars _ _ _

theorem rotatePoly_degree (g : Rotations) (W : StatePoly) :
    (rotatePoly g W).totalDegree ≤ W.totalDegree :=
  totalDegree_aeval_le W _ (linearVars_degree _)

theorem continuous_rotate (x : State) : Continuous (fun g : Rotations => rotate g x) := by
  unfold rotate mkState
  repeat' apply Continuous.matrixVecCons
  all_goals try exact continuous_const
  all_goals simp only [phases, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals fun_prop (disch := simp)

theorem continuous_coeff_rotatePoly (W : StatePoly) (e : Fin 8 →₀ ℕ) :
    Continuous (fun g : Rotations => coeff e (rotatePoly g W)) := by
  apply continuous_coeff_aeval W
  intro i e
  simp only [linearVars, coeff_sum, coeff_C_mul]
  apply continuous_finset_sum
  intro j _
  exact ((continuous_apply i).comp (continuous_rotate (Pi.single j 1))).mul continuous_const

theorem rotatePoly_drift (g : Rotations) (W : StatePoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ x u) (lieDeriv (rotatePoly g W)) =
      eval (pt ξ (rotate g x) ((g.1 : ℂ)*u)) (lieDeriv W) := by
  rw [PolynomialApproximation.eval_lieDeriv_eq_fderiv,
    PolynomialApproximation.eval_lieDeriv_eq_fderiv]
  have hf : (fun y => eval y (rotatePoly g W)) = (fun y => eval y W) ∘ rotateCLM g := by
    funext y
    simp
  rw [hf]
  have hd := ((contDiff_eval W).differentiable (by simp) (rotateCLM g x)).hasFDerivAt.comp x
    (rotateCLM g).hasFDerivAt
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, rotateCLM_apply, rotateCLM_apply, rotate_vf]

end CZExposure.RotationAction
