module
public import RequestProject.AppendixE.BFieldRegularity

/-!
# Cost-weighted polynomial approximation

Constructs the exposure-coordinate map `Jmap` as real polynomials and
proves its evaluation agrees exactly with `Jmap`. Given a differentiable
function `φ` whose centered pullback has physical
drift magnitude at most `c`, and a supplied polynomial `P` satisfying
`C1ApproxOnY φ P η` with `η ≥ 0`, the state polynomial
`Q = (P∘J − P(yπ))/(1+32η)` has rate bound `|DQ·vf| ≤ c`,
is zero on every state in `XCZ`, and has initial-value error at most
`(2+32|b|)η`, where `b = φ(y0) − φ(yπ)`. For `0 < α < 1`,
the further scaled `W = (1−α)Q` has residual `c + f_u W ≥ αc`.

These are transfer and tolerance theorems. PROVED here: the actual
polynomial substitution for `J`, the cost-relative drift error, the
normalized rate and target, the initial error, the strict residual,
and the positive tolerance choice. NOT proved: existence of `C¹`
approximants, `G`-symmetry averaging, any SOS representation, or
`StationaryFeasible`. No ball-box or superposition input is used.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PolynomialApproximation

open MvPolynomial Set
open scoped NNReal ENNReal

abbrev ExposurePoly := MvPolynomial (Fin 11) ℝ

/-- `cost` as a state polynomial: `(2(X₂²+X₃²)+(X₆²+X₇²))/4`. -/
def costPoly : StatePoly :=
  C (1/4:ℝ) * (2*(X 2^2 + X 3^2) + (X 6^2 + X 7^2))

/-- `(zObs x).re` as a state polynomial (includes the Rydberg cross
terms). -/
def zRealPoly : StatePoly :=
  X 4*(X 0^2 - X 1^2) + 2*X 5*X 0*X 1 +
  C (Real.sqrt 2)*(X 6*(X 0*X 2 - X 1*X 3) + X 7*(X 0*X 3 + X 1*X 2))

/-- `(zObs x).im` as a state polynomial. -/
def zImagPoly : StatePoly :=
  X 4*(2*X 0*X 1) - X 5*(X 0^2 - X 1^2) +
  C (Real.sqrt 2)*(X 6*(X 0*X 3 + X 1*X 2) - X 7*(X 0*X 2 - X 1*X 3))

/-- `Jmap` as eleven state polynomials. -/
def Jpoly : Fin 11 → StatePoly :=
  Fin.cons zRealPoly (Fin.cons zImagPoly
    (Fin.cons (costPoly^2) (fun i => costPoly^2 * X i)))

/-- Pullback `P ∘ J` as an actual state polynomial. -/
def pullbackPoly (P : ExposurePoly) : StatePoly := aeval Jpoly P

/-- The centered, scaled candidate `Q = (P∘J − P(yπ))/(1+32η)`. -/
def normalizedPolynomial (P : ExposurePoly) (η : ℝ) : StatePoly :=
  C ((1+32*η)⁻¹) * (pullbackPoly P - C (eval yPi P))

/-- The candidate obtained by scaling `Q`: `W = (1−α)Q`. -/
def strictPolynomial (P : ExposurePoly) (η α : ℝ) : StatePoly :=
  C (1-α) * normalizedPolynomial P η

/-- The centered pullback `φ∘J − φ(yπ)`. -/
def centeredPullback (φ : (Fin 11 → ℝ) → ℝ) (x : State) : ℝ :=
  φ (Jmap x) - φ yPi

/-- Uniform value plus derivative operator-norm closeness on `Yset`.
This defines closeness only; existence of approximants is not
asserted. -/
def C1ApproxOnY (φ : (Fin 11 → ℝ) → ℝ) (P : ExposurePoly) (η : ℝ) : Prop :=
  (∀ y ∈ Yset, |eval y P - φ y| ≤ η) ∧
  ∀ y ∈ Yset, ‖fderiv ℝ (fun z => eval z P) y - fderiv ℝ φ y‖ ≤ η

/-! ## Evaluation identities -/

@[simp] theorem eval_costPoly (x : State) :
    eval x costPoly = cost x := by
  simp [costPoly, cost, r1, r2, Complex.sq_norm, Complex.normSq_apply]
  ring

@[simp] theorem eval_zRealPoly (x : State) :
    eval x zRealPoly = (zObs x).re := by
  simp [zRealPoly, zObs_re]

@[simp] theorem eval_zImagPoly (x : State) :
    eval x zImagPoly = (zObs x).im := by
  simp [zImagPoly, zObs_im]

private theorem eval_cons (x : State) {n : ℕ} (a : StatePoly)
    (f : Fin n → StatePoly) :
    (fun i => eval x (Fin.cons (α := fun _ => StatePoly) a f i)) =
      Fin.cons (α := fun _ => ℝ) (eval x a) fun i => eval x (f i) := by
  funext i
  induction i using Fin.cases with
  | zero => rw [Fin.cons_zero, Fin.cons_zero]
  | succ i => rw [Fin.cons_succ, Fin.cons_succ]

@[simp] theorem eval_Jpoly (x : State) (i : Fin 11) :
    eval x (Jpoly i) = Jmap x i := by
  have h : (fun i => eval x (Jpoly i)) = Jmap x := by
    unfold Jpoly
    rw [eval_cons, eval_cons, eval_cons]
    simp only [Jmap, eval_zRealPoly, eval_zImagPoly, eval_costPoly,
      map_pow, map_mul, eval_X]
  exact congrFun h i

@[simp] theorem eval_pullbackPoly (P : ExposurePoly) (x : State) :
    eval x (pullbackPoly P) = eval (Jmap x) P := by
  show eval x (aeval Jpoly P) = eval (Jmap x) P
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (aeval Jpoly), map_add (eval x), map_add (eval (Jmap x)),
      hp, hq]
  | mul_X p i hp =>
    rw [map_mul (aeval Jpoly), aeval_X, map_mul (eval x),
      map_mul (eval (Jmap x)), eval_X, hp, eval_Jpoly]

@[simp] theorem eval_normalizedPolynomial (P : ExposurePoly) (η : ℝ) (x : State) :
    eval x (normalizedPolynomial P η) =
      (eval (Jmap x) P - eval yPi P)/(1+32*η) := by
  simp [normalizedPolynomial, map_sub, map_mul, eval_C, eval_pullbackPoly]
  rw [div_eq_mul_inv]
  ring

@[simp] theorem eval_strictPolynomial (P : ExposurePoly) (η α : ℝ) (x : State) :
    eval x (strictPolynomial P η α) =
      (1-α)*eval x (normalizedPolynomial P η) := by
  simp [strictPolynomial, map_mul, eval_C]

/-! ## Helper lemmas -/

theorem y0_mem_Yset : y0 ∈ Yset := by
  refine ⟨x0, ?_, Jmap_x0⟩
  simp [Xset, g1, r1, g2, r2, x0, Complex.sq_norm, Complex.normSq_apply]

theorem yPi_mem_Yset : yPi ∈ Yset := by
  have hxPi : (![1, 0, 0, 0, -1, 0, 0, 0] : State) ∈ XCZ := by
    simp [XCZ, Xset, g1, r1, g2, r2, Complex.ext_iff, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]
    norm_num [← pow_two, Complex.sq_norm, Complex.normSq_apply]
  exact ⟨_, hxPi.1, Jmap_of_mem_XCZ hxPi⟩

theorem Bfield_le_32 {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖Bfield (Jmap x) u‖ ≤ 32 := by
  refine (Bfield_Jmap_bound hx hu).trans ?_
  have hc := cost_le_one hx
  have hsqrt : Real.sqrt (cost x) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hc
  nlinarith

theorem centeredPullback_fderiv {φ : (Fin 11 → ℝ) → ℝ} {x : State}
    (hφ : DifferentiableAt ℝ φ (Jmap x)) :
    fderiv ℝ (centeredPullback φ) x =
      (fderiv ℝ φ (Jmap x)).comp (fderiv ℝ Jmap x) := by
  show fderiv ℝ (fun x => φ (Jmap x) - φ yPi) x = _
  rw [fderiv_sub_const]
  exact (hφ.hasFDerivAt.comp x
    (contDiff_Jmap.differentiable (by simp) x).hasFDerivAt).fderiv

theorem centeredPullback_drift_eq {φ : (Fin 11 → ℝ) → ℝ} {x : State}
    (hφ : DifferentiableAt ℝ φ (Jmap x)) (u : ℂ) :
    fderiv ℝ (centeredPullback φ) x (vf x u) =
      cost x * fderiv ℝ φ (Jmap x) (Bfield (Jmap x) u) := by
  rw [centeredPullback_fderiv hφ, ContinuousLinearMap.comp_apply,
    ← cost_smul_Bfield, map_smul, smul_eq_mul]

theorem centeredPullback_drift_error
    {φ ψ : (Fin 11 → ℝ) → ℝ} {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hφ : DifferentiableAt ℝ φ (Jmap x))
    (hψ : DifferentiableAt ℝ ψ (Jmap x))
    (hD : ‖fderiv ℝ ψ (Jmap x) - fderiv ℝ φ (Jmap x)‖ ≤ η) :
    |fderiv ℝ (centeredPullback ψ) x (vf x u) -
      fderiv ℝ (centeredPullback φ) x (vf x u)| ≤ 32*η*cost x := by
  rw [centeredPullback_drift_eq hψ u, centeredPullback_drift_eq hφ u,
    ← mul_sub, abs_mul, abs_of_nonneg (cost_nonneg x)]
  calc cost x *
        |fderiv ℝ ψ (Jmap x) (Bfield (Jmap x) u) -
          fderiv ℝ φ (Jmap x) (Bfield (Jmap x) u)|
      ≤ cost x * (η * 32) := by
        apply mul_le_mul_of_nonneg_left _ (cost_nonneg x)
        rw [← ContinuousLinearMap.sub_apply]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hD (Bfield_le_32 hx hu) (norm_nonneg _) hη)
    _ = 32 * η * cost x := by ring

theorem eval_lieDeriv_eq_fderiv (W : StatePoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ x u) (lieDeriv W) =
      fderiv ℝ (fun y => eval y W) x (vf x u) := by
  rw [eval_pt_lieDeriv, fderiv_eval_apply]

theorem normalization_denominator_pos {η : ℝ} (hη : 0 ≤ η) : 0 < 1 + 32*η := by
  linarith

theorem normalized_fderiv_apply (P : ExposurePoly) (η : ℝ) (x v : State) :
    fderiv ℝ (fun y => eval y (normalizedPolynomial P η)) x v =
      (1+32*η)⁻¹ * fderiv ℝ (centeredPullback (fun y => eval y P)) x v := by
  have hfun : (fun y => eval y (normalizedPolynomial P η)) =
      fun y => (1+32*η)⁻¹ * centeredPullback (fun y => eval y P) y := by
    funext y
    rw [eval_normalizedPolynomial, centeredPullback, div_eq_mul_inv]
    ring
  rw [hfun]
  have hd : DifferentiableAt ℝ (centeredPullback (fun y => eval y P)) x := by
    show DifferentiableAt ℝ (fun x => (fun y => eval y P) (Jmap x) -
      (fun y => eval y P) yPi) x
    exact DifferentiableAt.sub_const
      (((contDiff_eval P).differentiable (by simp) (Jmap x)).comp x
        (contDiff_Jmap.differentiable (by simp) x)) _
  rw [(hd.hasFDerivAt.const_mul _).fderiv,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- No approximation assumption needed; the `DJ·vf = c·B` geometry
alone kills the drift on the zero-cost face. -/
theorem normalized_drift_zero_of_cost_zero (P : ExposurePoly) (η : ℝ)
    {x : State} (hc : cost x = 0) (u : ℂ) :
    fderiv ℝ (fun y => eval y (normalizedPolynomial P η)) x (vf x u) = 0 := by
  rw [normalized_fderiv_apply,
    centeredPullback_drift_eq
      ((contDiff_eval P).differentiable (by simp) (Jmap x)) u]
  rw [hc, zero_mul, mul_zero]

/-! ## Core transfer theorems -/

theorem normalized_drift_bound
    {φ : (Fin 11 → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (hbound : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
      |fderiv ℝ (centeredPullback φ) x (vf x u)| ≤ cost x)
    {P : ExposurePoly} {η : ℝ} (hη : 0 ≤ η) (hP : C1ApproxOnY φ P η)
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |fderiv ℝ (fun y => eval y (normalizedPolynomial P η)) x (vf x u)| ≤
      cost x := by
  rw [normalized_fderiv_apply]
  have hφJ : DifferentiableAt ℝ φ (Jmap x) := hφ.differentiableAt
  have hPJ : DifferentiableAt ℝ (fun y => eval y P) (Jmap x) :=
    (contDiff_eval P).differentiable (by simp) (Jmap x)
  have hD := hP.2 (Jmap x) ⟨x, hx, rfl⟩
  have herr := centeredPullback_drift_error hx hu hη hφJ hPJ hD
  have hmain := hbound x hx u hu
  have hsum : |fderiv ℝ (centeredPullback (fun y => eval y P)) x (vf x u)| ≤
      (1+32*η)*cost x := by
    calc |fderiv ℝ (centeredPullback (fun y => eval y P)) x (vf x u)|
        = |fderiv ℝ (centeredPullback (fun y => eval y P)) x (vf x u) -
            fderiv ℝ (centeredPullback φ) x (vf x u) +
            fderiv ℝ (centeredPullback φ) x (vf x u)| := by
          rw [sub_add_cancel]
      _ ≤ |fderiv ℝ (centeredPullback (fun y => eval y P)) x (vf x u) -
            fderiv ℝ (centeredPullback φ) x (vf x u)| +
            |fderiv ℝ (centeredPullback φ) x (vf x u)| := abs_add_le _ _
      _ ≤ 32*η*cost x + cost x := add_le_add herr hmain
      _ = (1+32*η)*cost x := by ring
  have hpos : (0:ℝ) ≤ (1+32*η)⁻¹ :=
    inv_nonneg.mpr (normalization_denominator_pos hη).le
  rw [abs_mul, abs_of_nonneg hpos]
  calc (1+32*η)⁻¹ * |fderiv ℝ (centeredPullback (fun y => eval y P)) x (vf x u)|
      ≤ (1+32*η)⁻¹ * ((1+32*η)*cost x) :=
        mul_le_mul_of_nonneg_left hsum hpos
    _ = cost x := by
        rw [← mul_assoc, inv_mul_cancel₀
          (normalization_denominator_pos hη).ne', one_mul]

theorem normalized_target_zero (P : ExposurePoly) (η : ℝ)
    {x : State} (hx : x ∈ XCZ) : eval x (normalizedPolynomial P η) = 0 := by
  rw [eval_normalizedPolynomial, Jmap_of_mem_XCZ hx, sub_self, zero_div]

theorem normalized_initial_error
    {φ : (Fin 11 → ℝ) → ℝ} {P : ExposurePoly} {η : ℝ}
    (hη : 0 ≤ η) (hP : C1ApproxOnY φ P η) :
    |eval x0 (normalizedPolynomial P η) - (φ y0 - φ yPi)| ≤
      (2+32*|φ y0 - φ yPi|)*η := by
  set b := φ y0 - φ yPi with hb
  set D := (1:ℝ) + 32*η with hDdef
  have hDpos : 0 < D := normalization_denominator_pos hη
  have hn : |eval y0 P - eval yPi P - b| ≤ 2*η := by
    have h1 := hP.1 y0 y0_mem_Yset
    have h2 := hP.1 yPi yPi_mem_Yset
    have hid : eval y0 P - eval yPi P - (φ y0 - φ yPi) =
        (eval y0 P - φ y0) - (eval yPi P - φ yPi) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  rw [eval_normalizedPolynomial, Jmap_x0]
  have hkey : (eval y0 P - eval yPi P)/D - b =
      ((eval y0 P - eval yPi P - b) - 32*η*b)/D := by
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hDpos]
  calc |(eval y0 P - eval yPi P - b) - 32*η*b|/D
      ≤ ((2+32*|b|)*η)/D := by
        apply div_le_div_of_nonneg_right _ hDpos.le
        calc |(eval y0 P - eval yPi P - b) - 32*η*b|
            ≤ |eval y0 P - eval yPi P - b| + |32*η*b| := abs_sub _ _
          _ ≤ 2*η + |32*η*b| := add_le_add hn le_rfl
          _ = (2+32*|b|)*η := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 32),
              abs_of_nonneg hη]
            ring
    _ ≤ (2+32*|b|)*η := by
        have hD1 : 1 ≤ D := by linarith
        exact div_le_self (by positivity) hD1

theorem strict_drift_bound
    {φ : (Fin 11 → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (hbound : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
      |fderiv ℝ (centeredPullback φ) x (vf x u)| ≤ cost x)
    {P : ExposurePoly} {η α : ℝ} (hη : 0 ≤ η) (hα : α ≤ 1)
    (hP : C1ApproxOnY φ P η) {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |fderiv ℝ (fun y => eval y (strictPolynomial P η α)) x (vf x u)| ≤
      (1-α)*cost x := by
  have hfun : (fun y => eval y (strictPolynomial P η α)) =
      fun y => (1-α) * eval y (normalizedPolynomial P η) := by
    funext y
    rw [eval_strictPolynomial]
  rw [hfun]
  have hnorm : DifferentiableAt ℝ (fun y => eval y (normalizedPolynomial P η)) x :=
    (contDiff_eval _).differentiable (by simp) x
  rw [(hnorm.hasFDerivAt.const_mul _).fderiv,
    ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1-α)]
  exact mul_le_mul_of_nonneg_left
    (normalized_drift_bound hφ hbound hη hP hx hu) (by linarith)

theorem strict_residual_bound
    {φ : (Fin 11 → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (hbound : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
      |fderiv ℝ (centeredPullback φ) x (vf x u)| ≤ cost x)
    {P : ExposurePoly} {η α : ℝ} (hη : 0 ≤ η) (hα : α ≤ 1)
    (hP : C1ApproxOnY φ P η) {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ ≤ 1) (ξ : ℝ) :
    α*cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α)) := by
  rw [map_add, eval_pt_cpoly, eval_lieDeriv_eq_fderiv]
  have h := (abs_le.mp (strict_drift_bound hφ hbound hη hα hP hx hu)).1
  linarith

theorem strict_target_zero (P : ExposurePoly) (η α : ℝ)
    {x : State} (hx : x ∈ XCZ) : eval x (strictPolynomial P η α) = 0 := by
  rw [eval_strictPolynomial, normalized_target_zero P η hx, mul_zero]

theorem strict_initial_error
    {φ : (Fin 11 → ℝ) → ℝ} {P : ExposurePoly} {η α : ℝ}
    (hη : 0 ≤ η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hP : C1ApproxOnY φ P η) :
    |eval x0 (strictPolynomial P η α) - (φ y0 - φ yPi)| ≤
      α*|φ y0 - φ yPi| + (2+32*|φ y0 - φ yPi|)*η := by
  set q := eval x0 (normalizedPolynomial P η) with hqdef
  set b := φ y0 - φ yPi with hb
  have hq := normalized_initial_error hη hP
  rw [eval_strictPolynomial]
  have hnn : (0:ℝ) ≤ 1 - α := by linarith
  have hE : (0:ℝ) ≤ (2+32*|b|)*η :=
    mul_nonneg (by linarith [abs_nonneg b]) hη
  have hid : (1-α)*q - b = (1-α)*(q - b) - α*b := by ring
  rw [show (1-α)*eval x0 (normalizedPolynomial P η) - b =
      (1-α)*(q - b) - α*b from hid]
  calc |(1-α)*(q - b) - α*b|
      ≤ |(1-α)*(q - b)| + |α*b| := abs_sub _ _
    _ = (1-α)*|q - b| + α*|b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnn, abs_of_nonneg hα0]
    _ ≤ (1-α)*((2+32*|b|)*η) + α*|b| := by
        exact add_le_add (mul_le_mul_of_nonneg_left hq hnn) le_rfl
    _ ≤ α*|b| + (2+32*|b|)*η := by
        have hle : (1-α)*((2+32*|b|)*η) ≤ (2+32*|b|)*η := by
          have := mul_le_mul_of_nonneg_right (show (1:ℝ)-α ≤ 1 by linarith) hE
          rwa [one_mul] at this
        linarith

theorem exists_small_parameters (a b : ℝ) (hab : a < b) :
    ∃ α η : ℝ, 0 < α ∧ α < 1 ∧ 0 < η ∧
      α*|b| + (2+32*|b|)*η < b - a := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  set α := min (1/2 : ℝ) ((b-a)/(4*(|b|+1)))
  set η := (b-a)/(4*(2+32*|b|))
  have hα0 : 0 < α := lt_min (by norm_num) (div_pos hgap (by positivity))
  have hα1 : α < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hη0 : 0 < η := div_pos hgap (by positivity)
  refine ⟨α, η, hα0, hα1, hη0, ?_⟩
  have h1 : α*|b| ≤ (b-a)/4 := by
    have hαb : α*(|b|+1) ≤ (b-a)/4 := by
      calc α*(|b|+1) ≤ ((b-a)/(4*(|b|+1)))*(|b|+1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _)
              (by positivity : (0:ℝ) ≤ |b|+1)
        _ = (b-a)/4 := by field_simp
    nlinarith [abs_nonneg b, hα0.le, hαb]
  have h2 : (2+32*|b|)*η = (b-a)/4 := by
    rw [show η = (b-a)/(4*(2+32*|b|)) from rfl]
    field_simp
  linarith

/-- Positive parameters chosen before the approximating polynomial;
NO existence of `P` is asserted. -/
theorem exists_tolerance_for_strict_candidate
    {φ : (Fin 11 → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (hbound : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
      |fderiv ℝ (centeredPullback φ) x (vf x u)| ≤ cost x)
    (a : ℝ) (ha : a < φ y0 - φ yPi) :
    ∃ α η : ℝ, 0 < α ∧ α < 1 ∧ 0 < η ∧ ∀ P : ExposurePoly,
      C1ApproxOnY φ P η →
        a < eval x0 (strictPolynomial P η α) ∧
        (∀ x ∈ XCZ, eval x (strictPolynomial P η α) = 0) ∧
        (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
          α*cost x ≤
            eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α))) := by
  obtain ⟨α, η, hα0, hα1, hη0, hbudget⟩ :=
    exists_small_parameters a (φ y0 - φ yPi) ha
  refine ⟨α, η, hα0, hα1, hη0, fun P hP => ?_⟩
  have hinit := strict_initial_error hη0.le hα0.le hα1.le hP
  have habs := lt_of_le_of_lt hinit hbudget
  refine ⟨?_, fun x hx => strict_target_zero P η α hx,
    fun x hx u hu ξ => strict_residual_bound hφ hbound hη0.le hα1.le hP hx hu ξ⟩
  linarith [(abs_lt.mp habs).1]

end CZExposure.PolynomialApproximation
