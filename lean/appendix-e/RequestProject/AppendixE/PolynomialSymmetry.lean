module

public import RequestProject.AppendixE.PolynomialExistence
public import RequestProject.AppendixE.SectorPhase

/-!
# Polynomial symmetry: reflection averaging

Constructs the reflection average as an actual real polynomial, without
increasing degree. Reflection pairs the control with `-conj u`, not `conj u`.
The average preserves the initial value, terminal zero, and weighted residual
margin. It preserves both rotation invariances when they are already present.
The continuous rotation average is not constructed in this module.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PolynomialSymmetry

open MvPolynomial ComplexConjugate
open PolynomialApproximation

/-- Substituting polynomials of degree at most one does not increase degree. -/
theorem totalDegree_aeval_le {σ τ K : Type*} [CommSemiring K]
    (p : MvPolynomial σ K) (s : σ → MvPolynomial τ K)
    (hs : ∀ i, (s i).totalDegree ≤ 1) :
    (aeval s p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  refine (Finset.sum_le_sum fun i hi =>
    (totalDegree_pow (s i) (d i)).trans (Nat.mul_le_mul_left (d i) (hs i))).trans ?_
  simpa using (le_totalDegree hd : d.sum (fun _ e => e) ≤ p.totalDegree)

/-- The diagonal signs of complex conjugation in real coordinates. -/
def reflectionSign : Fin 8 → ℝ := ![1, -1, 1, -1, 1, -1, 1, -1]

theorem reflection_apply (x : State) (i : Fin 8) :
    reflection x i = reflectionSign i * x i := by
  fin_cases i <;> simp [reflection, reflectionSign, mkState, g1, r1, g2, r2]

/-- Complex conjugation as a real continuous linear map. -/
def reflectionCLM : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap
    { toFun := reflection
      map_add' := by
        intro x y
        funext i
        simp [reflection_apply, mul_add]
      map_smul' := by
        intro a x
        funext i
        simp [reflection_apply, mul_left_comm] }

@[simp] theorem reflectionCLM_apply (x : State) : reflectionCLM x = reflection x := rfl

@[simp] theorem reflection_reflection (x : State) : reflection (reflection x) = x := by
  apply state_ext <;> simp [reflection]

@[simp] theorem reflection_x0 : reflection x0 = x0 := by
  funext i
  fin_cases i <;> norm_num [reflection_apply, reflectionSign, x0]

@[simp] theorem cost_reflection (x : State) : cost (reflection x) = cost x := by
  simp [cost, reflection]

theorem reflection_mem_Xset {x : State} (hx : x ∈ Xset) : reflection x ∈ Xset := by
  simpa [Xset, reflection] using hx

theorem reflection_mem_XCZ {x : State} (hx : x ∈ XCZ) : reflection x ∈ XCZ := by
  obtain ⟨hX, h1, h2, hg⟩ := hx
  refine ⟨reflection_mem_Xset hX, ?_, ?_, ?_⟩
  · simp [reflection, h1]
  · simp [reflection, h2]
  · simpa [reflection] using congrArg (conj : ℂ → ℂ) hg

/-- The minus sign is forced by conjugation of the factor `-i` in the ODE. -/
theorem reflection_vf (x : State) (u : ℂ) :
    reflection (vf x u) = vf (reflection x) (-conj u) := by
  funext i
  fin_cases i <;>
    simp [vf, fC, reflection, mkState, g1, r1, g2, r2,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Substitution of conjugated real coordinates. -/
def reflectPoly (W : StatePoly) : StatePoly :=
  aeval (fun i => C (reflectionSign i) * X i) W

@[simp] theorem eval_reflectPoly (W : StatePoly) (x : State) :
    eval x (reflectPoly W) = eval (reflection x) W := by
  induction W using MvPolynomial.induction_on with
  | C a => simp [reflectPoly]
  | add p q hp hq => simpa [reflectPoly] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simpa [reflectPoly, reflection_apply] using
      congrArg (fun a => a * (reflectionSign i * x i)) hp

theorem reflectPoly_degree (W : StatePoly) : (reflectPoly W).totalDegree ≤ W.totalDegree := by
  apply totalDegree_aeval_le
  intro i
  exact (totalDegree_mul _ _).trans (by simp)

/-- The polynomial `(W + W ∘ reflection)/2`. -/
def reflectionAverage (W : StatePoly) : StatePoly :=
  C (1/2 : ℝ) * (W + reflectPoly W)

@[simp] theorem eval_reflectionAverage (W : StatePoly) (x : State) :
    eval x (reflectionAverage W) = (eval x W + eval (reflection x) W)/2 := by
  simp [reflectionAverage]
  ring

theorem reflectionAverage_degree (W : StatePoly) :
    (reflectionAverage W).totalDegree ≤ W.totalDegree := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_add _ _).trans (max_le le_rfl (reflectPoly_degree W))

theorem reflectionAverage_invariant (W : StatePoly) (x : State) :
    eval (reflection x) (reflectionAverage W) = eval x (reflectionAverage W) := by
  simp [add_comm]

@[simp] theorem reflectionAverage_initial (W : StatePoly) :
    eval x0 (reflectionAverage W) = eval x0 W := by
  simp

theorem reflectionAverage_target_zero {W : StatePoly}
    (hW : ∀ x ∈ XCZ, eval x W = 0) {x : State} (hx : x ∈ XCZ) :
    eval x (reflectionAverage W) = 0 := by
  simp [hW x hx, hW _ (reflection_mem_XCZ hx)]

theorem reflectPoly_drift (W : StatePoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ x u) (lieDeriv (reflectPoly W)) =
      eval (pt ξ (reflection x) (-conj u)) (lieDeriv W) := by
  rw [eval_lieDeriv_eq_fderiv, eval_lieDeriv_eq_fderiv]
  have hf : (fun y => eval y (reflectPoly W)) =
      (fun y => eval y W) ∘ reflectionCLM := by
    funext y
    simp
  rw [hf]
  have hd := ((contDiff_eval W).differentiable (by simp)
    (reflectionCLM x)).hasFDerivAt.comp x reflectionCLM.hasFDerivAt
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, reflectionCLM_apply,
    reflectionCLM_apply, reflection_vf]

theorem reflectionAverage_drift (W : StatePoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ x u) (lieDeriv (reflectionAverage W)) =
      (eval (pt ξ x u) (lieDeriv W) +
        eval (pt ξ (reflection x) (-conj u)) (lieDeriv W))/2 := by
  rw [← reflectPoly_drift]
  simp [reflectionAverage, lieDeriv, ofState, mul_add, add_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  ring

/-- The weighted margin is preserved, including on the zero-cost face. -/
theorem reflectionAverage_residual {W : StatePoly} {α : ℝ}
    (hW : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv W))
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) (ξ : ℝ) :
    α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (reflectionAverage W)) := by
  have h1 := hW x hx u hu ξ
  have h2 := hW (reflection x) (reflection_mem_Xset hx) (-conj u) (by simpa using hu) ξ
  simp only [map_add, eval_pt_cpoly, cost_reflection] at h1 h2 ⊢
  rw [reflectionAverage_drift]
  linarith

/-! ## The initial exposure fibre is preserved by every generator -/

theorem cost_opticalGauge (θ : ℝ) (x : State) : cost (opticalGauge θ x) = cost x := by
  simp [cost, opticalGauge, Complex.norm_exp, Complex.mul_re]

theorem cost_qubitGauge (θ : ℝ) (x : State) : cost (qubitGauge θ x) = cost x := by
  simp [cost, qubitGauge, Complex.norm_exp,
    Complex.mul_re, Complex.mul_im]

theorem zObs_opticalGauge (θ : ℝ) (x : State) : zObs (opticalGauge θ x) = zObs x := by
  have he : conj (Complex.exp (-(θ : ℂ) * Complex.I)) *
      Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [zObs, opticalGauge, g1_mkState, r1_mkState, g2_mkState,
    r2_mkState, map_mul]
  linear_combination (Complex.ofReal (Real.sqrt 2) * conj (r2 x) * g1 x * r1 x) * he

theorem zObs_qubitGauge (θ : ℝ) (x : State) : zObs (qubitGauge θ x) = zObs x := by
  have he : conj (Complex.exp (2 * (θ : ℂ) * Complex.I)) *
      Complex.exp ((θ : ℂ) * Complex.I) ^ 2 = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    exact Complex.exp_zero
  change zObs (sectorPhase (Complex.exp ((θ : ℂ) * Complex.I))
    (Complex.exp (2 * (θ : ℂ) * Complex.I)) x) = _
  rw [zObs_sectorPhase, he, one_mul]

/-- Characterize the initial exposure fibre without asserting that all of `J`
is invariant: its last eight coordinates transform away from zero cost. -/
theorem Jmap_eq_y0_iff (x : State) :
    Jmap x = y0 ↔ cost x = 0 ∧ zObs x = 1 := by
  constructor
  · intro h
    have hc := congrFun h (Fin.succ (Fin.succ 0))
    have hr := congrFun h 0
    have hi := congrFun h (Fin.succ 0)
    simp only [Jmap, y0, Fin.cons_succ, Fin.cons_zero, Pi.zero_apply] at hc hr hi
    refine ⟨(pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hc, ?_⟩
    exact Complex.ext hr hi
  · rintro ⟨hc, hz⟩
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
    all_goals simp only [Jmap, y0, Fin.cons_succ, Fin.cons_zero,
      Pi.zero_apply, hc, hz]
    all_goals norm_num

/-- Every generator preserves the initial exposure fibre, so any finite
composition does too. This is the objective-preservation premise for averaging
polynomials in `J`, not a claim about arbitrary state polynomials. -/
theorem generators_preserve_initial_fibre {x : State} (hx : Jmap x = y0) (θ α : ℝ) :
    Jmap (opticalGauge θ x) = y0 ∧ Jmap (qubitGauge α x) = y0 ∧
      Jmap (reflection x) = y0 := by
  obtain ⟨hc, hz⟩ := (Jmap_eq_y0_iff x).mp hx
  refine ⟨(Jmap_eq_y0_iff _).mpr ?_, (Jmap_eq_y0_iff _).mpr ?_,
    (Jmap_eq_y0_iff _).mpr ?_⟩
  · simp [cost_opticalGauge, zObs_opticalGauge, hc, hz]
  · simp [cost_qubitGauge, zObs_qubitGauge, hc, hz]
  · refine ⟨by simp [hc], ?_⟩
    simpa [zObs, reflection] using congrArg (conj : ℂ → ℂ) hz

theorem strictPolynomial_initial_fibre (P : ExposurePoly) (η α : ℝ)
    {x : State} (hx : Jmap x = y0) :
    eval x (strictPolynomial P η α) = eval x0 (strictPolynomial P η α) := by
  simp [hx, Jmap_x0]

/-! ## Reflection normalizes both rotation actions -/

theorem reflection_opticalGauge (θ : ℝ) (x : State) :
    reflection (opticalGauge θ x) = opticalGauge (-θ) (reflection x) := by
  apply state_ext <;>
    simp [reflection, opticalGauge, ← Complex.exp_conj, mul_neg]

theorem reflection_qubitGauge (θ : ℝ) (x : State) :
    reflection (qubitGauge θ x) = qubitGauge (-θ) (reflection x) := by
  apply state_ext <;>
    simp [reflection, qubitGauge, ← Complex.exp_conj, mul_neg, map_ofNat]

/-- Once the continuous rotations have been averaged, reflection averaging
completes `G`-invariance without destroying either rotation invariance. -/
theorem reflectionAverage_isGInvariant {W : StatePoly}
    (hOpt : ∀ x θ, eval (opticalGauge θ x) W = eval x W)
    (hQubit : ∀ x θ, eval (qubitGauge θ x) W = eval x W) :
    IsGInvariant (fun x => eval x (reflectionAverage W)) := by
  intro x θ α
  refine ⟨?_, ?_, reflectionAverage_invariant W x⟩
  · simp [reflection_opticalGauge, hOpt]
  · simp [reflection_qubitGauge, hQubit]

/-! ## Preserve the polynomial-in-`J` representation -/

/-- Reflection in exposure coordinates: conjugate `z`, leave `c²` fixed,
and conjugate the eight amplitude coordinates. -/
def exposureReflectionSign : Fin 11 → ℝ :=
  Fin.cons 1 (Fin.cons (-1) (Fin.cons 1 reflectionSign))

def exposureReflection (y : Fin 11 → ℝ) : Fin 11 → ℝ :=
  fun i => exposureReflectionSign i * y i

theorem zObs_reflection (x : State) : zObs (reflection x) = conj (zObs x) := by
  simp [zObs, reflection]

theorem Jmap_reflection (x : State) :
    Jmap (reflection x) = exposureReflection (Jmap x) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  all_goals simp only [Jmap, exposureReflection, exposureReflectionSign,
    Fin.cons_succ, Fin.cons_zero]
  all_goals simp [cost_reflection,
    zObs_reflection, reflection_apply, mul_left_comm]

@[simp] theorem exposureReflection_yPi : exposureReflection yPi = yPi := by
  funext i
  induction i using Fin.cases with
  | zero => simp [exposureReflection, exposureReflectionSign, yPi]
  | succ i => simp [exposureReflection, yPi]

/-- Average in the eleven exposure variables, retaining a concrete polynomial. -/
def exposureReflectionAverage (P : ExposurePoly) : ExposurePoly :=
  C (1/2 : ℝ) *
    (P + aeval (fun i => C (exposureReflectionSign i) * X i) P)

theorem eval_exposureReflectionAverage (P : ExposurePoly) (y : Fin 11 → ℝ) :
    eval y (exposureReflectionAverage P) =
      (eval y P + eval (exposureReflection y) P)/2 := by
  have h : eval y (aeval (fun i => C (exposureReflectionSign i) * X i) P) =
      eval (exposureReflection y) P := by
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, aeval_X, eval_X, eval_C, hp, exposureReflection]
  simp only [exposureReflectionAverage, map_mul, map_add, eval_C, h]
  ring

/-- Reflection averaging commutes with the actual normalized construction;
this is a polynomial identity, not just equality on normalized states. -/
theorem reflectionAverage_strictPolynomial (P : ExposurePoly) (η α : ℝ) :
    reflectionAverage (strictPolynomial P η α) =
      strictPolynomial (exposureReflectionAverage P) η α := by
  apply MvPolynomial.funext
  intro x
  simp [eval_exposureReflectionAverage, Jmap_reflection]
  ring

/-- The first, reflection-only, symmetry step applied to the existing strict
candidate. Superposition remains explicit; rotations and SOS
feasibility are not asserted. -/
theorem exists_reflection_candidate_below_Cstar
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ (P : ExposurePoly) (η α : ℝ),
      0 < η ∧ 0 < α ∧ α < 1 ∧
      a < eval x0 (strictPolynomial P η α) ∧
      (∀ x, eval (reflection x) (strictPolynomial P η α) =
        eval x (strictPolynomial P η α)) ∧
      (∀ x ∈ XCZ, eval x (strictPolynomial P η α) = 0) ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
        α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α))) := by
  obtain ⟨P, η, α, hη, hα, hα1, hv, hz, hr⟩ :=
    exists_strict_candidate_below_Cstar hSuperposition a ha
  refine ⟨exposureReflectionAverage P, η, α, hη, hα, hα1, ?_⟩
  rw [← reflectionAverage_strictPolynomial]
  exact ⟨by simpa using hv, reflectionAverage_invariant _,
    fun x hx => reflectionAverage_target_zero hz hx,
    fun x hx u hu ξ => reflectionAverage_residual hr hx hu ξ⟩

end CZExposure.PolynomialSymmetry
