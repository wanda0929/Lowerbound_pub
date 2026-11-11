module

public import RequestProject.AppendixE.RotationAction

/-!
# Continuous phase averaging and full symmetry

The normalized Haar measure on the compact rotation group is constructed using
mathlib, not assumed. Coefficientwise integration produces an actual finite
polynomial. Reflection averaging then supplies all three generators of `G`.
-/

@[expose] public section
noncomputable section

namespace CZExposure.RotationAverage

open MvPolynomial MeasureTheory PolynomialIntegration PolynomialSymmetry RotationAction
open PolynomialApproximation

local instance : MeasurableSpace Rotations := borel Rotations
local instance : BorelSpace Rotations := ⟨rfl⟩

/-- Translation-invariant probability measure on the two phase circles. -/
def rotationMeasure : Measure Rotations := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure rotationMeasure := by
  constructor
  exact Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Rotations))

instance : rotationMeasure.IsMulLeftInvariant :=
  inferInstanceAs (Measure.IsMulLeftInvariant (Measure.haarMeasure _))

theorem integrable_coeff_rotatePoly (W : StatePoly) (e : Fin 8 →₀ ℕ) :
    Integrable (fun g => coeff e (rotatePoly g W)) rotationMeasure :=
  (continuous_coeff_rotatePoly W e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def rotationAverage (W : StatePoly) : StatePoly :=
  polynomialIntegral W.totalDegree rotationMeasure (fun g => rotatePoly g W)

theorem rotationAverage_degree (W : StatePoly) :
    (rotationAverage W).totalDegree ≤ W.totalDegree :=
  polynomialIntegral_degree _ _ _ (fun g => rotatePoly_degree g W)

theorem linearMap_rotationAverage (W : StatePoly) (L : StatePoly →ₗ[ℝ] ℝ) :
    L (rotationAverage W) = ∫ g, L (rotatePoly g W) ∂rotationMeasure :=
  linearMap_polynomialIntegral L (fun g => rotatePoly_degree g W) (integrable_coeff_rotatePoly W)

theorem eval_rotationAverage (W : StatePoly) (x : State) :
    eval x (rotationAverage W) = ∫ g, eval (rotate g x) W ∂rotationMeasure := by
  simpa only [AlgHom.toLinearMap_apply, aeval_eq_eval, eval_rotatePoly] using
    linearMap_rotationAverage W (aeval x).toLinearMap

theorem rotationAverage_invariant (W : StatePoly) (h : Rotations) (x : State) :
    eval (rotate h x) (rotationAverage W) = eval x (rotationAverage W) := by
  simp only [eval_rotationAverage, ← rotate_mul]
  exact integral_mul_right_eq_self (fun g => eval (rotate g x) W) h

theorem rotationAverage_optical (W : StatePoly) (θ : ℝ) (x : State) :
    eval (opticalGauge θ x) (rotationAverage W) = eval x (rotationAverage W) := by
  have h := rotationAverage_invariant W (Circle.exp θ, Circle.exp 0) x
  rw [rotate_exp] at h
  simpa [qubitGauge] using h

theorem rotationAverage_qubit (W : StatePoly) (α : ℝ) (x : State) :
    eval (qubitGauge α x) (rotationAverage W) = eval x (rotationAverage W) := by
  have h := rotationAverage_invariant W (Circle.exp 0, Circle.exp α) x
  rw [rotate_exp] at h
  simpa [opticalGauge] using h

theorem rotationAverage_initial {W : StatePoly}
    (hW : ∀ x, Jmap x = y0 → eval x W = eval x0 W) :
    eval x0 (rotationAverage W) = eval x0 W := by
  rw [eval_rotationAverage]
  simp_rw [hW _ (rotate_initial_fibre _ Jmap_x0)]
  simp

theorem rotationAverage_target_zero {W : StatePoly}
    (hW : ∀ x ∈ XCZ, eval x W = 0) {x : State} (hx : x ∈ XCZ) :
    eval x (rotationAverage W) = 0 := by
  rw [eval_rotationAverage]
  simp_rw [hW _ (rotate_mem_XCZ _ hx)]
  simp

/-- The physical directional derivative is linear in the polynomial. -/
def driftLM (x : State) (u : ℂ) : StatePoly →ₗ[ℝ] ℝ :=
  ∑ i : Fin 8, (vf x u i) • ((aeval x).toLinearMap.comp (pderiv i).toLinearMap)

theorem driftLM_apply (x : State) (u : ℂ) (W : StatePoly) (ξ : ℝ) :
    driftLM x u W = eval (pt ξ x u) (lieDeriv W) := by
  simp [driftLM, eval_pt_lieDeriv, mul_comm]

theorem rotationAverage_residual {W : StatePoly} {α : ℝ}
    (hW : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv W))
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) (ξ : ℝ) :
    α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (rotationAverage W)) := by
  have hi := integrable_linearMap (driftLM x u)
    (fun g => rotatePoly_degree g W) (integrable_coeff_rotatePoly W)
  have hbound : ∀ g : Rotations, α * cost x - cost x ≤ driftLM x u (rotatePoly g W) := by
    intro g
    have h := hW _ (rotate_mem_Xset g hx) ((g.1 : ℂ)*u) (by simpa using hu) ξ
    simp only [map_add, eval_pt_cpoly, cost_rotate] at h
    rw [driftLM_apply x u _ ξ, rotatePoly_drift]
    linarith
  have h := integral_mono (integrable_const (α * cost x - cost x)) hi hbound
  simp only [integral_const, probReal_univ, one_smul] at h
  rw [map_add, eval_pt_cpoly, ← driftLM_apply x u _ ξ, linearMap_rotationAverage]
  linarith

/-- The last eight exposure coordinates transform by the state rotation. -/
def exposureTail : (Fin 11 → ℝ) →ₗ[ℝ] State where
  toFun y i := y i.succ.succ.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def exposureRotate (g : Rotations) : (Fin 11 → ℝ) →ₗ[ℝ] (Fin 11 → ℝ) :=
  LinearMap.pi (Fin.cons (LinearMap.proj 0) (Fin.cons (LinearMap.proj 1)
    (Fin.cons (LinearMap.proj 2) (fun i =>
      (LinearMap.proj i).comp ((rotateCLM g).toLinearMap.comp exposureTail)))))

theorem Jmap_rotate (g : Rotations) (x : State) :
    Jmap (rotate g x) = exposureRotate g (Jmap x) := by
  have hs := (rotateCLM g).map_smul (cost x ^ 2) x
  change rotate g ((cost x ^ 2) • x) = (cost x ^ 2) • rotate g x at hs
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  · simp [Jmap, exposureRotate, zObs_rotate]
  · simp [Jmap, exposureRotate, zObs_rotate]
  · change cost (rotate g x) ^ 2 = cost x ^ 2
    rw [cost_rotate]
  · simpa [Jmap, exposureRotate, exposureTail, cost_rotate, Pi.smul_apply,
      smul_eq_mul] using (congrFun hs i).symm

theorem exposureRotate_yPi (g : Rotations) : exposureRotate g yPi = yPi := by
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  · rfl
  · rfl
  · rfl
  · change rotateCLM g 0 i = 0
    exact congrFun (rotateCLM g).map_zero i

def exposureRotatePoly (g : Rotations) (P : ExposurePoly) : ExposurePoly :=
  aeval (linearVars (exposureRotate g)) P

theorem eval_exposureRotatePoly (g : Rotations) (P : ExposurePoly) (y : Fin 11 → ℝ) :
    eval y (exposureRotatePoly g P) = eval (exposureRotate g y) P :=
  eval_aeval_linearVars _ _ _

theorem exposureRotatePoly_degree (g : Rotations) (P : ExposurePoly) :
    (exposureRotatePoly g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le P _ (linearVars_degree _)

theorem continuous_exposureRotate (y : Fin 11 → ℝ) :
    Continuous (fun g : Rotations => exposureRotate g y) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply i).comp (continuous_rotate (exposureTail y))

theorem integrable_coeff_exposureRotatePoly (P : ExposurePoly) (e : Fin 11 →₀ ℕ) :
    Integrable (fun g => coeff e (exposureRotatePoly g P)) rotationMeasure := by
  have hc : Continuous (fun g => coeff e (exposureRotatePoly g P)) := by
    apply continuous_coeff_aeval P
    intro i d
    simp only [linearVars, coeff_sum, coeff_C_mul]
    apply continuous_finset_sum
    intro j _
    exact ((continuous_apply i).comp (continuous_exposureRotate (Pi.single j 1))).mul continuous_const
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def exposureRotationAverage (P : ExposurePoly) : ExposurePoly :=
  polynomialIntegral P.totalDegree rotationMeasure (fun g => exposureRotatePoly g P)

theorem eval_exposureRotationAverage (P : ExposurePoly) (y : Fin 11 → ℝ) :
    eval y (exposureRotationAverage P) =
      ∫ g, eval (exposureRotate g y) P ∂rotationMeasure := by
  simpa only [AlgHom.toLinearMap_apply, aeval_eq_eval, eval_exposureRotatePoly] using
    linearMap_polynomialIntegral (aeval y).toLinearMap
      (fun g => exposureRotatePoly_degree g P) (integrable_coeff_exposureRotatePoly P)

theorem rotationAverage_strictPolynomial (P : ExposurePoly) (η α : ℝ) :
    rotationAverage (strictPolynomial P η α) =
      strictPolynomial (exposureRotationAverage P) η α := by
  apply MvPolynomial.funext
  intro x
  have hi : Integrable (fun g => eval (exposureRotate g (Jmap x)) P) rotationMeasure := by
    simpa only [AlgHom.toLinearMap_apply, aeval_eq_eval, eval_exposureRotatePoly] using
      integrable_linearMap (aeval (Jmap x)).toLinearMap
        (fun g => exposureRotatePoly_degree g P) (integrable_coeff_exposureRotatePoly P)
  simp only [eval_rotationAverage, eval_strictPolynomial, eval_normalizedPolynomial,
    eval_exposureRotationAverage, exposureRotate_yPi, Jmap_rotate]
  rw [integral_const_mul, integral_div, integral_sub hi (integrable_const _)]

/-- Average over continuous rotations, then the two-element reflection group. -/
def symmetryAverage (W : StatePoly) : StatePoly := reflectionAverage (rotationAverage W)

theorem symmetryAverage_isGInvariant (W : StatePoly) :
    IsGInvariant (fun x => eval x (symmetryAverage W)) :=
  reflectionAverage_isGInvariant (fun x θ => rotationAverage_optical W θ x)
    (fun x α => rotationAverage_qubit W α x)

theorem symmetryAverage_degree (W : StatePoly) :
    (symmetryAverage W).totalDegree ≤ W.totalDegree :=
  (reflectionAverage_degree _).trans (rotationAverage_degree W)

theorem symmetryAverage_initial {W : StatePoly}
    (hW : ∀ x, Jmap x = y0 → eval x W = eval x0 W) :
    eval x0 (symmetryAverage W) = eval x0 W := by
  rw [symmetryAverage, reflectionAverage_initial, rotationAverage_initial hW]

theorem symmetryAverage_target_zero {W : StatePoly}
    (hW : ∀ x ∈ XCZ, eval x W = 0) {x : State} (hx : x ∈ XCZ) :
    eval x (symmetryAverage W) = 0 :=
  reflectionAverage_target_zero (fun _ hy => rotationAverage_target_zero hW hy) hx

theorem symmetryAverage_residual {W : StatePoly} {α : ℝ}
    (hW : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv W))
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) (ξ : ℝ) :
    α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (symmetryAverage W)) :=
  reflectionAverage_residual (fun _ hy _ hv t => rotationAverage_residual hW hy hv t) hx hu ξ

theorem symmetryAverage_strictPolynomial (P : ExposurePoly) (η α : ℝ) :
    symmetryAverage (strictPolynomial P η α) =
      strictPolynomial (exposureReflectionAverage (exposureRotationAverage P)) η α := by
  rw [symmetryAverage, rotationAverage_strictPolynomial, reflectionAverage_strictPolynomial]

/-- Full symmetry averaging of the conditional strict candidate. Superposition
remains explicit; no matrix or SOS representation is asserted. -/
theorem exists_G_invariant_candidate_below_Cstar
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ (P : ExposurePoly) (η α : ℝ),
      0 < η ∧ 0 < α ∧ α < 1 ∧
      a < eval x0 (strictPolynomial P η α) ∧
      IsGInvariant (fun x => eval x (strictPolynomial P η α)) ∧
      (∀ x ∈ XCZ, eval x (strictPolynomial P η α) = 0) ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
        α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α))) := by
  obtain ⟨P, η, α, hη, hα, hα1, hv, hz, hr⟩ :=
    exists_strict_candidate_below_Cstar hSuperposition a ha
  refine ⟨exposureReflectionAverage (exposureRotationAverage P), η, α, hη, hα, hα1, ?_⟩
  rw [← symmetryAverage_strictPolynomial]
  refine ⟨?_, symmetryAverage_isGInvariant _,
    fun x hx => symmetryAverage_target_zero hz hx,
    fun x hx u hu ξ => symmetryAverage_residual hr hx hu ξ⟩
  rwa [symmetryAverage_initial (fun _ hx => strictPolynomial_initial_fibre P η α hx)]

end CZExposure.RotationAverage
