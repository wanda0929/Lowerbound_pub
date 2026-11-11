module
public import RequestProject.AppendixE.PulseWords
public import RequestProject.AppendixE.CommutatorFactorization
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Operator expansions of the actual finite physical pulse words. -/
@[expose] public section
noncomputable section
namespace CZExposure.PulseExpansion
open ControlTranslation ControlLie PulseWords

abbrev End := State →L[ℝ] State

def leftLM (p : State) : State →ₗ[ℝ] State where
  toFun x := translate x p
  map_add' x y := by
    funext i
    fin_cases i <;> simp [ControlTranslation.translate, Pi.add_apply] <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp [ControlTranslation.translate, Pi.smul_apply, smul_eq_mul] <;> ring

def left (p : State) : End := (leftLM p).toContinuousLinearMap

@[simp] theorem left_apply (p x : State) : left p x = translate x p := rfl

def leftMap : State →L[ℝ] End := LinearMap.toContinuousLinearMap {
  toFun := left
  map_add' := fun p q => by
    ext x i
    simp [left_apply, ControlTranslation.translate, Pi.add_apply]
    fin_cases i <;> simp <;> ring
  map_smul' := fun r p => by
    ext x i
    simp [left_apply, ControlTranslation.translate, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> simp <;> ring }

@[simp] theorem leftMap_apply (p : State) : leftMap p = left p := rfl

/-- Operator multiplication reverses chronological list order. -/
def op : Word → ℝ → End
  | [], _ => 1
  | l :: w, t => op w t * left (ShortPulse.orbit (phase l) (time l t))

theorem op_apply (w : Word) (t : ℝ) (x : State) : op w t x = endpoint w t x := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih => exact ih _

theorem op_zero (w : Word) : op w 0 = 1 := by
  ext x : 1
  simpa only [op_apply] using endpoint_zero w x

theorem op_append (u v : Word) (t : ℝ) : op (u ++ v) t = op v t * op u t := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, op_apply, endpoint_append]

theorem op_inv (w : Word) (t : ℝ) : op (inv w) t * op w t = 1 := by
  ext x : 1
  simpa only [ContinuousLinearMap.mul_apply, op_apply] using endpoint_inv w t x

theorem op_commutator (u v : Word) (t : ℝ) :
    op (commutator u v) t = PulseCommutator.word (op u t) (op v t)
      (op (inv u) t) (op (inv v) t) := by
  simp only [PulseWords.commutator, op_append, PulseCommutator.word, mul_assoc]

theorem orbit_analytic (u : ℂ) (t : ℝ) : AnalyticAt ℝ (ShortPulse.orbit u) t := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i <;> simp [ShortPulse.orbit] <;> fun_prop

theorem op_analytic (w : Word) (t : ℝ) : AnalyticAt ℝ (op w) t := by
  induction w with
  | nil => exact analyticAt_const
  | cons l w ih =>
    have ht : AnalyticAt ℝ (time l) t := by
      unfold time
      cases l.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact analyticAt_id
      · exact analyticAt_id.neg
    exact ih.mul ((leftMap.analyticAt _).comp ((orbit_analytic _ _).comp ht))

/-- An exact vanishing-order factorization; the coefficient is analytic
at every real parameter, and its value at zero is the leading operator. -/
def Expanded (w : Word) (k : ℕ) (B : End) : Prop :=
  ∃ C : ℝ → End, (∀ t, AnalyticAt ℝ C t) ∧ C 0 = B ∧
    ∀ t, op w t = 1 + t ^ k • C t

theorem analytic_dslope {C : ℝ → End} (hC : AnalyticAt ℝ C 0) :
    AnalyticAt ℝ (dslope C 0) 0 := by
  obtain ⟨p, hp⟩ := hC
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem analytic_dslope_all {C : ℝ → End} (hC : ∀ t, AnalyticAt ℝ C t) :
    ∀ t, AnalyticAt ℝ (dslope C 0) t := by
  intro t
  by_cases ht : t = 0
  · subst t; exact analytic_dslope (hC 0)
  · have h : AnalyticAt ℝ (fun s => s⁻¹ • (C s - C 0)) t :=
      (analyticAt_id.inv ht).smul ((hC t).sub analyticAt_const)
    apply h.congr
    filter_upwards [(dslope_eventuallyEq_slope_of_ne C ht).symm] with s hs
    simpa [slope] using hs

theorem expanded_of_deriv (w : Word) (B : End) (hB : HasDerivAt (op w) B 0) :
    Expanded w 1 B := by
  refine ⟨dslope (op w) 0, analytic_dslope_all (op_analytic w), ?_, ?_⟩
  · rw [dslope_same, hB.deriv]
  · intro t
    have h := sub_smul_dslope (op w) 0 t
    rw [sub_zero, op_zero] at h
    rw [pow_one, h]
    abel

theorem expanded_commutator {u v : Word} {a b : ℕ} {A B : End}
    (hU : Expanded u a A) (hV : Expanded v b B) :
    Expanded (commutator u v) (a + b) (B * A - A * B) := by
  obtain ⟨P, hP, hP0, hU⟩ := hU
  obtain ⟨Q, hQ, hQ0, hV⟩ := hV
  refine ⟨fun t => op (inv v) t * op (inv u) t * (Q t * P t - P t * Q t),
    ?_, ?_, ?_⟩
  · intro t
    exact ((op_analytic _ _).mul (op_analytic _ _)).mul
      (((hQ t).mul (hP t)).sub ((hP t).mul (hQ t)))
  · simp only [op_zero, one_mul, hP0, hQ0]
  · intro t
    rw [op_commutator, hU, hV]
    apply PulseCommutator.factor
    · rw [← hU]; exact op_inv u t
    · rw [← hV]; exact op_inv v t

def gx : End := leftMap (vf x0 1)
def gy : End := leftMap (vf x0 Complex.I)
def b2 : End := gy * gx - gx * gy
def b3X : End := b2 * gy - gy * b2
def b3Y : End := gx * b2 - b2 * gx
def b4 : End := b3Y * gx - gx * b3Y

theorem expanded_X : Expanded X 1 gx := by
  apply expanded_of_deriv
  have h := leftMap.hasFDerivAt.comp_hasDerivAt 0 (ShortPulse.orbit_deriv (u := 1) norm_one 0)
  simpa [op, X, phase, time, gx, Function.comp_def] using h

theorem expanded_Y : Expanded Y 1 gy := by
  apply expanded_of_deriv
  have h := leftMap.hasFDerivAt.comp_hasDerivAt 0
    (ShortPulse.orbit_deriv (u := Complex.I) Complex.norm_I 0)
  simpa [op, Y, phase, time, gy, Function.comp_def] using h

theorem expanded_W2 : Expanded W2 2 b2 :=
  expanded_commutator expanded_X expanded_Y

theorem expanded_W3X : Expanded W3X 3 b3X :=
  expanded_commutator expanded_Y expanded_W2

theorem expanded_W3Y : Expanded W3Y 3 b3Y :=
  expanded_commutator expanded_W2 expanded_X

theorem expanded_W4 : Expanded W4 4 b4 :=
  expanded_commutator expanded_X expanded_W3Y

theorem left_vf (u : ℂ) (x : State) : leftMap (vf x0 u) x = vf x u := by
  funext i
  fin_cases i <;>
    simp [leftMap_apply, left_apply, ControlTranslation.translate, vf_eq_act, x0, act] <;> ring

theorem gx_field : (fun x => gx x) = driveX := funext (left_vf 1)
theorem gy_field : (fun x => gy x) = driveY := funext (left_vf Complex.I)

theorem lie_linear (A B : End) :
    VectorField.lieBracket ℝ (fun x => A x) (fun x => B x) =
      fun x => (B * A - A * B) x := by
  rw [VectorField.lieBracket_eq]
  funext x
  rw [A.hasFDerivAt.fderiv, B.hasFDerivAt.fderiv]
  rfl

theorem b2_field : (fun x => b2 x) = bracket2 := by
  rw [bracket2, ← gx_field, ← gy_field, lie_linear]
  rfl

theorem b3X_field : (fun x => b3X x) = bracket3X := by
  rw [bracket3X, ← gy_field, ← b2_field, lie_linear]
  rfl

theorem b3Y_field : (fun x => b3Y x) = bracket3Y := by
  rw [bracket3Y, ← b2_field, ← gx_field, lie_linear]
  rfl

theorem b4_field : (fun x => b4 x) = bracket4 := by
  rw [bracket4, ← gx_field, ← b3Y_field, lie_linear]
  rfl

def orders : Fin 6 → ℕ := ![1, 1, 2, 3, 3, 4]
def leading : Fin 6 → End := ![gx, gy, b2, b3X, b3Y, b4]

theorem leading_field (i : Fin 6) (x : State) : leading i x = bracketFields i x := by
  fin_cases i <;> simp [leading, bracketFields, ← gx_field, ← gy_field,
    ← b2_field, ← b3X_field, ← b3Y_field, ← b4_field]

theorem six_expanded (i : Fin 6) : Expanded (six i) (orders i) (leading i) := by
  fin_cases i
  · exact expanded_X
  · exact expanded_Y
  · exact expanded_W2
  · exact expanded_W3X
  · exact expanded_W3Y
  · exact expanded_W4

/-- Extract a further power while retaining analytic (hence C¹) regularity.
The identity includes t = 0 and holds on both sides of zero. -/
theorem remainder {w : Word} {k : ℕ} {B : End} (h : Expanded w k B) :
    ∃ R : ℝ → End, AnalyticAt ℝ R 0 ∧
      ∀ t, op w t = 1 + t ^ k • B + t ^ (k + 1) • R t := by
  obtain ⟨C, hC, hC0, heq⟩ := h
  refine ⟨dslope C 0, analytic_dslope (hC 0), ?_⟩
  intro t
  have hs := sub_smul_dslope C 0 t
  rw [sub_zero, hC0] at hs
  have hc : C t = B + t • dslope C 0 t := by rw [hs]; abel
  rw [heq, hc, smul_add, smul_smul, pow_succ]
  abel

/-- The actual physical endpoints have the claimed bracket leading terms,
with one common operator-valued analytic remainder for all initial states. -/
theorem six_endpoint_expansion (i : Fin 6) :
    ∃ R : ℝ → End, AnalyticAt ℝ R 0 ∧ ContDiffAt ℝ 1 R 0 ∧
      ∀ t x, endpoint (six i) t x =
        x + t ^ orders i • bracketFields i x + t ^ (orders i + 1) • R t x := by
  obtain ⟨R, hR, heq⟩ := remainder (six_expanded i)
  refine ⟨R, hR, hR.contDiffAt, ?_⟩
  intro t x
  have h := congrArg (fun A : End => A x) (heq t)
  simpa only [op_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, leading_field] using h

/-- The same expansion at the terminal time of the constructed integral
trajectory. No supplied controllability or ball-box hypothesis is used. -/
theorem six_physical_expansion (i : Fin 6) :
    ∃ R : ℝ → End, AnalyticAt ℝ R 0 ∧ ContDiffAt ℝ 1 R 0 ∧
      ∀ t x (hx : x ∈ Xset),
        (run (six i) t x hx).val.path (run (six i) t x hx).val.duration =
          x + t ^ orders i • bracketFields i x + t ^ (orders i + 1) • R t x := by
  obtain ⟨R, hR, hC, heq⟩ := six_endpoint_expansion i
  refine ⟨R, hR, hC, ?_⟩
  intro t x hx
  rw [run_terminal]
  exact heq t x

end CZExposure.PulseExpansion
