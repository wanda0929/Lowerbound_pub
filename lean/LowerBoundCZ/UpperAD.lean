import LowerBoundCZ.UpperAnalytic

/-! Real forward-mode differentiation for the upper checker's amplitude program.
The interval implementation encloses these real operations; interval arithmetic
itself is outside the first-tier kernel boundary. -/
noncomputable section
namespace LowerBoundCZ.Certification.Upper.AD
open Complex

inductive Expr where
  | const : ℝ → Expr
  | var : Fin 5 → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | sin : Expr → Expr
  | cos : Expr → Expr

def Expr.eval (p : Parameters) : Expr → ℝ
  | .const r => r
  | .var i => p i
  | .add a b => a.eval p + b.eval p
  | .neg a => -a.eval p
  | .mul a b => a.eval p * b.eval p
  | .sin a => Real.sin (a.eval p)
  | .cos a => Real.cos (a.eval p)

/-- The five dual-number components, written as a continuous linear map.
Evaluation on `Pi.single j 1` extracts Python's derivative component j. -/
def Expr.diff (p : Parameters) : Expr → Parameters →L[ℝ] ℝ
  | .const _ => 0
  | .var i => ContinuousLinearMap.proj i
  | .add a b => a.diff p + b.diff p
  | .neg a => -a.diff p
  | .mul a b => b.eval p • a.diff p + a.eval p • b.diff p
  | .sin a => Real.cos (a.eval p) • a.diff p
  | .cos a => -Real.sin (a.eval p) • a.diff p

theorem Expr.hasFDerivAt (e : Expr) (p : Parameters) :
    HasFDerivAt (fun q => e.eval q) (e.diff p) p := by
  induction e with
  | const r => exact hasFDerivAt_const r p
  | var i => exact (ContinuousLinearMap.proj i : Parameters →L[ℝ] ℝ).hasFDerivAt
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb => simpa only [Expr.diff, add_comm] using ha.mul hb
  | sin a ha => exact ha.sin
  | cos a ha => exact ha.cos

/-- Division in the amplitude program has the fixed nonzero denominator 12672.
The checker's quotient rule therefore equals multiplication by its reciprocal. -/
theorem constant_quotient_rule (x dx c : ℝ) (hc : c ≠ 0) :
    (dx*c-x*0)/(c*c) = c⁻¹*dx := by field_simp; ring

abbrev CExpr := Expr × Expr
def CExpr.eval (p : Parameters) (z : CExpr) : ℂ := ⟨z.1.eval p, z.2.eval p⟩
def cconst (z : ℂ) : CExpr := (.const z.re, .const z.im)
def cadd (a b : CExpr) : CExpr := (.add a.1 b.1, .add a.2 b.2)
def cmul (a b : CExpr) : CExpr :=
  (.add (.mul a.1 b.1) (.neg (.mul a.2 b.2)),
   .add (.mul a.1 b.2) (.mul a.2 b.1))
def conj (a : CExpr) : CExpr := (a.1, .neg a.2)
def real (a : Expr) : CExpr := (a, .const 0)

@[simp] theorem eval_const (p : Parameters) (z : ℂ) : (cconst z).eval p = z := rfl
@[simp] theorem eval_add (p : Parameters) (a b : CExpr) :
    (cadd a b).eval p = a.eval p + b.eval p := rfl
@[simp] theorem eval_mul (p : Parameters) (a b : CExpr) :
    (cmul a b).eval p = a.eval p * b.eval p := by
  apply Complex.ext <;> simp [cmul, CExpr.eval, Expr.eval, sub_eq_add_neg]
@[simp] theorem eval_conj (p : Parameters) (a : CExpr) :
    (conj a).eval p = star (a.eval p) := rfl
@[simp] theorem eval_real (p : Parameters) (a : Expr) :
    (real a).eval p = (a.eval p : ℂ) := rfl

abbrev Record := CExpr × CExpr
def step (k : ℕ) (dt ph : Expr) (z : Record) : Record :=
  let angle := Expr.mul dt (.const (Real.sqrt k / 2))
  let u : CExpr := (.cos ph, .sin ph)
  (cadd (cmul z.1 (real (.cos angle)))
    (cmul (cmul (cmul (cconst (-I)) u) z.2) (real (.sin angle))),
   cadd (cmul z.2 (real (.cos angle)))
    (cmul (cmul (cmul (cconst (-I)) (conj u)) z.1) (real (.sin angle))))

theorem step_eval (k : ℕ) (dt ph : Expr) (z : Record) (p : Parameters)
    (a : SectorRecord) (hg : z.1.eval p = a.ground) (hr : z.2.eval p = a.rydberg) :
    (step k dt ph z).1.eval p = (segment k (dt.eval p) (ph.eval p) a).ground ∧
    (step k dt ph z).2.eval p = (segment k (dt.eval p) (ph.eval p) a).rydberg := by
  simp only [step, eval_add, eval_mul, eval_real, eval_const, eval_conj, hg, hr,
    Expr.eval]
  constructor <;> simp [segment, CExpr.eval, Expr.eval, sub_eq_add_neg, neg_mul]

def phaseExpr (fixed : Fin 12672 → ℝ) (j : Fin 12672) : Expr :=
  if j.val = 731 then .var 1 else if j.val = 6676 then .var 2 else
  if j.val = 8661 then .var 3 else if j.val = 11922 then .var 4 else .const (fixed j)

theorem phase_eval (fixed : Fin 12672 → ℝ) (j : Fin 12672) (p : Parameters) :
    (phaseExpr fixed j).eval p = phase fixed p j := by
  unfold phaseExpr phase
  split_ifs <;> rfl

def program (fixed : Fin 12672 → ℝ) (k : ℕ) : Record :=
  (List.finRange 12672).foldl
    (fun z j => step k (.mul (.var 0) (.const (1/12672))) (phaseExpr fixed j) z)
    (cconst 1, cconst 0)

theorem program_eval (fixed : Fin 12672 → ℝ) (k : ℕ) (p : Parameters) :
    (program fixed k).1.eval p = (propagate fixed p k).ground ∧
    (program fixed k).2.eval p = (propagate fixed p k).rydberg := by
  have hf (l : List (Fin 12672)) (z : Record) (a : SectorRecord)
      (hg : z.1.eval p = a.ground) (hr : z.2.eval p = a.rydberg) :
      (l.foldl (fun z j => step k (.mul (.var 0) (.const (1/12672)))
        (phaseExpr fixed j) z) z).1.eval p =
          (l.foldl (fun a j => segment k (p 0 / 12672) (phase fixed p j) a) a).ground ∧
      (l.foldl (fun z j => step k (.mul (.var 0) (.const (1/12672)))
        (phaseExpr fixed j) z) z).2.eval p =
          (l.foldl (fun a j => segment k (p 0 / 12672) (phase fixed p j) a) a).rydberg := by
    induction l generalizing z a with
    | nil => exact ⟨hg, hr⟩
    | cons j l ih =>
      have hs := step_eval k (.mul (.var 0) (.const (1/12672))) (phaseExpr fixed j) z p a hg hr
      simp only [Expr.eval, phase_eval, mul_one_div] at hs
      exact ih _ _ hs.1 hs.2
  exact hf _ _ _ rfl rfl

def terminal (fixed : Fin 12672 → ℝ) : Fin 5 → Expr :=
  let a := program fixed 1
  let b := program fixed 2
  ![a.2.1, a.2.2, b.2.1, b.2.2, (cmul b.1 (conj (cmul a.1 a.1))).2]

theorem terminal_eval (fixed : Fin 12672 → ℝ) (p : Parameters) :
    (fun i => (terminal fixed i).eval p) = residual fixed p := by
  have ha := program_eval fixed 1 p
  have hb := program_eval fixed 2 p
  have hcross : (cmul (program fixed 2).1
      (conj (cmul (program fixed 1).1 (program fixed 1).1))).eval p =
      (propagate fixed p 2).ground * star
        ((propagate fixed p 1).ground * (propagate fixed p 1).ground) := by
    rw [eval_mul, eval_conj, eval_mul, ha.1, hb.1]
  ext i
  fin_cases i
  all_goals dsimp only [terminal, residual, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · have h := congrArg Complex.re ha.2
    dsimp only [CExpr.eval] at h
    exact h
  · have h := congrArg Complex.im ha.2
    dsimp only [CExpr.eval] at h
    exact h
  · have h := congrArg Complex.re hb.2
    dsimp only [CExpr.eval] at h
    exact h
  · have h := congrArg Complex.im hb.2
    dsimp only [CExpr.eval] at h
    exact h
  · exact congrArg Complex.im hcross

/-- Forward-mode Jacobian of the finite checker program, not an assumed derivative. -/
def jacobian (fixed : Fin 12672 → ℝ) (p : Parameters) : LinearMap :=
  ContinuousLinearMap.pi (fun i => (terminal fixed i).diff p)

theorem jacobian_eq_fderiv (fixed : Fin 12672 → ℝ) (p : Parameters) :
    jacobian fixed p = fderiv ℝ (residual fixed) p := by
  have h := hasFDerivAt_pi.mpr (fun i => (terminal fixed i).hasFDerivAt p)
  have he : (fun q i => (terminal fixed i).eval q) = residual fixed :=
    funext (terminal_eval fixed)
  rw [he] at h
  exact h.fderiv.symm

/-- First-tier numerical input: intervals enclose the explicit forward-mode
program, not an assumed root, pulse, or derivative correspondence. -/
structure Enclosures (a : Payload) : Prop extends NumericalBounds a where
  jacobian_enclosure : ∀ p ∈ Metric.closedBall a.center a.radius,
    jacobian a.fixed p ∈ a.jacobians

theorem Enclosures.analyticChecks {a : Payload} (h : Enclosures a) : Checks a where
  toNumericalBounds := h.toNumericalBounds
  jacobian_enclosure := fun p hp => by
    rw [← jacobian_eq_fderiv]
    exact h.jacobian_enclosure p hp

end LowerBoundCZ.Certification.Upper.AD
