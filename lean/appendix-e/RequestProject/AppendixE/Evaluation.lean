module
public import RequestProject.AppendixE.Algebra

/-! Evaluation of the hierarchy polynomials at points of the state–control set. -/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial ComplexConjugate

theorem eval_pt_ofState (ξ : ℝ) (x : State) (u : ℂ) (W : StatePoly) :
    eval (pt ξ x u) (ofState W) = eval x W := by
  simp only [ofState, eval_rename]; rfl

theorem eval_pt_ofCell (ξ : ℝ) (x : State) (u : ℂ) (V : CellPoly) :
    eval (pt ξ x u) (ofCell V) = evalCell ξ x V := by
  have : (pt ξ x u ∘ fun o : Option (Fin 8) => o.elim Var.xi Var.st) = fun o => o.elim ξ x := by
    funext o; cases o <;> rfl
  simp only [ofCell, eval_rename, evalCell, this]

set_option maxHeartbeats 2000000 in
theorem eval_pt_fpoly (ξ : ℝ) (x : State) (u : ℂ) (i : Fin 8) :
    eval (pt ξ x u) (fpoly i) = vf x u i := by
  fin_cases i <;> simp only [fpoly, vf, fC] <;>
    simp [pt, g1, r1, g2, r2, xs, ua, ub, Complex.mul_re, Complex.mul_im] <;> ring

theorem eval_pt_cpoly (ξ : ℝ) (x : State) (u : ℂ) : eval (pt ξ x u) cpoly = cost x := by
  simp [cpoly, cost, pt, r1, r2, xs, Complex.sq_norm, Complex.normSq_apply]; ring

theorem eval_pt_xi (ξ : ℝ) (x : State) (u : ℂ) : eval (pt ξ x u) (X Var.xi) = ξ := by
  simp [pt]

theorem eval_pt_lieDeriv (ξ : ℝ) (x : State) (u : ℂ) (W : StatePoly) :
    eval (pt ξ x u) (lieDeriv W) = ∑ i, eval x (pderiv i W) * vf x u i := by
  simp [lieDeriv, eval_pt_ofState, eval_pt_fpoly]

theorem eval_pt_cellOp (ξ : ℝ) (x : State) (u : ℂ) (κ : ℝ) (V : CellPoly) :
    eval (pt ξ x u) (cellOp κ V) = (∑ i, evalCell ξ x (pderiv (some i) V) * vf x u i) +
      κ * cost x * evalCell ξ x (pderiv none V) := by
  simp [cellOp, eval_pt_ofCell, eval_pt_fpoly, eval_pt_cpoly]

theorem eval_atXi (t : ℝ) (x : State) (V : CellPoly) : eval x (atXi t V) = evalCell t x V := by
  rw [atXi, evalCell]
  induction V using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p o hp => simp only [map_mul, aeval_X, eval_X, hp]; cases o <;> simp

theorem norm_sq_g1_add (x : State) : ‖g1 x‖ ^ 2 + ‖r1 x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  simp [g1, r1, Complex.sq_norm, Complex.normSq_apply]; ring

theorem norm_sq_g2_add (x : State) : ‖g2 x‖ ^ 2 + ‖r2 x‖ ^ 2 = x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2 := by
  simp [g2, r2, Complex.sq_norm, Complex.normSq_apply]; ring

theorem eval_eq_zero_of_mem_normIdeal {ξ : ℝ} {x : State} {u : ℂ} (hx : x ∈ Xset) (hu : ‖u‖ = 1)
    {q : Poly} (hq : q ∈ normIdeal) : eval (pt ξ x u) q = 0 := by
  have : normIdeal ≤ RingHom.ker (eval (pt ξ x u)) := by
    refine Ideal.span_le.2 ?_
    have h1 := norm_sq_g1_add x
    have h2 := norm_sq_g2_add x
    rw [hx.1] at h1; rw [hx.2] at h2
    have h3 : u.re ^ 2 + u.im ^ 2 = 1 := by
      have := congrArg (· ^ 2) hu
      simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at this
      linarith
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl <;> simp [pt, xs, ua, ub] <;> linarith
  exact this hq

theorem eval_eq_zero_of_mem_stateNormIdeal {x : State} (hx : x ∈ Xset)
    {q : StatePoly} (hq : q ∈ stateNormIdeal) : eval x q = 0 := by
  have : stateNormIdeal ≤ RingHom.ker (eval x) := by
    refine Ideal.span_le.2 ?_
    have h1 := norm_sq_g1_add x
    have h2 := norm_sq_g2_add x
    rw [hx.1] at h1; rw [hx.2] at h2
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl <;> simp <;> linarith
  exact this hq

theorem IsSOS.eval_nonneg {σ : Type*} {d : ℕ} {p : MvPolynomial σ ℝ} (h : IsSOS d p)
    (v : σ → ℝ) : 0 ≤ eval v p := by
  obtain ⟨n, f, _, rfl⟩ := h
  simp only [map_sum, map_pow]
  exact Finset.sum_nonneg fun l _ => sq_nonneg _

/-- A polynomial congruent modulo `I` to a sum of squares is nonnegative on `K`. -/
theorem eval_nonneg_of_sos_mod {ξ : ℝ} {x : State} {u : ℂ} (hx : x ∈ Xset) (hu : ‖u‖ = 1)
    {d : ℕ} {p σ : Poly} (hσ : IsSOS d σ) (hp : p - σ ∈ normIdeal) : 0 ≤ eval (pt ξ x u) p := by
  have h := eval_eq_zero_of_mem_normIdeal (ξ := ξ) hx hu hp
  rw [map_sub, sub_eq_zero] at h
  rw [h]; exact hσ.eval_nonneg _

end CZExposure
