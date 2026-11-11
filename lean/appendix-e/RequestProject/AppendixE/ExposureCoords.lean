module
public import RequestProject.AppendixE.WeakDuality

/-!
# Exposure coordinates (Appendix E 2, Step 1)

Smoothness of the map `J`, its values at `x₀` and on the CZ orbit, and the identity
`c(x) B(J(x), u) = DJ(x) f_u(x)` (which uses that `DJ(x) f_u(x)` vanishes on the zero-cost face).
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial MeasureTheory Set ComplexConjugate


theorem zObs_re (x : State) : (zObs x).re = x 4 * (x 0 ^ 2 - x 1 ^ 2) + 2 * x 5 * x 0 * x 1 +
    Real.sqrt 2 * (x 6 * (x 0 * x 2 - x 1 * x 3) + x 7 * (x 0 * x 3 + x 1 * x 2)) := by
  simp [zObs, g1, g2, r1, r2, Complex.mul_re, Complex.mul_im, pow_two]; ring

theorem zObs_im (x : State) : (zObs x).im = x 4 * (2 * x 0 * x 1) - x 5 * (x 0 ^ 2 - x 1 ^ 2) +
    Real.sqrt 2 * (x 6 * (x 0 * x 3 + x 1 * x 2) - x 7 * (x 0 * x 2 - x 1 * x 3)) := by
  simp [zObs, g1, g2, r1, r2, Complex.mul_re, Complex.mul_im, pow_two]; ring

theorem contDiff_zObs_re : ContDiff ℝ ⊤ (fun x => (zObs x).re) := by
  simp only [zObs_re]; fun_prop

theorem contDiff_cost : ContDiff ℝ ⊤ cost := by
  have : cost = fun x : State => (2 * (x 2 ^ 2 + x 3 ^ 2) + (x 6 ^ 2 + x 7 ^ 2)) / 4 := funext cost_eq
  rw [this]; fun_prop

theorem contDiff_Jmap : ContDiff ℝ ⊤ Jmap := by
  rw [contDiff_pi]
  intro k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k) k
  · simp only [Jmap, Fin.cons_zero, zObs_re]; fun_prop
  · simp only [Jmap, Fin.cons_succ, Fin.cons_zero, zObs_im]; fun_prop
  · simp only [Jmap, Fin.cons_succ, Fin.cons_zero]; exact contDiff_cost.pow 2
  · simp only [Jmap, Fin.cons_succ]; exact (contDiff_cost.pow 2).mul (contDiff_apply ℝ ℝ i)

theorem vf_eq_eval (x : State) (u : ℂ) : vf x u = fun i => eval (pt 0 x u) (fpoly i) :=
  funext fun i => (eval_pt_fpoly 0 x u i).symm

theorem continuous_pt : Continuous (fun p : State × ℂ => pt 0 p.1 p.2) := by
  refine continuous_pi fun k => ?_
  cases k with
  | st i => exact (continuous_apply i).comp continuous_fst
  | ctl i =>
    fin_cases i
    · exact Complex.continuous_re.comp continuous_snd
    · exact Complex.continuous_im.comp continuous_snd
  | xi => exact continuous_const

theorem continuous_vf : Continuous (fun p : State × ℂ => vf p.1 p.2) := by
  simp only [vf_eq_eval]
  exact continuous_pi fun i => (MvPolynomial.continuous_eval _).comp continuous_pt

theorem coords_zero_of_cost_zero {x : State} (hc : cost x = 0) :
    x 2 = 0 ∧ x 3 = 0 ∧ x 6 = 0 ∧ x 7 = 0 := by
  rw [cost_eq] at hc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x 2), sq_nonneg (x 3), sq_nonneg (x 6),
    sq_nonneg (x 7)]

theorem hasDerivAt_const_add_sq_mul (A : ℝ) {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    HasDerivAt (fun t => A + t ^ 2 * g t) 0 0 := by
  have h := ((hasDerivAt_pow 2 (0 : ℝ)).mul (hg 0).hasDerivAt).const_add A
  simpa using h

/-- On the zero-cost face, `DJ(x) f_u(x) = 0`. -/
theorem fderiv_Jmap_vf_of_cost_zero {x : State} (hc : cost x = 0) (u : ℂ) :
    fderiv ℝ Jmap x (vf x u) = 0 := by
  obtain ⟨h2, h3, h6, h7⟩ := coords_zero_of_cost_zero hc
  set v := vf x u with hvdef
  have hv : v 0 = 0 ∧ v 1 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
    simp only [hvdef, vf_eq_eval]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [fpoly, pt, xs, ua, ub, h2, h3, h6, h7]
  obtain ⟨hv0, hv1, hv4, hv5⟩ := hv
  have hJ : HasFDerivAt Jmap (fderiv ℝ Jmap x) x :=
    ((contDiff_Jmap.differentiable (by simp)) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hline : HasDerivAt (fun t : ℝ => Jmap (x + t • v)) (fderiv ℝ Jmap x v) 0 := by
    have hJ' : HasFDerivAt Jmap (fderiv ℝ Jmap x) (x + (0 : ℝ) • v) := by simpa using hJ
    exact hJ'.comp_hasDerivAt (0 : ℝ) hl
  have hcost : ∀ t : ℝ, cost (x + t • v) = t ^ 2 * cost v := by
    intro t; simp only [cost_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, h3, h6, h7]; ring
  have hzero : HasDerivAt (fun t : ℝ => Jmap (x + t • v)) 0 0 := by
    rw [hasDerivAt_pi]
    intro k
    simp only [Pi.zero_apply]
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k) k
    · have : (fun t : ℝ => Jmap (x + t • v) 0) = fun t : ℝ => (x 4 * (x 0 ^ 2 - x 1 ^ 2) + 2 * x 5 * x 0 * x 1)
          + t ^ 2 * (fun _ => Real.sqrt 2 * (v 6 * (x 0 * v 2 - x 1 * v 3) +
            v 7 * (x 0 * v 3 + x 1 * v 2))) t := by
        funext t
        simp only [Jmap, Fin.cons_zero, zObs_re, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, h3,
          h6, h7, hv0, hv1, hv4, hv5]
        ring
      rw [this]; exact hasDerivAt_const_add_sq_mul _ (differentiable_const _)
    · have : (fun t : ℝ => Jmap (x + t • v) (Fin.succ 0)) = fun t : ℝ =>
          (x 4 * (2 * x 0 * x 1) - x 5 * (x 0 ^ 2 - x 1 ^ 2))
          + t ^ 2 * (fun _ => Real.sqrt 2 * (v 6 * (x 0 * v 3 + x 1 * v 2) -
            v 7 * (x 0 * v 2 - x 1 * v 3))) t := by
        funext t
        simp only [Jmap, Fin.cons_succ, Fin.cons_zero, zObs_im, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, h2, h3, h6, h7, hv0, hv1, hv4, hv5]
        ring
      rw [this]; exact hasDerivAt_const_add_sq_mul _ (differentiable_const _)
    · have : (fun t : ℝ => Jmap (x + t • v) (Fin.succ (Fin.succ 0))) = fun t : ℝ =>
          0 + t ^ 2 * (fun t : ℝ => t ^ 2 * cost v ^ 2) t := by
        funext t
        simp only [Jmap, Fin.cons_succ, Fin.cons_zero, hcost]
        ring
      rw [this]; exact hasDerivAt_const_add_sq_mul _ (by fun_prop)
    · have : (fun t : ℝ => Jmap (x + t • v) (Fin.succ (Fin.succ (Fin.succ i)))) = fun t : ℝ =>
          0 + t ^ 2 * (fun t : ℝ => t ^ 2 * cost v ^ 2 * (x i + t * v i)) t := by
        funext t
        simp only [Jmap, Fin.cons_succ, hcost, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]; exact hasDerivAt_const_add_sq_mul _ (by fun_prop)
  exact hline.unique hzero

theorem Jmap_two (x : State) : Jmap x 2 = cost x ^ 2 := rfl

theorem Bfield_Jmap_of_pos {x : State} (hc : 0 < cost x) (u : ℂ) :
    Bfield (Jmap x) u = (cost x)⁻¹ • fderiv ℝ Jmap x (vf x u) := by
  have h2 : 0 < Jmap x 2 := by rw [Jmap_two]; positivity
  have hx : (fun i : Fin 8 => Jmap x i.succ.succ.succ / Jmap x 2) = x := by
    funext i
    simp only [Jmap_two]
    simp only [Jmap, Fin.cons_succ]
    field_simp
  simp only [Bfield, if_pos h2, hx]

theorem Bfield_Jmap_of_zero {x : State} (hc : cost x = 0) (u : ℂ) : Bfield (Jmap x) u = 0 := by
  have h2 : ¬ 0 < Jmap x 2 := by rw [Jmap_two, hc]; simp
  simp only [Bfield, if_neg h2]

/-- `c(x) B(J(x), u) = DJ(x) f_u(x)` everywhere. -/
theorem cost_smul_Bfield (x : State) (u : ℂ) :
    cost x • Bfield (Jmap x) u = fderiv ℝ Jmap x (vf x u) := by
  rcases (cost_nonneg x).lt_or_eq with hc | hc
  · rw [Bfield_Jmap_of_pos hc, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · rw [Bfield_Jmap_of_zero hc.symm, fderiv_Jmap_vf_of_cost_zero hc.symm, smul_zero]

theorem Jmap_x0 : Jmap x0 = y0 := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k) k
  · simp [Jmap, y0, zObs_re, x0]
  · simp [Jmap, y0, zObs_im, x0]
  · show cost x0 ^ 2 = 0
    simp [cost_eq, x0]
  · simp [Jmap, y0, cost_eq, x0]

theorem Jmap_of_mem_XCZ {x : State} (hx : x ∈ XCZ) : Jmap x = yPi := by
  obtain ⟨⟨h1, -⟩, hr1, hr2, hg2⟩ := hx
  have hx2 : x 2 = 0 := by have := congrArg Complex.re hr1; simpa [r1] using this
  have hx3 : x 3 = 0 := by have := congrArg Complex.im hr1; simpa [r1] using this
  have hx6 : x 6 = 0 := by have := congrArg Complex.re hr2; simpa [r2] using this
  have hx7 : x 7 = 0 := by have := congrArg Complex.im hr2; simpa [r2] using this
  have hx4 : x 4 = -(x 0 ^ 2 - x 1 ^ 2) := by
    have := congrArg Complex.re hg2; simp [g1, g2, pow_two] at this; linarith
  have hx5 : x 5 = -(2 * x 0 * x 1) := by
    have := congrArg Complex.im hg2; simp [g1, g2, pow_two] at this; linarith
  have hn : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    rw [norm_sq_g1_add, hx2, hx3] at h1; linarith
  have hc : cost x = 0 := by rw [cost_eq, hx2, hx3, hx6, hx7]; ring
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k) k
  · simp only [Jmap, yPi, Fin.cons_zero, zObs_re, hx2, hx3, hx4, hx5, hx6, hx7]
    nlinarith [hn]
  · simp only [Jmap, yPi, Fin.cons_succ, Fin.cons_zero, zObs_im, hx2, hx3, hx4, hx5, hx6, hx7]
    simp; ring
  · show cost x ^ 2 = 0
    simp [hc]
  · simp [Jmap, yPi, hc]

theorem Xset_eq : Xset = {x : State | x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 1 ∧
    x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2 = 1} := by
  ext x; simp [Xset, norm_sq_g1_add, norm_sq_g2_add]

theorem abs_le_one_of_mem_Xset {x : State} (hx : x ∈ Xset) (i : Fin 8) : |x i| ≤ 1 := by
  rw [Xset_eq] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
    sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5), sq_nonneg (x 6), sq_nonneg (x 7)]

theorem Xset_subset_closedBall : Xset ⊆ Metric.closedBall (0 : State) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i; rw [Real.norm_eq_abs]; exact abs_le_one_of_mem_Xset hx i

theorem isCompact_Xset : IsCompact Xset := by
  refine Metric.isCompact_of_isClosed_isBounded ?_
    (Metric.isBounded_closedBall.subset Xset_subset_closedBall)
  rw [Xset_eq]
  exact (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const)

theorem isCompact_Yset : IsCompact Yset :=
  isCompact_Xset.image (contDiff_Jmap.continuous)

end CZExposure
