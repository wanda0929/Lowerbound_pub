module
public import RequestProject.AppendixE.ExposureCoords

/-!
# Regularity of the exposure field `B` (Appendix E 2)

Uniform estimate `‖B(J(x), u)‖ ≤ K √c(x)`, joint continuity of `B` on `Y × U`, and
boundedness of `B` there. The estimate is proved by differentiating `J` along the vector
field `f_u`: the progress coordinates are cubic in the Rydberg amplitudes, and the
remaining coordinates contain a factor `c²`, so `c(x) B(J(x), u) = DJ(x) f_u(x)` is
`O(c(x)^{3/2})` uniformly on `X × U`.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

namespace CZExposure

open MvPolynomial MeasureTheory Set ComplexConjugate Complex Filter Topology

/-! ### Basic bounds on `X × U` -/

theorem norm_g1_le_one {x : State} (hx : x ∈ Xset) : ‖g1 x‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  rw [one_pow]
  nlinarith [hx.1, sq_nonneg (‖r1 x‖)]

theorem norm_r1_le_one {x : State} (hx : x ∈ Xset) : ‖r1 x‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  rw [one_pow]
  nlinarith [hx.1, sq_nonneg (‖g1 x‖)]

theorem norm_g2_le_one {x : State} (hx : x ∈ Xset) : ‖g2 x‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  rw [one_pow]
  nlinarith [hx.2, sq_nonneg (‖r2 x‖)]

theorem norm_r2_le_one {x : State} (hx : x ∈ Xset) : ‖r2 x‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  rw [one_pow]
  nlinarith [hx.2, sq_nonneg (‖g2 x‖)]

theorem cost_le_one {x : State} (hx : x ∈ Xset) : cost x ≤ 1 := by
  rw [cost]
  nlinarith [hx.1, hx.2, sq_nonneg (‖g1 x‖), sq_nonneg (‖g2 x‖)]

/-- Squared bound for the four real Rydberg coordinates in terms of `cost`. -/
theorem rcoord_sq_le (x : State) :
    x 2 ^ 2 ≤ 2 * cost x ∧ x 3 ^ 2 ≤ 2 * cost x ∧
      x 6 ^ 2 ≤ 4 * cost x ∧ x 7 ^ 2 ≤ 4 * cost x := by
  rw [cost_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg (x 2), sq_nonneg (x 3), sq_nonneg (x 6), sq_nonneg (x 7)]

/-- Each real Rydberg coordinate `x₂, x₃, x₆, x₇` is bounded by `2√c`. -/
theorem abs_rydberg_coord_le (x : State) {i : Fin 8}
    (hi : i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7) : |x i| ≤ 2 * Real.sqrt (cost x) := by
  have hs := rcoord_sq_le x
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (cost_nonneg x)]
  rcases hi with rfl | rfl | rfl | rfl <;>
    nlinarith [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, cost_nonneg x]

/-- `‖r₁‖² ≤ 2c`. -/
theorem r1_norm_sq_le (x : State) : ‖r1 x‖ ^ 2 ≤ 2 * cost x := by
  simp only [cost, Complex.sq_norm]
  nlinarith [Complex.normSq_nonneg (r2 x)]

/-- `‖r₂‖ ≤ 2√c`. -/
theorem r2_norm_le_sqrt (x : State) : ‖r2 x‖ ≤ 2 * Real.sqrt (cost x) := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (cost_nonneg x)]
  simp only [cost, Complex.sq_norm]
  nlinarith [Complex.normSq_nonneg (r1 x)]

theorem sqrt_two_le : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Each complex vector-field entry has norm at most `1` on `X × U`. -/
theorem norm_fC_le {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) (j : Fin 4) :
    ‖fC x u j‖ ≤ 1 := by
  have h1 := norm_g1_le_one hx
  have h2 := norm_r1_le_one hx
  have h3 := norm_g2_le_one hx
  have h4 := norm_r2_le_one hx
  have hrt := sqrt_two_le
  fin_cases j
  · show ‖-(I / 2) * (u * r1 x)‖ ≤ 1
    rw [show ‖-(I / 2) * (u * r1 x)‖ = 2⁻¹ * (‖u‖ * ‖r1 x‖) by simp]
    have hp : ‖u‖ * ‖r1 x‖ ≤ 1 * 1 := mul_le_mul hu h2 (norm_nonneg _) (by norm_num)
    linarith
  · show ‖-(I / 2) * (conj u * g1 x)‖ ≤ 1
    rw [show ‖-(I / 2) * (conj u * g1 x)‖ = 2⁻¹ * (‖u‖ * ‖g1 x‖) by simp]
    have hp : ‖u‖ * ‖g1 x‖ ≤ 1 * 1 := mul_le_mul hu h1 (norm_nonneg _) (by norm_num)
    linarith
  · show ‖-(I / 2) * (↑(Real.sqrt 2) * u * r2 x)‖ ≤ 1
    rw [show ‖-(I / 2) * (↑(Real.sqrt 2) * u * r2 x)‖ = 2⁻¹ * (√2 * ‖u‖ * ‖r2 x‖) by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]]
    have hA : √2 * ‖u‖ ≤ 2 := by
      simpa using mul_le_mul hrt hu (norm_nonneg _) (by norm_num)
    have hB : (√2 * ‖u‖) * ‖r2 x‖ ≤ 2 := by
      simpa using mul_le_mul hA h4 (norm_nonneg _) (by norm_num)
    linarith
  · show ‖-(I / 2) * (↑(Real.sqrt 2) * conj u * g2 x)‖ ≤ 1
    rw [show ‖-(I / 2) * (↑(Real.sqrt 2) * conj u * g2 x)‖ =
        2⁻¹ * (√2 * ‖u‖ * ‖g2 x‖) by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]]
    have hA : √2 * ‖u‖ ≤ 2 := by
      simpa using mul_le_mul hrt hu (norm_nonneg _) (by norm_num)
    have hB : (√2 * ‖u‖) * ‖g2 x‖ ≤ 2 := by
      simpa using mul_le_mul hA h3 (norm_nonneg _) (by norm_num)
    linarith

/-- Each real vector-field coordinate has absolute value at most `1` on `X × U`. -/
theorem abs_vf_le_one {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) (i : Fin 8) :
    |vf x u i| ≤ 1 := by
  have h := norm_fC_le hx hu
  fin_cases i <;>
    first
      | exact (Complex.abs_re_le_norm _).trans (h _)
      | exact (Complex.abs_im_le_norm _).trans (h _)

/-! ### Directional derivatives of `cost` and `z` -/

/-- `zObs` is smooth as a real function into `ℂ`. -/
theorem contDiff_zObs : ContDiff ℝ ⊤ zObs := by
  have hz : zObs = fun x =>
      ((x 4 : ℂ) - (x 5 : ℂ) * I) * ((x 0 : ℂ) + (x 1 : ℂ) * I) ^ 2 +
        (Real.sqrt 2 : ℂ) * ((x 6 : ℂ) - (x 7 : ℂ) * I) *
          ((x 0 : ℂ) + (x 1 : ℂ) * I) * ((x 2 : ℂ) + (x 3 : ℂ) * I) := by
    funext x
    have hg1 : g1 x = (x 0 : ℂ) + (x 1 : ℂ) * I := by
      refine Complex.ext ?_ ?_ <;> simp [g1]
    have hr1 : r1 x = (x 2 : ℂ) + (x 3 : ℂ) * I := by
      refine Complex.ext ?_ ?_ <;> simp [r1]
    have hcr2 : conj (r2 x) = (x 6 : ℂ) - (x 7 : ℂ) * I := by
      refine Complex.ext ?_ ?_ <;> simp [r2]
    have hcg2 : conj (g2 x) = (x 4 : ℂ) - (x 5 : ℂ) * I := by
      refine Complex.ext ?_ ?_ <;> simp [g2]
    rw [zObs, hg1, hr1, hcr2, hcg2]
  rw [hz]
  simp only [← Complex.ofRealCLM_apply]
  fun_prop

/-- The curve `t ↦ x + t • v` has derivative `v` at `0`. -/
theorem hasDerivAt_add_smul (x v : State) :
    HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x

theorem hasDerivAt_sq_add_mul (a b : ℝ) :
    HasDerivAt (fun t : ℝ => (a + b * t) ^ 2) (2 * a * b) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => a + b * t) b 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul b).const_add a
  simpa using hlin.pow 2

/-- The directional derivative of `cost` along `v`. -/
theorem fderiv_cost_apply (x v : State) :
    fderiv ℝ cost x v = x 2 * v 2 + x 3 * v 3 + (x 6 * v 6 + x 7 * v 7) / 2 := by
  have hF : HasFDerivAt cost (fderiv ℝ cost x) (x + (0 : ℝ) • v) := by
    simpa using (contDiff_cost.differentiable (by simp) x).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => cost (x + t • v)) (fderiv ℝ cost x v) 0 := by
    exact hF.comp_hasDerivAt (0 : ℝ) (hasDerivAt_add_smul x v)
  have h2 : HasDerivAt (fun t : ℝ => cost (x + t • v))
      ((2 * (2 * x 2 * v 2 + 2 * x 3 * v 3) + (2 * x 6 * v 6 + 2 * x 7 * v 7)) / 4) 0 := by
    have e : (fun t : ℝ => cost (x + t • v)) = fun t =>
        (2 * ((x 2 + v 2 * t) ^ 2 + (x 3 + v 3 * t) ^ 2) +
          ((x 6 + v 6 * t) ^ 2 + (x 7 + v 7 * t) ^ 2)) / 4 := by
      funext t
      simp only [cost_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    refine (HasDerivAt.add ?_ ?_).div_const 4
    · exact ((hasDerivAt_sq_add_mul _ _).add (hasDerivAt_sq_add_mul _ _)).const_mul 2
    · exact (hasDerivAt_sq_add_mul _ _).add (hasDerivAt_sq_add_mul _ _)
  have hq := h1.unique h2
  rw [hq]
  ring

/-- Conjugation along a real curve has derivative the conjugate derivative. -/
theorem hasDerivAt_conj_comp {w : ℝ → ℂ} {w' : ℂ} (hw : HasDerivAt w w' 0) :
    HasDerivAt (fun t : ℝ => conj (w t)) (conj w') 0 := by
  have h := ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := w 0)).comp_hasDerivAt (0 : ℝ) hw
  simpa [Function.comp_def, Complex.conjCLE_apply] using h

/-- Real part along a real curve has derivative the real part of the derivative. -/
theorem hasDerivAt_re_comp {w : ℝ → ℂ} {w' : ℂ} (hw : HasDerivAt w w' 0) :
    HasDerivAt (fun t : ℝ => (w t).re) w'.re 0 := by
  have h := (Complex.reCLM.hasFDerivAt (x := w 0)).comp_hasDerivAt (0 : ℝ) hw
  simpa [Function.comp_def, Complex.reCLM_apply] using h

/-- Imaginary part along a real curve has derivative the imaginary part of the derivative. -/
theorem hasDerivAt_im_comp {w : ℝ → ℂ} {w' : ℂ} (hw : HasDerivAt w w' 0) :
    HasDerivAt (fun t : ℝ => (w t).im) w'.im 0 := by
  have h := (Complex.imCLM.hasFDerivAt (x := w 0)).comp_hasDerivAt (0 : ℝ) hw
  simpa [Function.comp_def, Complex.imCLM_apply] using h

/-- The directional derivative of `z` along `f_u(x)`: the `g₂` terms cancel and only
`-(i√2/2) · r̄₂ · u · r₁²` survives. -/
theorem fderiv_zObs_vf (x : State) (u : ℂ) :
    fderiv ℝ zObs x (vf x u) =
      -(Complex.I * (Real.sqrt 2 : ℂ) / 2) * conj (r2 x) * u * (r1 x) ^ 2 := by
  set v := vf x u with hvdef
  have hg1 : HasDerivAt (fun t : ℝ => g1 (x + t • v)) (fC x u 0) 0 := by
    have e : (fun t : ℝ => g1 (x + t • v)) = fun t => g1 x + t • (fC x u 0) := by
      funext t
      refine Complex.ext ?_ ?_ <;> simp [g1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.smul_re,
        Complex.smul_im, hvdef, vf]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fC x u 0)).const_add (g1 x)
  have hr1 : HasDerivAt (fun t : ℝ => r1 (x + t • v)) (fC x u 1) 0 := by
    have e : (fun t : ℝ => r1 (x + t • v)) = fun t => r1 x + t • (fC x u 1) := by
      funext t
      refine Complex.ext ?_ ?_ <;> simp [r1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.smul_re,
        Complex.smul_im, hvdef, vf]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fC x u 1)).const_add (r1 x)
  have hg2 : HasDerivAt (fun t : ℝ => g2 (x + t • v)) (fC x u 2) 0 := by
    have e : (fun t : ℝ => g2 (x + t • v)) = fun t => g2 x + t • (fC x u 2) := by
      funext t
      refine Complex.ext ?_ ?_ <;> simp [g2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.smul_re,
        Complex.smul_im, hvdef, vf]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fC x u 2)).const_add (g2 x)
  have hr2 : HasDerivAt (fun t : ℝ => r2 (x + t • v)) (fC x u 3) 0 := by
    have e : (fun t : ℝ => r2 (x + t • v)) = fun t => r2 x + t • (fC x u 3) := by
      funext t
      refine Complex.ext ?_ ?_ <;> simp [r2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.smul_re,
        Complex.smul_im, hvdef, vf]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fC x u 3)).const_add (r2 x)
  have hF : HasFDerivAt zObs (fderiv ℝ zObs x) (x + (0 : ℝ) • v) := by
    simpa using (contDiff_zObs.differentiable (by simp) x).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => zObs (x + t • v)) (fderiv ℝ zObs x v) 0 := by
    exact hF.comp_hasDerivAt (0 : ℝ) (hasDerivAt_add_smul x v)
  have hcg2 := hasDerivAt_conj_comp hg2
  have hcr2 := (hasDerivAt_conj_comp hr2).const_mul (↑(Real.sqrt 2) : ℂ)
  have hD := (hcg2.mul (hg1.mul hg1)).add ((hcr2.mul hg1).mul hr1)
  have hD' : HasDerivAt (fun t : ℝ => zObs (x + t • v))
      (conj (fC x u 2) * (g1 x * g1 x) +
          conj (g2 x) * (fC x u 0 * g1 x + g1 x * fC x u 0) +
        (((Real.sqrt 2 : ℂ) * conj (fC x u 3)) * g1 x +
            ((Real.sqrt 2 : ℂ) * conj (r2 x)) * fC x u 0) * r1 x +
          ((Real.sqrt 2 : ℂ) * conj (r2 x)) * g1 x * fC x u 1) 0 := by
    convert hD using 1
    · funext t
      simp only [zObs, pow_two, Pi.mul_apply, Pi.add_apply]
    · simp only [Pi.mul_apply, zero_smul, add_zero]
      abel
  have hq := h1.unique hD'
  rw [hq]
  simp only [fC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zero_smul, add_zero]
  simp only [map_neg, map_mul, map_pow, map_div₀, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, starRingEnd_self_apply]
  ring_nf
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    map_ofNat]
  push_cast
  ring_nf

/-- Derivative bound for `cost` along `vf`: `|Dc| ≤ 6√c`. -/
theorem abs_fderiv_cost_vf_le {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |fderiv ℝ cost x (vf x u)| ≤ 6 * Real.sqrt (cost x) := by
  rw [fderiv_cost_apply]
  have h0 : 0 ≤ cost x := cost_nonneg x
  have hs0 : 0 ≤ Real.sqrt (cost x) := Real.sqrt_nonneg _
  have hv := abs_vf_le_one hx hu
  have h2 := abs_rydberg_coord_le x (i := 2) (Or.inl rfl)
  have h3 := abs_rydberg_coord_le x (i := 3) (Or.inr (Or.inl rfl))
  have h6 := abs_rydberg_coord_le x (i := 6) (Or.inr (Or.inr (Or.inl rfl)))
  have h7 := abs_rydberg_coord_le x (i := 7) (Or.inr (Or.inr (Or.inr rfl)))
  have t1 := abs_add_le (x 2 * vf x u 2 + x 3 * vf x u 3)
    ((x 6 * vf x u 6 + x 7 * vf x u 7) / 2)
  have t2 := abs_add_le (x 2 * vf x u 2) (x 3 * vf x u 3)
  have t3 := abs_add_le (x 6 * vf x u 6) (x 7 * vf x u 7)
  have d1 : |(x 6 * vf x u 6 + x 7 * vf x u 7) / 2| =
      |x 6 * vf x u 6 + x 7 * vf x u 7| / 2 := by
    rw [abs_div, abs_two]
  have h2s : (0:ℝ) ≤ 2 * Real.sqrt (cost x) := by nlinarith [hs0]
  have m2 : |x 2| * |vf x u 2| ≤ 2 * Real.sqrt (cost x) := by
    nlinarith [mul_le_mul h2 (hv 2) (abs_nonneg _) h2s]
  have m3 : |x 3| * |vf x u 3| ≤ 2 * Real.sqrt (cost x) := by
    nlinarith [mul_le_mul h3 (hv 3) (abs_nonneg _) h2s]
  have m6 : |x 6| * |vf x u 6| ≤ 2 * Real.sqrt (cost x) := by
    nlinarith [mul_le_mul h6 (hv 6) (abs_nonneg _) h2s]
  have m7 : |x 7| * |vf x u 7| ≤ 2 * Real.sqrt (cost x) := by
    nlinarith [mul_le_mul h7 (hv 7) (abs_nonneg _) h2s]
  have am2 := abs_mul (x 2) (vf x u 2)
  have am3 := abs_mul (x 3) (vf x u 3)
  have am6 := abs_mul (x 6) (vf x u 6)
  have am7 := abs_mul (x 7) (vf x u 7)
  nlinarith [t1, t2, t3, d1, m2, m3, m6, m7, am2, am3, am6, am7,
    abs_nonneg (x 6 * vf x u 6 + x 7 * vf x u 7)]

/-- Norm bound for the `zObs` derivative along `vf`: `‖Dz‖ ≤ 4c√c`. -/
theorem norm_fderiv_zObs_vf_le {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖fderiv ℝ zObs x (vf x u)‖ ≤ 4 * cost x * Real.sqrt (cost x) := by
  rw [fderiv_zObs_vf]
  have hcoef : ‖-(Complex.I * (Real.sqrt 2 : ℂ) / 2)‖ = Real.sqrt 2 / 2 := by
    rw [norm_neg, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), one_mul]
    norm_num
  have hle1 : Real.sqrt 2 / 2 ≤ 1 := by
    nlinarith [sqrt_two_le, Real.sqrt_nonneg 2]
  have h0 : 0 ≤ cost x := cost_nonneg x
  have hs0 : 0 ≤ Real.sqrt (cost x) := Real.sqrt_nonneg _
  have hr1 := r1_norm_sq_le x
  have hr2 := r2_norm_le_sqrt x
  calc ‖-(Complex.I * (Real.sqrt 2 : ℂ) / 2) * conj (r2 x) * u * (r1 x) ^ 2‖
      = ‖-(Complex.I * (Real.sqrt 2 : ℂ) / 2)‖ * ‖r2 x‖ * ‖u‖ * ‖r1 x‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_pow]
    _ = (Real.sqrt 2 / 2) * ‖r2 x‖ * ‖u‖ * ‖r1 x‖ ^ 2 := by rw [hcoef]
    _ ≤ 4 * cost x * Real.sqrt (cost x) := by
        have m1 : (Real.sqrt 2 / 2) * ‖r2 x‖ ≤ 1 * (2 * Real.sqrt (cost x)) :=
          mul_le_mul hle1 hr2 (norm_nonneg _) (by norm_num)
        have m2 : (Real.sqrt 2 / 2) * ‖r2 x‖ * ‖u‖ ≤ (2 * Real.sqrt (cost x)) * 1 := by
          refine (mul_le_mul m1 hu (norm_nonneg _) ?_).trans_eq (by ring)
          nlinarith
        have m3 : (Real.sqrt 2 / 2) * ‖r2 x‖ * ‖u‖ * ‖r1 x‖ ^ 2 ≤
            (2 * Real.sqrt (cost x)) * (2 * cost x) := by
          refine (mul_le_mul m2 hr1 ?_ ?_).trans_eq (by ring)
          · positivity
          · nlinarith
        nlinarith [m3]

/-- `fderiv` evaluated coordinatewise is `fderiv` of the coordinate function. -/
theorem fderiv_Jmap_apply_eq (x v : State) (i : Fin 11) :
    fderiv ℝ Jmap x v i = fderiv ℝ (fun y => Jmap y i) x v := by
  have hJ : HasFDerivAt Jmap (fderiv ℝ Jmap x) x :=
    (contDiff_Jmap.differentiable (by simp) x).hasFDerivAt
  have hc := ((ContinuousLinearMap.proj i : (Fin 11 → ℝ) →L[ℝ] ℝ).hasFDerivAt
    (x := Jmap x)).comp x hJ
  have hfd := hc.fderiv
  have e : (fun y : State => Jmap y i) =
      (ContinuousLinearMap.proj i : (Fin 11 → ℝ) →L[ℝ] ℝ) ∘ Jmap := rfl
  rw [e]
  show fderiv ℝ Jmap x v i =
    fderiv ℝ ((ContinuousLinearMap.proj i : (Fin 11 → ℝ) →L[ℝ] ℝ) ∘ Jmap) x v
  rw [hfd]
  rfl

/-- The 0-th coordinate of `fderiv Jmap` is `Re (Dz)`. -/
theorem fderiv_Jmap_zero (x v : State) :
    fderiv ℝ (fun y => Jmap y 0) x v = (fderiv ℝ zObs x v).re := by
  have e : (fun y : State => Jmap y 0) = Complex.reCLM ∘ zObs := by
    funext y
    simp only [Jmap, Fin.cons_zero, Function.comp_apply]
    rfl
  rw [e]
  have hz : HasFDerivAt zObs (fderiv ℝ zObs x) x :=
    (contDiff_zObs.differentiable (by simp) x).hasFDerivAt
  have hc := (Complex.reCLM.hasFDerivAt (x := zObs x)).comp x hz
  rw [hc.fderiv]
  rfl

/-- The 1-st coordinate of `fderiv Jmap` is `Im (Dz)`. -/
theorem fderiv_Jmap_one (x v : State) :
    fderiv ℝ (fun y => Jmap y (Fin.succ 0)) x v = (fderiv ℝ zObs x v).im := by
  have e : (fun y : State => Jmap y (Fin.succ 0)) = Complex.imCLM ∘ zObs := by
    funext y
    simp only [Jmap, Fin.cons_succ, Fin.cons_zero, Function.comp_apply]
    rfl
  rw [e]
  have hz : HasFDerivAt zObs (fderiv ℝ zObs x) x :=
    (contDiff_zObs.differentiable (by simp) x).hasFDerivAt
  have hc := (Complex.imCLM.hasFDerivAt (x := zObs x)).comp x hz
  rw [hc.fderiv]
  rfl

/-- The 2-nd coordinate of `fderiv Jmap` is `2c·Dc`. -/
theorem fderiv_Jmap_two' (x v : State) :
    fderiv ℝ (fun y => Jmap y (Fin.succ (Fin.succ 0))) x v =
      2 * cost x * fderiv ℝ cost x v := by
  have e : (fun y : State => Jmap y (Fin.succ (Fin.succ 0))) = fun y => cost y ^ 2 := by
    funext y
    simp only [Jmap, Fin.cons_succ, Fin.cons_zero]
  rw [e]
  rw [fderiv_pow 2 (contDiff_cost.differentiable (by simp) x)]
  simp [pow_one, smul_eq_mul]

/-- Tail coordinates `i+3` of `fderiv Jmap` are `c²·vᵢ + xᵢ·2c·Dc`. -/
theorem fderiv_Jmap_succ (x v : State) (i : Fin 8) :
    fderiv ℝ (fun y => Jmap y i.succ.succ.succ) x v =
      cost x ^ 2 * v i + x i * (2 * cost x * fderiv ℝ cost x v) := by
  have e : (fun y : State => Jmap y i.succ.succ.succ) =
      (fun y => cost y ^ 2) * fun y => y i := by
    funext y
    simp only [Jmap, Fin.cons_succ, Pi.mul_apply]
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun y => cost y ^ 2) x :=
    ((contDiff_cost.differentiable (by simp) x).hasFDerivAt.pow 2).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y => y i) x :=
    ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).hasFDerivAt).differentiableAt
  have hmul := (hd1.hasFDerivAt.mul hd2.hasFDerivAt).fderiv
  have hpow := fderiv_pow 2 (contDiff_cost.differentiable (by simp) x)
  rw [hmul, hpow]
  rw [show (fun y : State => y i) = ⇑(ContinuousLinearMap.proj i : State →L[ℝ] ℝ) from rfl,
    ContinuousLinearMap.fderiv]
  simp [pow_one, smul_eq_mul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]

/-- Each coordinate of `fderiv Jmap x (vf x u)` is bounded by `32·c·√c`. -/
theorem fderiv_Jmap_coord_le {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1)
    (i : Fin 11) : |fderiv ℝ Jmap x (vf x u) i| ≤ 32 * cost x * Real.sqrt (cost x) := by
  set v := vf x u
  have h0 : 0 ≤ cost x := cost_nonneg x
  have h1 : cost x ≤ 1 := cost_le_one hx
  have hs0 : 0 ≤ Real.sqrt (cost x) := Real.sqrt_nonneg _
  have hcs0 : 0 ≤ cost x * Real.sqrt (cost x) := mul_nonneg h0 hs0
  have hDc := abs_fderiv_cost_vf_le hx hu
  have hDz := norm_fderiv_zObs_vf_le hx hu
  have hv := abs_vf_le_one hx hu
  have hxi := abs_le_one_of_mem_Xset hx
  have hcsq : cost x ^ 2 ≤ cost x * Real.sqrt (cost x) := by
    have hc : cost x ≤ Real.sqrt (cost x) := by
      have hs : cost x ^ 2 ≤ cost x := by nlinarith [h0, h1]
      calc cost x = Real.sqrt (cost x ^ 2) := (Real.sqrt_sq h0).symm
        _ ≤ Real.sqrt (cost x) := Real.sqrt_le_sqrt hs
    calc cost x ^ 2 = cost x * cost x := by ring
      _ ≤ cost x * Real.sqrt (cost x) := mul_le_mul_of_nonneg_left hc h0
  rw [fderiv_Jmap_apply_eq]
  refine Fin.cases ?_ ?_ i
  · rw [fderiv_Jmap_zero]
    nlinarith [Complex.abs_re_le_norm (fderiv ℝ zObs x v), hDz, hcs0]
  · intro j
    refine Fin.cases ?_ ?_ j
    · rw [fderiv_Jmap_one]
      nlinarith [Complex.abs_im_le_norm (fderiv ℝ zObs x v), hDz, hcs0]
    · intro k
      refine Fin.cases ?_ ?_ k
      · rw [fderiv_Jmap_two']
        have e : |2 * cost x * fderiv ℝ cost x v| = 2 * cost x * |fderiv ℝ cost x v| := by
          rw [abs_mul, abs_mul, abs_two, abs_of_nonneg h0]
        rw [e]
        nlinarith [hDc, hcs0]
      · intro l
        rw [fderiv_Jmap_succ]
        have h2c : 0 ≤ 2 * cost x * |fderiv ℝ cost x v| := by positivity
        have e : |cost x ^ 2 * v l + x l * (2 * cost x * fderiv ℝ cost x v)| ≤
            cost x ^ 2 * |v l| + |x l| * (2 * cost x * |fderiv ℝ cost x v|) := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          · rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg h0]
        have h2cb : 2 * cost x * |fderiv ℝ cost x v| ≤ 12 * cost x * Real.sqrt (cost x) := by
          have := mul_le_mul_of_nonneg_left hDc (show (0:ℝ) ≤ 2 * cost x by positivity)
          nlinarith
        refine e.trans ?_
        nlinarith [hv l, hxi l, hcsq, hcs0, h2cb, h2c, sq_nonneg (cost x),
          abs_nonneg (x l), abs_nonneg (v l), mul_nonneg (sq_nonneg (cost x)) (abs_nonneg (v l))]

/-- The sup-norm bound `‖fderiv Jmap x (vf x u)‖ ≤ 32·c·√c`. -/
theorem fderiv_Jmap_bound {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖fderiv ℝ Jmap x (vf x u)‖ ≤ 32 * cost x * Real.sqrt (cost x) := by
  have hC : 0 ≤ 32 * cost x * Real.sqrt (cost x) := by
    have h0 := cost_nonneg x
    have hs := Real.sqrt_nonneg (cost x)
    positivity
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
  exact fderiv_Jmap_coord_le hx hu i

/-- The `B`-field along `J(X)` is bounded by `32√c`. -/
theorem Bfield_Jmap_bound {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖Bfield (Jmap x) u‖ ≤ 32 * Real.sqrt (cost x) := by
  rcases (cost_nonneg x).lt_or_eq with hc | hc0
  · rw [Bfield_Jmap_of_pos hc, norm_smul]
    have hw := fderiv_Jmap_bound hx hu
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg hc.le]
    nlinarith [hw, inv_mul_cancel₀ hc.ne', Real.sqrt_nonneg (cost x),
      mul_nonneg hc.le (Real.sqrt_nonneg (cost x))]
  · rw [Bfield_Jmap_of_zero hc0.symm, norm_zero]
    positivity

/-- The uniform `B`-field bound in state coordinates. -/
theorem Bfield_norm_le_sqrt_cost :
    ∃ K : ℝ, 0 < K ∧
      ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        ‖Bfield (Jmap x) u‖ ≤ K * Real.sqrt (cost x) :=
  ⟨32, by norm_num, fun x hx u hu => Bfield_Jmap_bound hx hu⟩

/-- The `B`-field bound in image coordinates: `‖B‖ ≤ 32·√√y₂`. -/
theorem Bfield_image_bound {y : Fin 11 → ℝ} (hy : y ∈ Yset) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖Bfield y u‖ ≤ 32 * Real.sqrt (Real.sqrt (y 2)) := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Jmap_two, Real.sqrt_sq (cost_nonneg x)]
  exact Bfield_Jmap_bound hx hu

/-- Global boundedness of `B` on `Y × U`. -/
theorem Bfield_bounded :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Yset, ∀ u : ℂ, ‖u‖ ≤ 1 → ‖Bfield y u‖ ≤ K := by
  refine ⟨32, by norm_num, fun y hy u hu => ?_⟩
  refine (Bfield_image_bound hy hu).trans ?_
  obtain ⟨x, hx, rfl⟩ := hy
  have h : Real.sqrt (Real.sqrt (Jmap x 2)) ≤ 1 := by
    rw [Jmap_two, Real.sqrt_sq (cost_nonneg x)]
    exact (Real.sqrt_le_sqrt (cost_le_one hx)).trans (by rw [Real.sqrt_one])
  nlinarith

/-- State recovered from a positive-cost image point: `xᵢ = yᵢ₊₃ / y₂`. -/
private def recoveredState (q : (Fin 11 → ℝ) × ℂ) : State :=
  fun i => q.1 i.succ.succ.succ / q.1 2

/-- `recoveredState` is ambient-continuous at any point with `q.1.2 ≠ 0`. -/
private theorem continuousAt_recoveredState
    {p : (Fin 11 → ℝ) × ℂ} (hp : p.1 2 ≠ 0) :
    ContinuousAt recoveredState p := by
  unfold recoveredState
  apply continuousAt_pi.2
  intro i
  exact ((continuous_apply i.succ.succ.succ).comp continuous_fst).continuousAt.div
    ((continuous_apply 2).comp continuous_fst).continuousAt hp

/-- `B` restricted to `Y × U` is jointly continuous. At the zero-cost face the bound
`‖B‖ ≤ 32·√√y₂` squeezes it to `0`; off the face the state is recovered smoothly. -/
theorem continuousOn_Bfield :
    ContinuousOn
      (fun p : (Fin 11 → ℝ) × ℂ => Bfield p.1 p.2)
      (Yset ×ˢ Metric.closedBall (0 : ℂ) 1) := by
  intro p hp
  obtain ⟨x, hx, hJ⟩ := hp.1
  have hu' : ‖p.2‖ ≤ 1 := mem_closedBall_zero_iff.mp hp.2
  have hp2 : p.1 2 = cost x ^ 2 := by rw [← hJ]; rfl
  have hcostx : cost x ≥ 0 := cost_nonneg x
  rcases hcostx.lt_or_eq with hc | hc0
  · -- positive-cost point: `B` coincides eventually with a continuous expression
    have hp2pos : 0 < p.1 2 := by rw [hp2]; exact sq_pos_of_pos hc
    have hxp : recoveredState p = x := by
      funext i
      change p.1 i.succ.succ.succ / p.1 2 = x i
      rw [← hJ, Jmap_two]
      change cost x ^ 2 * x i / (cost x ^ 2) = x i
      field_simp [hc.ne']
    have hrec : ContinuousAt recoveredState p :=
      continuousAt_recoveredState hp2pos.ne'
    have hpair : ContinuousAt
        (fun q : (Fin 11 → ℝ) × ℂ => (recoveredState q, q.2)) p :=
      ContinuousAt.prodMk hrec continuous_snd.continuousAt
    have hcostw : ContinuousAt
        (fun q : (Fin 11 → ℝ) × ℂ => cost (recoveredState q)) p :=
      contDiff_cost.continuous.continuousAt.comp hrec
    have hcostne : cost (recoveredState p) ≠ 0 := by rw [hxp]; exact hc.ne'
    have hinv := hcostw.inv₀ hcostne
    have hfd : ContinuousAt
        (fun q : (Fin 11 → ℝ) × ℂ =>
          (fderiv ℝ Jmap (recoveredState q) : State →L[ℝ] (Fin 11 → ℝ))) p :=
      (contDiff_Jmap.continuous_fderiv (by simp)).continuousAt.comp hrec
    have hvf : ContinuousAt ((fun r : State × ℂ => vf r.1 r.2) ∘
        (fun q : (Fin 11 → ℝ) × ℂ => (recoveredState q, q.2))) p :=
      continuous_vf.continuousAt.comp hpair
    have happ : ContinuousAt
        (fun q : (Fin 11 → ℝ) × ℂ =>
          fderiv ℝ Jmap (recoveredState q)
            (((fun r : State × ℂ => vf r.1 r.2) ∘
              (fun q : (Fin 11 → ℝ) × ℂ => (recoveredState q, q.2))) q)) p :=
      ContinuousAt.clm_apply hfd hvf
    have hbranch : ContinuousAt
        (fun q : (Fin 11 → ℝ) × ℂ =>
          (cost (recoveredState q))⁻¹ •
            fderiv ℝ Jmap (recoveredState q)
              (((fun r : State × ℂ => vf r.1 r.2) ∘
                (fun q : (Fin 11 → ℝ) × ℂ => (recoveredState q, q.2))) q)) p :=
      ContinuousAt.smul hinv happ
    have hcoord2 : Continuous (fun q : (Fin 11 → ℝ) × ℂ => q.1 2) :=
      (continuous_apply 2).comp continuous_fst
    have hev : ∀ᶠ q in 𝓝 p, 0 < q.1 2 :=
      (isOpen_lt continuous_const hcoord2).mem_nhds hp2pos
    have heq : (fun q : (Fin 11 → ℝ) × ℂ => Bfield q.1 q.2) =ᶠ[𝓝 p]
        (fun q : (Fin 11 → ℝ) × ℂ =>
          (cost (recoveredState q))⁻¹ •
            fderiv ℝ Jmap (recoveredState q)
              (((fun r : State × ℂ => vf r.1 r.2) ∘
                (fun q : (Fin 11 → ℝ) × ℂ => (recoveredState q, q.2))) q)) := by
      filter_upwards [hev] with q hq
      simp only [Bfield, if_pos hq, Function.comp_apply]
      rfl
    exact (hbranch.congr_of_eventuallyEq heq).continuousWithinAt
  · -- zero-cost point: squeeze ‖B‖ ≤ 32·√√(q.1 2) → 0
    have hp2z : p.1 2 = 0 := by rw [hp2, ← hc0]; norm_num
    have hB0 : Bfield p.1 p.2 = 0 := by
      have hnc : ¬ 0 < p.1 2 := by rw [hp2z]; exact lt_irrefl _
      calc Bfield p.1 p.2
          = (if 0 < p.1 2 then (cost (fun i : Fin 8 => p.1 (i.succ.succ.succ) / p.1 2))⁻¹ •
              fderiv ℝ Jmap (fun i : Fin 8 => p.1 (i.succ.succ.succ) / p.1 2)
                (vf (fun i : Fin 8 => p.1 (i.succ.succ.succ) / p.1 2) p.2) else 0) := rfl
        _ = 0 := if_neg hnc
    -- tendsto of the bound function to 0
    have hsqrt : Filter.Tendsto (fun q : (Fin 11 → ℝ) × ℂ => Real.sqrt (Real.sqrt (q.1 2)))
        (𝓝[Yset ×ˢ Metric.closedBall (0 : ℂ) 1] p) (𝓝 (Real.sqrt (Real.sqrt (p.1 2)))) :=
      (Real.continuous_sqrt.continuousWithinAt).comp
        ((Real.continuous_sqrt.continuousWithinAt).comp
          (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 11 => ℝ)
              2).continuous.continuousWithinAt).comp
            continuous_fst.continuousWithinAt (Set.mapsTo_univ _ _))
          (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    have h32 : Filter.Tendsto (fun q : (Fin 11 → ℝ) × ℂ =>
        32 * Real.sqrt (Real.sqrt (q.1 2)))
        (𝓝[Yset ×ˢ Metric.closedBall (0 : ℂ) 1] p) (𝓝 0) := by
      have := hsqrt.const_mul 32
      rw [hp2z] at this
      simpa using this
    have hz : (fun q : (Fin 11 → ℝ) × ℂ => Bfield q.1 q.2) p = 0 := hB0
    show Filter.Tendsto (fun q : (Fin 11 → ℝ) × ℂ => Bfield q.1 q.2)
      (𝓝[Yset ×ˢ Metric.closedBall (0 : ℂ) 1] p)
      (𝓝 ((fun q : (Fin 11 → ℝ) × ℂ => Bfield q.1 q.2) p))
    rw [hz]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' ?_ ?_ h32
    · exact Filter.Eventually.of_forall fun q => norm_nonneg _
    · refine Filter.Eventually.mono self_mem_nhdsWithin fun q hq =>
        Bfield_image_bound hq.1 (mem_closedBall_zero_iff.mp hq.2)

end CZExposure
