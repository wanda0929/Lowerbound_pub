module
public import RequestProject.AppendixE.FaceProjection

/-!
# Independent sector phases

`sectorPhase a b` multiplies the two sector amplitudes by independent constant
unit complex numbers `(a, b)` — a strictly larger family than `qubitGauge`,
whose phases have a fixed `1 : 2` ratio.  With `‖a‖ = ‖b‖ = 1` the action
preserves `X`, `F`, and the running cost; `z` transforms as
`z ↦ conj b · a² · z`, so every endpoint progress ratio (and its
normalization) is invariant.  The vector field is equivariant under the same
control `u`, hence the integral equation commutes with `sectorPhase`.
`faceAlign p q` is the sector phase mapping a supplied face state `p` to a
face state `q`.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set ComplexConjugate

/-! ## The sector-phase map and its continuous linear form -/

/-- Multiply sector `k`'s two amplitudes by the constant phase `a` or `b`. -/
def sectorPhase (a b : ℂ) (x : State) : State :=
  mkState (a * g1 x) (a * r1 x) (b * g2 x) (b * r2 x)

private theorem g1_add (x y : State) : g1 (x + y) = g1 x + g1 y :=
  Complex.ext rfl rfl

private theorem r1_add (x y : State) : r1 (x + y) = r1 x + r1 y :=
  Complex.ext rfl rfl

private theorem g2_add (x y : State) : g2 (x + y) = g2 x + g2 y :=
  Complex.ext rfl rfl

private theorem r2_add (x y : State) : r2 (x + y) = r2 x + r2 y :=
  Complex.ext rfl rfl

private theorem g1_smul (c : ℝ) (x : State) : g1 (c • x) = c • g1 x := by
  apply Complex.ext <;> simp [Complex.real_smul, g1]

private theorem r1_smul (c : ℝ) (x : State) : r1 (c • x) = c • r1 x := by
  apply Complex.ext <;> simp [Complex.real_smul, r1]

private theorem g2_smul (c : ℝ) (x : State) : g2 (c • x) = c • g2 x := by
  apply Complex.ext <;> simp [Complex.real_smul, g2]

private theorem r2_smul (c : ℝ) (x : State) : r2 (c • x) = c • r2 x := by
  apply Complex.ext <;> simp [Complex.real_smul, r2]

/-- `sectorPhase` is `ℝ`-linear; on the finite-dimensional `State` space it is
automatically continuous. -/
def sectorPhaseLM (a b : ℂ) : State →ₗ[ℝ] State where
  toFun := sectorPhase a b
  map_add' x y := by
    apply state_ext <;>
      simp only [sectorPhase, g1_mkState, r1_mkState, g2_mkState,
        r2_mkState, g1_add, r1_add, g2_add, r2_add] <;>
      ring
  map_smul' c x := by
    apply state_ext <;>
      simp only [sectorPhase, g1_mkState, r1_mkState, g2_mkState,
        r2_mkState, g1_smul, r1_smul, g2_smul, r2_smul, Complex.real_smul,
        RingHom.id_apply] <;>
      ring

/-- `sectorPhase` as a real continuous linear map on `State`. -/
def sectorPhaseCLM (a b : ℂ) : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap (sectorPhaseLM a b)

@[simp] theorem sectorPhaseCLM_apply (a b : ℂ) (x : State) :
    sectorPhaseCLM a b x = sectorPhase a b x := by
  simp [sectorPhaseCLM, sectorPhaseLM, LinearMap.coe_toContinuousLinearMap']

/-! ## Preservation of `X`, `F`, cost, and the progress observable -/

theorem sectorPhase_mem_Xset {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {x : State} (hx : x ∈ Xset) : sectorPhase a b x ∈ Xset := by
  obtain ⟨h1, h2⟩ := hx
  constructor
  · show ‖a * g1 x‖ ^ 2 + ‖a * r1 x‖ ^ 2 = 1
    rw [norm_mul, norm_mul, ha]
    have : (1 * ‖g1 x‖) ^ 2 + (1 * ‖r1 x‖) ^ 2 =
        ‖g1 x‖ ^ 2 + ‖r1 x‖ ^ 2 := by ring
    rw [this]
    exact h1
  · show ‖b * g2 x‖ ^ 2 + ‖b * r2 x‖ ^ 2 = 1
    rw [norm_mul, norm_mul, hb]
    have : (1 * ‖g2 x‖) ^ 2 + (1 * ‖r2 x‖) ^ 2 =
        ‖g2 x‖ ^ 2 + ‖r2 x‖ ^ 2 := by ring
    rw [this]
    exact h2

theorem sectorPhase_mem_Fface {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {x : State} (hx : x ∈ Fface) : sectorPhase a b x ∈ Fface := by
  obtain ⟨hxX, hr1, hr2⟩ := hx
  refine ⟨sectorPhase_mem_Xset ha hb hxX, ?_, ?_⟩
  · show a * r1 x = 0
    rw [hr1, mul_zero]
  · show b * r2 x = 0
    rw [hr2, mul_zero]

theorem cost_sectorPhase {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (x : State) : cost (sectorPhase a b x) = cost x := by
  show (2 * ‖a * r1 x‖ ^ 2 + ‖b * r2 x‖ ^ 2) / 4 = cost x
  rw [norm_mul, norm_mul, ha, hb]
  show (2 * (1 * ‖r1 x‖) ^ 2 + (1 * ‖r2 x‖) ^ 2) / 4 = cost x
  rw [show cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4 from rfl]
  ring

theorem zObs_sectorPhase (a b : ℂ) (x : State) :
    zObs (sectorPhase a b x) = (conj b * a ^ 2) * zObs x := by
  simp only [zObs, sectorPhase, g1_mkState, r1_mkState, g2_mkState,
    r2_mkState, map_mul]
  ring

/-! ## Equivariance of the dynamics -/

private theorem g1_vf (x : State) (u : ℂ) : g1 (vf x u) = fC x u 0 :=
  Complex.ext rfl rfl

private theorem r1_vf (x : State) (u : ℂ) : r1 (vf x u) = fC x u 1 :=
  Complex.ext rfl rfl

private theorem g2_vf (x : State) (u : ℂ) : g2 (vf x u) = fC x u 2 :=
  Complex.ext rfl rfl

private theorem r2_vf (x : State) (u : ℂ) : r2 (vf x u) = fC x u 3 :=
  Complex.ext rfl rfl

set_option linter.unusedSimpArgs false in
theorem sectorPhase_vf (a b : ℂ) (x : State) (u : ℂ) :
    sectorPhase a b (vf x u) = vf (sectorPhase a b x) u := by
  apply state_ext
  · show a * g1 (vf x u) = g1 (vf (sectorPhase a b x) u)
    rw [g1_vf, g1_vf]
    simp only [fC, sectorPhase, r1_mkState, Matrix.cons_val_zero]
    ring
  · show a * r1 (vf x u) = r1 (vf (sectorPhase a b x) u)
    rw [r1_vf, r1_vf]
    simp only [fC, sectorPhase, g1_mkState, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · show b * g2 (vf x u) = g2 (vf (sectorPhase a b x) u)
    rw [g2_vf, g2_vf]
    simp only [fC, sectorPhase, r2_mkState, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · show b * r2 (vf x u) = r2 (vf (sectorPhase a b x) u)
    rw [r2_vf, r2_vf]
    simp only [fC, sectorPhase, g2_mkState, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    ring

theorem hasDerivAt_sectorPhase (a b : ℂ) {x : ℝ → State} {u : ℂ} {s : ℝ}
    (hx : HasDerivAt x (vf (x s) u) s) :
    HasDerivAt (fun t => sectorPhase a b (x t))
      (vf (sectorPhase a b (x s)) u) s := by
  have h := (sectorPhaseCLM a b).hasFDerivAt.comp_hasDerivAt s hx
  exact h.congr_deriv
    ((sectorPhaseCLM_apply a b _).trans (sectorPhase_vf a b (x s) u))

/-- The sector-phase action commutes with the integral form of the dynamics
under the same control `u`. -/
theorem sectorPhase_integralEquation (a b : ℂ) {x : ℝ → State} {u : ℝ → ℂ}
    {s t : ℝ}
    (hint : IntervalIntegrable (fun r => vf (x r) (u r)) volume s t)
    (hode : x t = x s + ∫ r in s..t, vf (x r) (u r)) :
    sectorPhase a b (x t) = sectorPhase a b (x s) +
      ∫ r in s..t, vf (sectorPhase a b (x r)) (u r) := by
  have key : ∫ r in s..t, vf (sectorPhase a b (x r)) (u r) =
      sectorPhaseCLM a b (∫ r in s..t, vf (x r) (u r)) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    apply intervalIntegral.integral_congr
    intro r hr
    exact (sectorPhase_vf a b (x r) (u r)).symm.trans
      (sectorPhaseCLM_apply a b _).symm
  rw [hode, key, ← sectorPhaseCLM_apply, ← sectorPhaseCLM_apply,
    (sectorPhaseCLM a b).map_add]

/-! ## Invariance of progress ratios -/

theorem zObs_ratio_sectorPhase {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (x₁ x₂ : State) :
    zObs (sectorPhase a b x₂) / zObs (sectorPhase a b x₁) =
      zObs x₂ / zObs x₁ := by
  have hc : conj b * a ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · exact norm_ne_zero_iff.mp
        (by rw [Complex.norm_conj, hb]; norm_num)
    · exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by rw [ha]; norm_num))
  rw [zObs_sectorPhase, zObs_sectorPhase]
  exact mul_div_mul_left _ _ hc

theorem unitPhase_ratio_sectorPhase {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (x₁ x₂ : State) :
    complexUnitPhase (zObs (sectorPhase a b x₂)) /
      complexUnitPhase (zObs (sectorPhase a b x₁)) =
    complexUnitPhase (zObs x₂) / complexUnitPhase (zObs x₁) := by
  have hb0 : conj b ≠ 0 := norm_ne_zero_iff.mp
    (by rw [Complex.norm_conj, hb]; norm_num)
  have ha20 : a ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mp (by rw [ha]; norm_num))
  have hc0 : complexUnitPhase (conj b) * complexUnitPhase (a ^ 2) ≠ 0 :=
    mul_ne_zero
      (norm_ne_zero_iff.mp (by rw [norm_complexUnitPhase hb0]; norm_num))
      (norm_ne_zero_iff.mp (by rw [norm_complexUnitPhase ha20]; norm_num))
  rw [zObs_sectorPhase, zObs_sectorPhase, complexUnitPhase_mul,
    complexUnitPhase_mul, complexUnitPhase_mul, complexUnitPhase_mul]
  exact mul_div_mul_left _ _ hc0

/-! ## Face alignment -/

/-- The sector phase carrying face state `p` to face state `q`. -/
def faceAlign (p q : State) : State → State :=
  sectorPhase (g1 q / g1 p) (g2 q / g2 p)

theorem faceAlign_unit {p q : State} (hp : p ∈ Fface) (hq : q ∈ Fface) :
    ‖g1 q / g1 p‖ = 1 ∧ ‖g2 q / g2 p‖ = 1 := by
  obtain ⟨hp1, hp2⟩ := norm_ground_of_mem_Fface hp
  obtain ⟨hq1, hq2⟩ := norm_ground_of_mem_Fface hq
  exact ⟨by rw [norm_div, hq1, hp1, div_one],
         by rw [norm_div, hq2, hp2, div_one]⟩

theorem faceAlign_source {p q : State} (hp : p ∈ Fface) (hq : q ∈ Fface) :
    faceAlign p q p = q := by
  have hp1 := hp.2.1
  have hp2 := hp.2.2
  have hq1 := hq.2.1
  have hq2 := hq.2.2
  obtain ⟨hgp1, hgp2⟩ := norm_ground_of_mem_Fface hp
  have hg1p : g1 p ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hgp1]; norm_num)
  have hg2p : g2 p ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hgp2]; norm_num)
  apply state_ext
  · show (g1 q / g1 p) * g1 p = g1 q
    rw [div_mul_cancel₀ _ hg1p]
  · show (g1 q / g1 p) * r1 p = r1 q
    rw [hp1, mul_zero, hq1]
  · show (g2 q / g2 p) * g2 p = g2 q
    rw [div_mul_cancel₀ _ hg2p]
  · show (g2 q / g2 p) * r2 p = r2 q
    rw [hp2, mul_zero, hq2]

theorem faceAlign_cost {p q : State} (hp : p ∈ Fface) (hq : q ∈ Fface)
    (x : State) : cost (faceAlign p q x) = cost x :=
  cost_sectorPhase (faceAlign_unit hp hq).1 (faceAlign_unit hp hq).2 x

theorem faceAlign_zObs_ratio {p q : State} (hp : p ∈ Fface) (hq : q ∈ Fface)
    (x : State) :
    zObs (faceAlign p q x) / zObs q = zObs x / zObs p := by
  have hp1 := hp.2.1
  have hp2 := hp.2.2
  have hq1 := hq.2.1
  have hq2 := hq.2.2
  obtain ⟨hgp1, hgp2⟩ := norm_ground_of_mem_Fface hp
  obtain ⟨hgq1, hgq2⟩ := norm_ground_of_mem_Fface hq
  have hg1p : g1 p ≠ 0 := norm_ne_zero_iff.mp (by rw [hgp1]; norm_num)
  have hg2p : g2 p ≠ 0 := norm_ne_zero_iff.mp (by rw [hgp2]; norm_num)
  have hg1q : g1 q ≠ 0 := norm_ne_zero_iff.mp (by rw [hgq1]; norm_num)
  have hg2q : g2 q ≠ 0 := norm_ne_zero_iff.mp (by rw [hgq2]; norm_num)
  have hcg2p : conj (g2 p) ≠ 0 := norm_ne_zero_iff.mp
    (by rw [Complex.norm_conj, hgp2]; norm_num)
  have hzq : zObs q = (conj (g2 q / g2 p) * (g1 q / g1 p) ^ 2) * zObs p := by
    have hzp : zObs p = conj (g2 p) * g1 p ^ 2 := by
      rw [zObs, hp1, hp2]
      simp
    have hzqe : zObs q = conj (g2 q) * g1 q ^ 2 := by
      rw [zObs, hq1, hq2]
      simp
    rw [hzqe, hzp, map_div₀]
    field_simp
  have hc0 : conj (g2 q / g2 p) * (g1 q / g1 p) ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · rw [map_div₀]
      exact div_ne_zero
        (norm_ne_zero_iff.mp (by rw [Complex.norm_conj, hgq2]; norm_num))
        hcg2p
    · exact pow_ne_zero 2 (div_ne_zero hg1q hg1p)
  rw [faceAlign, zObs_sectorPhase, hzq]
  exact mul_div_mul_left _ _ hc0

end CZExposure
