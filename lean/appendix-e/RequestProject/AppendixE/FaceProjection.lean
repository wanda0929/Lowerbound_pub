module
public import RequestProject.AppendixE.ExposureProgress
public import RequestProject.AppendixE.PhaseTransport

/-!
# Endpoint projection to the zero-cost face and static CZ repair

For `x ∈ X` with `c(x) ≤ 1/12`, `faceProjection` is the paper's projection
`P(x) = (phase(g₁), 0, phase(g₁)² conj(phase(z)), 0)` onto `F`.  It satisfies
`z(P(x)) = phase(z(x))` and `‖P(x) − x‖ ≤ 32√c(x)` in the ambient sup norm on
`State` (not the Riemannian distance of the ball-box argument).  For `x ∈ F`,
`faceCZTarget x` is a point of the exact CZ orbit at ambient distance at most
`|z(x)+1|`, hence at most `|θ|` when `z(x) = −exp(iθ)`.  These are static
algebra/distance statements: no steering trajectory is asserted.

`PositiveExposureSegment.zObs_liftedState` identifies the lifted progress
observable with the exposure-path progress, and
`FiniteExcursionSelection.physical_endpoints_projection` applies the
projection bounds to both physical endpoints of every retained segment.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set ComplexConjugate

/-! ## `mkState` coordinate lemmas and extensionality -/

@[simp] theorem g1_mkState (a b c d : ℂ) : g1 (mkState a b c d) = a := by
  apply Complex.ext <;> simp [g1, mkState]

@[simp] theorem r1_mkState (a b c d : ℂ) : r1 (mkState a b c d) = b := by
  apply Complex.ext <;> simp [r1, mkState]

@[simp] theorem g2_mkState (a b c d : ℂ) : g2 (mkState a b c d) = c := by
  apply Complex.ext <;> simp [g2, mkState]

@[simp] theorem r2_mkState (a b c d : ℂ) : r2 (mkState a b c d) = d := by
  apply Complex.ext <;> simp [r2, mkState]

theorem state_ext {x y : State} (hg1 : g1 x = g1 y) (hr1 : r1 x = r1 y)
    (hg2 : g2 x = g2 y) (hr2 : r2 x = r2 y) : x = y := by
  funext i
  fin_cases i
  · exact congrArg Complex.re hg1
  · exact congrArg Complex.im hg1
  · exact congrArg Complex.re hr1
  · exact congrArg Complex.im hr1
  · exact congrArg Complex.re hg2
  · exact congrArg Complex.im hg2
  · exact congrArg Complex.re hr2
  · exact congrArg Complex.im hr2

@[simp] theorem mkState_eta (x : State) :
    mkState (g1 x) (r1 x) (g2 x) (r2 x) = x := by
  apply state_ext <;> simp

private theorem g1_sub (x y : State) : g1 (x - y) = g1 x - g1 y := rfl
private theorem r1_sub (x y : State) : r1 (x - y) = r1 x - r1 y := rfl
private theorem g2_sub (x y : State) : g2 (x - y) = g2 x - g2 y := rfl
private theorem r2_sub (x y : State) : r2 (x - y) = r2 x - r2 y := rfl

private theorem norm_mkState_le {a b c d : ℂ} :
    ‖mkState a b c d‖ ≤ max (max ‖a‖ ‖b‖) (max ‖c‖ ‖d‖) := by
  have hD : (0:ℝ) ≤ max (max ‖a‖ ‖b‖) (max ‖c‖ ‖d‖) :=
    le_trans (norm_nonneg a) ((le_max_left _ _).trans (le_max_left _ _))
  rw [pi_norm_le_iff_of_nonneg hD]
  intro i
  fin_cases i <;>
    simp only [mkState, Real.norm_eq_abs]
  · exact (Complex.abs_re_le_norm a).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (Complex.abs_im_le_norm a).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (Complex.abs_re_le_norm b).trans
      ((le_max_right _ _).trans (le_max_left _ _))
  · exact (Complex.abs_im_le_norm b).trans
      ((le_max_right _ _).trans (le_max_left _ _))
  · exact (Complex.abs_re_le_norm c).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (Complex.abs_im_le_norm c).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (Complex.abs_re_le_norm d).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · exact (Complex.abs_im_le_norm d).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-! ## Unit-phase algebra -/

theorem complexUnitPhase_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    complexUnitPhase z = z := by
  simp [complexUnitPhase, hz]

theorem complexUnitPhase_mul (z w : ℂ) :
    complexUnitPhase (z * w) = complexUnitPhase z * complexUnitPhase w := by
  simp only [complexUnitPhase, norm_mul, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, mul_inv]
  ring

theorem complexUnitPhase_conj (z : ℂ) :
    complexUnitPhase (conj z) = conj (complexUnitPhase z) := by
  simp only [complexUnitPhase, Complex.norm_conj, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

theorem norm_complexUnitPhase_sub_self {z : ℂ} (hz : z ≠ 0) :
    ‖complexUnitPhase z - z‖ = |1 - ‖z‖| := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have e : complexUnitPhase z - z = ((‖z‖ : ℂ)⁻¹ - 1) * z := by
    rw [complexUnitPhase, Complex.real_smul, Complex.ofReal_inv, sub_mul,
      one_mul]
  rw [e, norm_mul]
  have hcast : ((‖z‖ : ℂ)⁻¹ - 1) = ((‖z‖⁻¹ - 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖z‖⁻¹ - 1 = (1 - ‖z‖) / ‖z‖ := by
    field_simp
  rw [h1, abs_div, abs_of_pos (norm_pos_iff.mpr hz), div_mul_cancel₀ _ hn]

theorem norm_complexUnitPhase_sub_unit_le {z w : ℂ} (hz : z ≠ 0)
    (hw : ‖w‖ = 1) :
    ‖complexUnitPhase z - w‖ ≤ 2 * ‖z - w‖ := by
  have h2 : |1 - ‖z‖| ≤ ‖z - w‖ := by
    calc |1 - ‖z‖| = |‖w‖ - ‖z‖| := by rw [hw]
      _ ≤ ‖w - z‖ := abs_norm_sub_norm_le w z
      _ = ‖z - w‖ := norm_sub_rev w z
  calc ‖complexUnitPhase z - w‖
      ≤ ‖complexUnitPhase z - z‖ + ‖z - w‖ := by
        have e : complexUnitPhase z - w =
            (complexUnitPhase z - z) + (z - w) := by ring
        rw [e]
        exact norm_add_le _ _
    _ = |1 - ‖z‖| + ‖z - w‖ := by
        rw [norm_complexUnitPhase_sub_self hz]
    _ ≤ 2 * ‖z - w‖ := by linarith

/-! ## Basic facts on `F` and `X_CZ` -/

theorem norm_ground_of_mem_Fface {x : State} (hx : x ∈ Fface) :
    ‖g1 x‖ = 1 ∧ ‖g2 x‖ = 1 := by
  obtain ⟨hxX, hr1, hr2⟩ := hx
  have h1 : ‖g1 x‖ ^ 2 = 1 := by
    have h := hxX.1
    rw [hr1, norm_zero] at h
    linarith
  have h2 : ‖g2 x‖ ^ 2 = 1 := by
    have h := hxX.2
    rw [hr2, norm_zero] at h
    linarith
  constructor
  · calc ‖g1 x‖ = Real.sqrt (‖g1 x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [h1, Real.sqrt_one]
  · calc ‖g2 x‖ = Real.sqrt (‖g2 x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [h2, Real.sqrt_one]

theorem norm_zObs_of_mem_Fface {x : State} (hx : x ∈ Fface) :
    ‖zObs x‖ = 1 := by
  have hr1 := hx.2.1
  have hr2 := hx.2.2
  obtain ⟨hg1, hg2⟩ := norm_ground_of_mem_Fface hx
  have hz : zObs x = conj (g2 x) * g1 x ^ 2 := by
    simp only [zObs, hr1, hr2, map_zero, mul_zero, add_zero]
  rw [hz, norm_mul, norm_pow, Complex.norm_conj, hg1, hg2]
  norm_num

theorem mem_XCZ_iff_zObs_eq_neg_one {x : State} (hx : x ∈ Fface) :
    x ∈ XCZ ↔ zObs x = -1 := by
  have hxX := hx.1
  have hr1 := hx.2.1
  have hr2 := hx.2.2
  obtain ⟨hg1, hg2⟩ := norm_ground_of_mem_Fface hx
  have hz : zObs x = conj (g2 x) * g1 x ^ 2 := by
    simp only [zObs, hr1, hr2, map_zero, mul_zero, add_zero]
  rw [hz]
  constructor
  · rintro ⟨-, -, -, hg⟩
    have hc : conj (g1 x ^ 2) * g1 x ^ 2 = 1 := by
      rw [Complex.conj_mul', norm_pow, hg1]
      norm_num
    rw [hg]
    calc conj (-(g1 x) ^ 2) * g1 x ^ 2
        = -(conj (g1 x ^ 2) * g1 x ^ 2) := by
          rw [map_neg]
          ring
      _ = -1 := by rw [hc]
  · intro h
    refine ⟨hxX, hr1, hr2, ?_⟩
    have hg2sq : conj (g2 x) * g2 x = 1 := by
      rw [Complex.conj_mul', hg2]
      norm_num
    have e1 : g1 x ^ 2 = -g2 x := by
      have step : g1 x ^ 2 = -1 * g2 x := by
        calc g1 x ^ 2 = g1 x ^ 2 * (conj (g2 x) * g2 x) := by
              rw [hg2sq, mul_one]
          _ = conj (g2 x) * g1 x ^ 2 * g2 x := by ring
          _ = -1 * g2 x := by rw [h]
      rw [step]
      ring
    rw [e1, neg_neg]

/-! ## The face projection -/

private theorem nonzero_of_low_cost {x : State} (hx : x ∈ Xset)
    (hc : cost x ≤ 1/12) :
    g1 x ≠ 0 ∧ g2 x ≠ 0 ∧ zObs x ≠ 0 := by
  have hr2sq : ‖r2 x‖ ^ 2 ≤ 4 * cost x := by
    have e : 4 * cost x = 2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2 := by
      show 4 * ((2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4) = _
      ring
    nlinarith [sq_nonneg (‖r1 x‖)]
  have h1 : ‖g1 x‖ ^ 2 ≥ 5 / 6 := by
    have h : ‖g1 x‖ ^ 2 = 1 - ‖r1 x‖ ^ 2 := by linarith [hx.1]
    have hr : ‖r1 x‖ ^ 2 ≤ 2 * cost x := r1_norm_sq_le x
    linarith
  have h2 : ‖g2 x‖ ^ 2 ≥ 1 / 2 := by
    have h : ‖g2 x‖ ^ 2 = 1 - ‖r2 x‖ ^ 2 := by linarith [hx.2]
    linarith
  have h3 : (1 / 2 : ℝ) ≤ ‖zObs x‖ := by
    have h := norm_zObs_ge_one_sub_six_cost hx
    linarith
  exact ⟨fun h0 => by rw [h0, norm_zero] at h1; norm_num at h1,
         fun h0 => by rw [h0, norm_zero] at h2; norm_num at h2,
         fun h0 => by rw [h0, norm_zero] at h3; norm_num at h3⟩

/-- The cross term `√2·r̄₂g₁r₁` of `z` is bounded by `2c`; the argument is
the one used in `norm_zObs_ge_one_sub_six_cost`. -/
private theorem norm_cross_le_two_cost (x : State) (hx : x ∈ Xset) :
    ‖(Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖ ≤ 2 * cost x := by
  have hb1 : ‖(Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖ =
      Real.sqrt 2 * ‖r2 x‖ * ‖g1 x‖ * ‖r1 x‖ := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), mul_assoc]
  have hb2 : Real.sqrt 2 * ‖r2 x‖ * ‖g1 x‖ * ‖r1 x‖ ≤
      Real.sqrt 2 * ‖r2 x‖ * 1 * ‖r1 x‖ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_g1_le_one hx)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
      (norm_nonneg (r1 x))
  have hb3 : Real.sqrt 2 * ‖r2 x‖ * 1 * ‖r1 x‖ ≤ 2 * cost x := by
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hc : 2 * cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 2 := by
      rw [show cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4 from rfl]
      ring
    rw [hc]
    nlinarith [sq_nonneg (Real.sqrt 2 * ‖r1 x‖ - ‖r2 x‖),
      Real.sqrt_nonneg (2 : ℝ), norm_nonneg (r1 x), norm_nonneg (r2 x)]
  rw [hb1]
  exact hb2.trans hb3

/-- For `0 ≤ t ≤ 1`, `1 − √(1−t) ≤ t`. -/
private theorem one_sub_sqrt_one_sub_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 - Real.sqrt (1 - t) ≤ t := by
  have hs : 1 - t ≤ Real.sqrt (1 - t) := by
    rw [Real.le_sqrt (by linarith)]
    · nlinarith
    · linarith
  linarith

def faceProjection (x : State) : State :=
  mkState (complexUnitPhase (g1 x)) 0
    (complexUnitPhase (g1 x) ^ 2 * conj (complexUnitPhase (zObs x))) 0

@[simp] theorem cost_faceProjection (x : State) :
    cost (faceProjection x) = 0 := by
  simp [faceProjection, cost, r1_mkState, r2_mkState]

theorem faceProjection_mem {x : State} (hx : x ∈ Xset)
    (hc : cost x ≤ 1/12) :
    faceProjection x ∈ Fface := by
  obtain ⟨hg1n0, -, hzn0⟩ := nonzero_of_low_cost hx hc
  have hp1 : ‖complexUnitPhase (g1 x)‖ = 1 := norm_complexUnitPhase hg1n0
  have hP : ‖complexUnitPhase (g1 x) ^ 2 *
      conj (complexUnitPhase (zObs x))‖ = 1 := by
    rw [norm_mul, norm_pow, hp1, Complex.norm_conj,
      norm_complexUnitPhase hzn0]
    norm_num
  have hX : faceProjection x ∈ Xset := by
    simp only [Xset, Set.mem_setOf_eq, faceProjection, g1_mkState,
      r1_mkState, g2_mkState, r2_mkState]
    constructor
    · rw [hp1, norm_zero]
      norm_num
    · rw [hP, norm_zero]
      norm_num
  exact ⟨hX, by simp [faceProjection], by simp [faceProjection]⟩

theorem zObs_faceProjection {x : State} (hx : x ∈ Xset)
    (hc : cost x ≤ 1/12) :
    zObs (faceProjection x) = complexUnitPhase (zObs x) := by
  obtain ⟨hg1n0, -, hzn0⟩ := nonzero_of_low_cost hx hc
  have hp1 : ‖complexUnitPhase (g1 x)‖ = 1 := norm_complexUnitPhase hg1n0
  have hc1 : conj (complexUnitPhase (g1 x) ^ 2) *
      complexUnitPhase (g1 x) ^ 2 = 1 := by
    rw [Complex.conj_mul', norm_pow, hp1]
    norm_num
  calc zObs (faceProjection x)
      = conj (complexUnitPhase (g1 x) ^ 2 *
          conj (complexUnitPhase (zObs x))) *
            complexUnitPhase (g1 x) ^ 2 := by
        simp [zObs, faceProjection, g1_mkState, r1_mkState, g2_mkState,
          r2_mkState]
    _ = conj (complexUnitPhase (g1 x) ^ 2) *
          complexUnitPhase (g1 x) ^ 2 * complexUnitPhase (zObs x) := by
        rw [map_mul, starRingEnd_self_apply]
        ring
    _ = complexUnitPhase (zObs x) := by rw [hc1, one_mul]

theorem faceProjection_eq_self {x : State} (hx : x ∈ Fface) :
    faceProjection x = x := by
  have hr1 := hx.2.1
  have hr2 := hx.2.2
  obtain ⟨hg1, hg2⟩ := norm_ground_of_mem_Fface hx
  have hz : ‖zObs x‖ = 1 := norm_zObs_of_mem_Fface hx
  have hzObs : zObs x = conj (g2 x) * g1 x ^ 2 := by
    simp only [zObs, hr1, hr2, map_zero, mul_zero, add_zero]
  have hg2eq : complexUnitPhase (g1 x) ^ 2 *
      conj (complexUnitPhase (zObs x)) = g2 x := by
    rw [complexUnitPhase_of_norm_one hg1, complexUnitPhase_of_norm_one hz,
      hzObs, map_mul, map_pow, starRingEnd_self_apply]
    have e : g1 x ^ 2 * conj (g1 x) ^ 2 = 1 := by
      rw [← mul_pow, mul_comm (g1 x) _, Complex.conj_mul', hg1]
      norm_num
    calc g1 x ^ 2 * (g2 x * conj (g1 x) ^ 2)
        = g2 x * (g1 x ^ 2 * conj (g1 x) ^ 2) := by ring
      _ = g2 x := by rw [e, mul_one]
  apply state_ext
  · show complexUnitPhase (g1 x) = g1 x
    exact complexUnitPhase_of_norm_one hg1
  · show (0 : ℂ) = r1 x
    exact hr1.symm
  · show complexUnitPhase (g1 x) ^ 2 *
        conj (complexUnitPhase (zObs x)) = g2 x
    exact hg2eq
  · show (0 : ℂ) = r2 x
    exact hr2.symm

theorem norm_faceProjection_sub_le {x : State} (hx : x ∈ Xset)
    (hc : cost x ≤ 1/12) :
    ‖faceProjection x - x‖ ≤ 32 * Real.sqrt (cost x) := by
  obtain ⟨hg1n0, hg2n0, hzn0⟩ := nonzero_of_low_cost hx hc
  set p1 := complexUnitPhase (g1 x) with hp1d
  set p2 := complexUnitPhase (g2 x) with hp2d
  set w := conj p2 * p1 ^ 2 with hwd
  have hc0 : 0 ≤ cost x := cost_nonneg x
  have hc1 : cost x ≤ 1 := cost_le_one hx
  have hp1 : ‖p1‖ = 1 := norm_complexUnitPhase hg1n0
  have hp2 : ‖p2‖ = 1 := norm_complexUnitPhase hg2n0
  have hw : ‖w‖ = 1 := by
    rw [hwd, norm_mul, Complex.norm_conj, hp2, norm_pow, hp1]
    norm_num
  have hr1sq : ‖r1 x‖ ^ 2 ≤ 2 * cost x := r1_norm_sq_le x
  have hr2sq : ‖r2 x‖ ^ 2 ≤ 4 * cost x := by
    have e : 4 * cost x = 2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2 := by
      show 4 * ((2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4) = _
      ring
    nlinarith [sq_nonneg (‖r1 x‖)]
  have hg1le : ‖g1 x‖ ≤ 1 := norm_g1_le_one hx
  have hg2le : ‖g2 x‖ ≤ 1 := norm_g2_le_one hx
  have hg1sq' : ‖g1 x‖ = Real.sqrt (1 - ‖r1 x‖ ^ 2) := by
    have h : ‖g1 x‖ ^ 2 = 1 - ‖r1 x‖ ^ 2 := by linarith [hx.1]
    conv_rhs => rw [← h]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hg2sq' : ‖g2 x‖ = Real.sqrt (1 - ‖r2 x‖ ^ 2) := by
    have h : ‖g2 x‖ ^ 2 = 1 - ‖r2 x‖ ^ 2 := by linarith [hx.2]
    conv_rhs => rw [← h]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hsub1 : ‖p1 - g1 x‖ ≤ ‖r1 x‖ ^ 2 := by
    rw [hp1d, norm_complexUnitPhase_sub_self hg1n0,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ‖g1 x‖), hg1sq']
    exact one_sub_sqrt_one_sub_le (sq_nonneg _)
      (by nlinarith [norm_r1_le_one hx, norm_nonneg (r1 x)])
  have hsub2 : ‖p2 - g2 x‖ ≤ ‖r2 x‖ ^ 2 := by
    rw [hp2d, norm_complexUnitPhase_sub_self hg2n0,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ‖g2 x‖), hg2sq']
    exact one_sub_sqrt_one_sub_le (sq_nonneg _)
      (by nlinarith [norm_r2_le_one hx, norm_nonneg (r2 x)])
  have hgsq : ‖g1 x ^ 2 - p1 ^ 2‖ ≤ 4 * cost x := by
    have e : g1 x ^ 2 - p1 ^ 2 = (g1 x - p1) * (g1 x + p1) := by ring
    have h1 : ‖g1 x - p1‖ ≤ ‖r1 x‖ ^ 2 := by rwa [norm_sub_rev]
    have h2 : ‖g1 x + p1‖ ≤ 2 := by
      have h := norm_add_le (g1 x) p1
      linarith
    have h3 : ‖g1 x - p1‖ * ‖g1 x + p1‖ ≤ ‖r1 x‖ ^ 2 * 2 :=
      mul_le_mul h1 h2 (norm_nonneg _) (sq_nonneg _)
    rw [e, norm_mul]
    linarith
  have hwg : ‖conj (g2 x) * g1 x ^ 2 - w‖ ≤ 8 * cost x := by
    have e : conj (g2 x) * g1 x ^ 2 - w =
        conj (g2 x) * (g1 x ^ 2 - p1 ^ 2) +
          (conj (g2 x) - conj p2) * p1 ^ 2 := by
      rw [hwd]
      ring
    have hconj : conj (g2 x) - conj p2 = conj (g2 x - p2) := by
      simp
    have h1 : ‖conj (g2 x) * (g1 x ^ 2 - p1 ^ 2)‖ ≤ 4 * cost x := by
      rw [norm_mul, Complex.norm_conj]
      have h := mul_le_mul hg2le hgsq (norm_nonneg _) (by norm_num)
      linarith
    have h2 : ‖(conj (g2 x) - conj p2) * p1 ^ 2‖ ≤ 4 * cost x := by
      rw [norm_mul, hconj, Complex.norm_conj, norm_pow, hp1, one_pow,
        mul_one]
      rw [norm_sub_rev]
      exact hsub2.trans hr2sq
    rw [e]
    exact (norm_add_le _ _).trans
      ((add_le_add h1 h2).trans_eq (by ring))
  have hzw : ‖zObs x - w‖ ≤ 10 * cost x := by
    have e : zObs x - w = (conj (g2 x) * g1 x ^ 2 - w) +
        ((Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x) := by
      rw [zObs]
      ring
    rw [e]
    calc ‖conj (g2 x) * g1 x ^ 2 - w +
          (Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖
        ≤ ‖conj (g2 x) * g1 x ^ 2 - w‖ +
          ‖(Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖ := norm_add_le _ _
      _ ≤ 8 * cost x + 2 * cost x :=
          add_le_add hwg (norm_cross_le_two_cost x hx)
      _ = 10 * cost x := by ring
  have huz : ‖complexUnitPhase (zObs x) - w‖ ≤ 20 * cost x := by
    have h := (norm_complexUnitPhase_sub_unit_le hzn0 hw).trans
      (mul_le_mul_of_nonneg_left hzw (by norm_num))
    linarith
  have hpw : p1 ^ 2 * conj w = p2 := by
    rw [hwd, map_mul, starRingEnd_self_apply]
    have e : p1 ^ 2 * conj (p1 ^ 2) = 1 := by
      rw [mul_comm, Complex.conj_mul', norm_pow, hp1]
      norm_num
    calc p1 ^ 2 * (p2 * conj (p1 ^ 2))
        = p2 * (p1 ^ 2 * conj (p1 ^ 2)) := by ring
      _ = p2 := by rw [e, mul_one]
  have hPp2 : ‖p1 ^ 2 * conj (complexUnitPhase (zObs x)) - p2‖ ≤
      20 * cost x := by
    have e : p1 ^ 2 * conj (complexUnitPhase (zObs x)) - p2 =
        p1 ^ 2 * conj (complexUnitPhase (zObs x) - w) := by
      have e1 : conj (complexUnitPhase (zObs x) - w) =
          conj (complexUnitPhase (zObs x)) - conj w := by simp
      rw [e1, mul_sub, hpw]
    rw [e, norm_mul, norm_pow, hp1, one_pow, Complex.norm_conj, one_mul]
    exact huz
  have hPg : ‖p1 ^ 2 * conj (complexUnitPhase (zObs x)) - g2 x‖ ≤
      24 * cost x := by
    have e : p1 ^ 2 * conj (complexUnitPhase (zObs x)) - g2 x =
        (p1 ^ 2 * conj (complexUnitPhase (zObs x)) - p2) + (p2 - g2 x) :=
      by ring
    rw [e]
    calc ‖(p1 ^ 2 * conj (complexUnitPhase (zObs x)) - p2) + (p2 - g2 x)‖
        ≤ ‖p1 ^ 2 * conj (complexUnitPhase (zObs x)) - p2‖ +
          ‖p2 - g2 x‖ := norm_add_le _ _
      _ ≤ 20 * cost x + 4 * cost x :=
          add_le_add hPp2 (hsub2.trans hr2sq)
      _ = 24 * cost x := by ring
  -- the rydberg amplitudes are `O(√c)`
  have hr1b : ‖r1 x‖ ≤ 2 * Real.sqrt (cost x) := by
    have h : ‖r1 x‖ ≤ Real.sqrt (2 * cost x) := by
      rw [← Real.sqrt_sq (norm_nonneg (r1 x))]
      exact Real.sqrt_le_sqrt hr1sq
    calc ‖r1 x‖ ≤ Real.sqrt (2 * cost x) := h
      _ = Real.sqrt 2 * Real.sqrt (cost x) := Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.sqrt (cost x) :=
          mul_le_mul_of_nonneg_right sqrt_two_le (Real.sqrt_nonneg _)
  have hr2b : ‖r2 x‖ ≤ 2 * Real.sqrt (cost x) := r2_norm_le_sqrt x
  -- `c ≤ √c` since `0 ≤ c ≤ 1`
  have hsqrt1 : Real.sqrt (cost x) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hc1
    rwa [Real.sqrt_one] at h
  have hcle : cost x ≤ Real.sqrt (cost x) := by
    have h := Real.mul_self_sqrt hc0
    calc cost x = Real.sqrt (cost x) * Real.sqrt (cost x) := h.symm
      _ ≤ 1 * Real.sqrt (cost x) :=
          mul_le_mul_of_nonneg_right hsqrt1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (cost x) := one_mul _
  have hD : (0:ℝ) ≤ 32 * Real.sqrt (cost x) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hdiff : faceProjection x - x =
      mkState (complexUnitPhase (g1 x) - g1 x) (0 - r1 x)
        (complexUnitPhase (g1 x) ^ 2 * conj (complexUnitPhase (zObs x)) -
          g2 x) (0 - r2 x) := by
    apply state_ext <;>
      simp only [faceProjection, g1_mkState, r1_mkState, g2_mkState,
        r2_mkState, g1_sub, r1_sub, g2_sub, r2_sub]
  rw [hdiff]
  refine norm_mkState_le.trans ?_
  rw [zero_sub, zero_sub, norm_neg, norm_neg]
  simp only [max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (hsub1.trans hr1sq).trans (by linarith)
  · exact hr1b.trans (by linarith)
  · exact hPg.trans
      (by nlinarith [hcle, Real.sqrt_nonneg (cost x)])
  · exact hr2b.trans (by linarith)

/-! ## Static exact-CZ target repair -/

/-- The exact-CZ target of a face state: `(g₁, 0, −g₁², 0)`. -/
def faceCZTarget (x : State) : State := mkState (g1 x) 0 (-(g1 x)^2) 0

theorem faceCZTarget_mem {x : State} (hx : x ∈ Fface) :
    faceCZTarget x ∈ XCZ := by
  obtain ⟨hg1, hg2⟩ := norm_ground_of_mem_Fface hx
  have hX : faceCZTarget x ∈ Xset := by
    simp only [Xset, Set.mem_setOf_eq, faceCZTarget, g1_mkState,
      r1_mkState, g2_mkState, r2_mkState]
    constructor <;> simp [norm_neg, norm_pow, hg1]
  refine ⟨hX, ?_, ?_, ?_⟩
  · simp [faceCZTarget]
  · simp [faceCZTarget]
  · simp [faceCZTarget]

theorem norm_faceCZTarget_sub_le {x : State} (hx : x ∈ Fface) :
    ‖faceCZTarget x - x‖ ≤ ‖zObs x + 1‖ := by
  have hr1 := hx.2.1
  have hr2 := hx.2.2
  obtain ⟨hg1, hg2⟩ := norm_ground_of_mem_Fface hx
  have hz : zObs x = conj (g2 x) * g1 x ^ 2 := by
    simp only [zObs, hr1, hr2, map_zero, mul_zero, add_zero]
  have hmain : ‖-(g1 x) ^ 2 - g2 x‖ = ‖zObs x + 1‖ := by
    have e : -(g1 x) ^ 2 - g2 x = -(g1 x ^ 2 + g2 x) := by ring
    have e3 : zObs x + 1 = conj (g2 x) * (g1 x ^ 2 + g2 x) := by
      rw [hz, mul_add, Complex.conj_mul', hg2]
      norm_num
    calc ‖-(g1 x) ^ 2 - g2 x‖
        = ‖g1 x ^ 2 + g2 x‖ := by rw [e, norm_neg]
      _ = ‖zObs x + 1‖ := by
          rw [e3, norm_mul, Complex.norm_conj, hg2, one_mul]
  have hdiff : faceCZTarget x - x =
      mkState 0 0 (-(g1 x) ^ 2 - g2 x) 0 := by
    apply state_ext <;>
      simp only [faceCZTarget, g1_mkState, r1_mkState, g2_mkState,
        r2_mkState, g1_sub, r1_sub, g2_sub, r2_sub, hr1, hr2, sub_self]
  have h0 : (0:ℝ) ≤ ‖-(g1 x) ^ 2 - g2 x‖ := norm_nonneg _
  calc ‖faceCZTarget x - x‖
      = ‖mkState 0 0 (-(g1 x) ^ 2 - g2 x) 0‖ := by rw [hdiff]
    _ ≤ max (max ‖(0:ℂ)‖ ‖(0:ℂ)‖)
          (max ‖-(g1 x) ^ 2 - g2 x‖ ‖(0:ℂ)‖) := norm_mkState_le
    _ = ‖-(g1 x) ^ 2 - g2 x‖ := by
        rw [norm_zero, max_self, max_eq_left h0, max_eq_right h0]
    _ = ‖zObs x + 1‖ := hmain

theorem norm_faceCZTarget_sub_le_phase {x : State} (hx : x ∈ Fface)
    {θ : ℝ} (hphase : zObs x = -phaseFactor θ) :
    ‖faceCZTarget x - x‖ ≤ |θ| := by
  have h := norm_faceCZTarget_sub_le hx
  rw [hphase] at h
  have e : ‖-phaseFactor θ + 1‖ = ‖phaseFactor θ - 1‖ := by
    have e1 : -phaseFactor θ + 1 = -(phaseFactor θ - 1) := by ring
    rw [e1, norm_neg]
  rw [e] at h
  exact h.trans (norm_phaseFactor_sub_one_le θ)

/-! ## Application to retained physical endpoints -/

namespace PositiveExposureSegment

theorem zObs_liftedState (S : PositiveExposureSegment) {t : ℝ}
    (ht : t ∈ Set.Icc S.a S.b) :
    zObs (S.liftedState t) = exposureProgressPath S.y t := by
  have hspec := euclideanStateLift_spec (S.y_mem t ht) (S.cost_pos ht)
  calc zObs (S.liftedState t)
      = euclideanProgressCLM
          (exposureEuclideanEquiv (Jmap (S.liftedState t))) :=
        (euclideanProgressCLM_Jmap _).symm
    _ = euclideanProgressCLM (S.y t) := congrArg _ hspec.2.1
    _ = exposureProgressPath S.y t := rfl

end PositiveExposureSegment

namespace FiniteExcursionSelection

theorem physical_endpoints_projection {T α β : ℝ} {y : ℝ → ExposureEuclidean}
    {u : ℝ → ℂ}
    (S : FiniteExcursionSelection T α β y u) (hα : α ≤ 1/12)
    (i : Fin S.count) :
    faceProjection ((S.segment i).physicalPath 0) ∈ Fface ∧
    faceProjection ((S.segment i).physicalPath (S.segment i).duration) ∈
      Fface ∧
    ‖faceProjection ((S.segment i).physicalPath 0) -
      (S.segment i).physicalPath 0‖ ≤ 32 * Real.sqrt α ∧
    ‖faceProjection ((S.segment i).physicalPath (S.segment i).duration) -
      (S.segment i).physicalPath (S.segment i).duration‖ ≤
        32 * Real.sqrt α ∧
    zObs (faceProjection ((S.segment i).physicalPath 0)) =
      complexUnitPhase (exposureProgressPath y (S.segment i).a) ∧
    zObs (faceProjection ((S.segment i).physicalPath (S.segment i).duration)) =
      complexUnitPhase (exposureProgressPath y (S.segment i).b) := by
  obtain ⟨hc0, hcd⟩ := S.physical_endpoints_cost i
  have hX0 : (S.segment i).physicalPath 0 ∈ Xset :=
    (S.segment i).physicalPath_mem 0
  have hXd : (S.segment i).physicalPath (S.segment i).duration ∈ Xset :=
    (S.segment i).physicalPath_mem _
  have hα0 : cost ((S.segment i).physicalPath 0) ≤ 1/12 := by
    rw [hc0]
    exact hα
  have hαd : cost ((S.segment i).physicalPath (S.segment i).duration) ≤
      1/12 := by
    rw [hcd]
    exact hα
  refine ⟨faceProjection_mem hX0 hα0, faceProjection_mem hXd hαd,
    ?_, ?_, ?_, ?_⟩
  · have hn := norm_faceProjection_sub_le hX0 hα0
    rwa [hc0] at hn
  · have hn := norm_faceProjection_sub_le hXd hαd
    rwa [hcd] at hn
  · have ha : (S.segment i).a ∈ Set.Icc (S.segment i).a (S.segment i).b :=
      ⟨le_rfl, (S.segment i).a_lt_b.le⟩
    rw [zObs_faceProjection hX0 hα0, (S.segment i).physicalPath_zero]
    congr 1
    have hl := (S.segment i).zObs_liftedState ha
    rw [S.trajectory_eq i] at hl
    exact hl
  · have hb : (S.segment i).b ∈ Set.Icc (S.segment i).a (S.segment i).b :=
      ⟨(S.segment i).a_lt_b.le, le_rfl⟩
    rw [zObs_faceProjection hXd hαd, (S.segment i).physicalPath_terminal]
    congr 1
    have hl := (S.segment i).zObs_liftedState hb
    rw [S.trajectory_eq i] at hl
    exact hl

end FiniteExcursionSelection

end CZExposure
