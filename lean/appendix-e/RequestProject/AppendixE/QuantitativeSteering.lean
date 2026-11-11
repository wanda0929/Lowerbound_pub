module
public import RequestProject.AppendixE.SteeringExposure
public import RequestProject.AppendixE.FaceProjection
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit quantitative local steering

`LocalSteering` packages quantitative controllability: positive `radius` and `K`, plus the
guarantee that nearby states of `X` are joined by a physical segment
of duration at most `K ‖y−x‖^(1/4)`.  The distance is the ambient
sup norm on `State`; no relation to a Riemannian distance is asserted.
`LocalSteeringConstruction.physicalLocalSteering` constructs an unconditional
inhabitant in the downstream `LocalSteeringConstruction` module using finite
pulse words and the inverse function theorem. `BallBoxSteering` retains its
alternative conditional constructor from a generic ball-box input.
-/

@[expose] public section

noncomputable section

namespace CZExposure

/-- Quantitative controllability in the ambient sup norm, with physical integral
dynamics. An unconditional inhabitant is constructed downstream in
`LocalSteeringConstruction.physicalLocalSteering`. -/
structure LocalSteering where
  radius : ℝ
  radius_pos : 0 < radius
  K : ℝ
  K_pos : 0 < K
  connect : ∀ (x : State), x ∈ Xset → ∀ (y : State), y ∈ Xset →
    ‖y - x‖ ≤ radius → ∃ P : PhysicalSegment,
      P.path 0 = x ∧ P.path P.duration = y ∧
      P.duration ≤ K * Real.rpow ‖y - x‖ (1/4 : ℝ)

namespace LocalSteering

open MeasureTheory Set
open scoped NNReal ENNReal

variable (H : LocalSteering)

def timeBound (d : ℝ) : ℝ := H.K * Real.rpow d (1/4 : ℝ)

def exposureBound (d : ℝ) : ℝ := (H.timeBound d)^3/12

theorem timeBound_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ H.timeBound d :=
  mul_nonneg H.K_pos.le (Real.rpow_nonneg hd _)

theorem timeBound_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e) :
    H.timeBound d ≤ H.timeBound e :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hd hde (by norm_num)) H.K_pos.le

@[simp] theorem timeBound_zero : H.timeBound 0 = 0 := by
  simp [timeBound]

@[simp] theorem exposureBound_zero : H.exposureBound 0 = 0 := by
  simp [exposureBound]

theorem exposureBound_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ H.exposureBound d :=
  div_nonneg (pow_nonneg (H.timeBound_nonneg hd) _) (by norm_num)

theorem exposureBound_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e) :
    H.exposureBound d ≤ H.exposureBound e := by
  unfold exposureBound
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (H.timeBound_nonneg hd) (H.timeBound_mono hd hde) 3)
    (by norm_num)

theorem exposureBound_eq {d : ℝ} (hd : 0 ≤ d) :
    H.exposureBound d = (H.K^3/12) * Real.rpow d (3/4 : ℝ) := by
  have h3 : (d ^ (1/4 : ℝ))^3 = d ^ (3/4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
    norm_num
  rw [exposureBound, timeBound, mul_pow]
  show H.K^3 * (d ^ (1/4 : ℝ))^3 / 12 = H.K^3/12 * d ^ (3/4 : ℝ)
  rw [h3]
  ring

/-- Cubic bound from `Q.duration ≤ timeBound d`: `Q.D³/12` is at most
`exposureBound d`. -/
private theorem cube_div_twelve_le_exposureBound {Q : PhysicalSegment}
    {d : ℝ} (hd0 : 0 ≤ d)
    (hQ : Q.duration ≤ H.timeBound d) :
    Q.duration^3/12 ≤ H.exposureBound d := by
  have hD : 0 ≤ Q.duration := Q.duration_nonneg
  have hT := H.timeBound_nonneg hd0
  have hc : Q.duration^3 ≤ (H.timeBound d)^3 :=
    pow_le_pow_left₀ hD hQ 3
  unfold exposureBound
  linarith [hc]

/-- Connection out of `F`, bounded by ANY supplied displacement upper
bound `d`. -/
theorem exists_from_face {p x : State} (hp : p ∈ Fface) (hx : x ∈ Xset)
    {d : ℝ} (hd : ‖x - p‖ ≤ d) (hnear : d ≤ H.radius) :
    ∃ Q : PhysicalSegment, Q.path 0 = p ∧ Q.path Q.duration = x ∧
      Q.duration ≤ H.timeBound d ∧ Q.exposure ≤ H.exposureBound d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  obtain ⟨Q, hQ0, hQD, hQdur⟩ :=
    H.connect p hp.1 x hx (hd.trans hnear)
  have hd0' : 0 ≤ ‖x - p‖ := norm_nonneg _
  refine ⟨Q, hQ0, hQD, hQdur.trans (H.timeBound_mono hd0' hd), ?_⟩
  have hstart : Q.path 0 ∈ Fface := hQ0 ▸ hp
  have h3 : Q.duration ≤ H.timeBound (‖x - p‖) := hQdur
  have h4 : Q.duration ≤ H.timeBound d :=
    h3.trans (H.timeBound_mono hd0' hd)
  exact (Q.exposure_le_cube_div_twelve hstart).trans
    (H.cube_div_twelve_le_exposureBound hd0 h4)

/-- Connection into `F`. -/
theorem exists_to_face {x p : State} (hx : x ∈ Xset) (hp : p ∈ Fface)
    {d : ℝ} (hd : ‖p - x‖ ≤ d) (hnear : d ≤ H.radius) :
    ∃ Q : PhysicalSegment, Q.path 0 = x ∧ Q.path Q.duration = p ∧
      Q.duration ≤ H.timeBound d ∧ Q.exposure ≤ H.exposureBound d := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  obtain ⟨Q, hQ0, hQD, hQdur⟩ :=
    H.connect x hx p hp.1 (hd.trans hnear)
  have hd0' : 0 ≤ ‖p - x‖ := norm_nonneg _
  refine ⟨Q, hQ0, hQD, hQdur.trans (H.timeBound_mono hd0' hd), ?_⟩
  have hend : Q.path Q.duration ∈ Fface := hQD ▸ hp
  have h4 : Q.duration ≤ H.timeBound d :=
    hQdur.trans (H.timeBound_mono hd0' hd)
  exact (Q.exposure_le_cube_div_twelve_of_end hend).trans
    (H.cube_div_twelve_le_exposureBound hd0 h4)

/-- Both endpoint connectors together have this exposure budget. -/
theorem projection_pair_exposureBound_eq {α : ℝ} (hα : 0 ≤ α) :
    2 * H.exposureBound (32 * Real.sqrt α) =
      (H.K^3 * Real.rpow 32 (3/4 : ℝ)/6) * Real.rpow α (3/8 : ℝ) := by
  have h32 : (0:ℝ) ≤ 32 := by norm_num
  have hsqrt : (0:ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  rw [H.exposureBound_eq (mul_nonneg h32 hsqrt)]
  have hsqrtpow : (Real.sqrt α)^(3/4 : ℝ) = α ^ (3/8 : ℝ) :=
    calc (√α)^(3/4 : ℝ)
        = ((√α)^(2 : ℝ))^(3/8 : ℝ) := by
          rw [← Real.rpow_mul (Real.sqrt_nonneg α)]
          norm_num
      _ = α ^ (3/8 : ℝ) := by rw [Real.rpow_two, Real.sq_sqrt hα]
  have hpow : (32 * Real.sqrt α)^(3/4 : ℝ) =
      (32:ℝ)^(3/4 : ℝ) * α^(3/8 : ℝ) := by
    rw [Real.mul_rpow h32 hsqrt, hsqrtpow]
  show 2 * (H.K^3/12 * (32 * Real.sqrt α)^(3/4 : ℝ)) =
    (H.K^3 * (32:ℝ)^(3/4 : ℝ)/6) * α^(3/8 : ℝ)
  rw [hpow]
  ring

end LocalSteering
end CZExposure
