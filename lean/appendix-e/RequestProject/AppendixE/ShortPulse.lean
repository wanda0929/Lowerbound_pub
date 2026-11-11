module
public import RequestProject.AppendixE.ControlTranslation
public import RequestProject.AppendixE.PhysicalConcatenation

/-! Exact constant-phase pulses, including signed times. Negative time is
implemented by the opposite control and positive physical duration. -/
@[expose] public section
noncomputable section
namespace CZExposure.ShortPulse
open MeasureTheory ControlTranslation ControlLie

def orbit (u : ℂ) (t : ℝ) : State :=
  ![Real.cos (t / 2), 0, -u.im * Real.sin (t / 2), -u.re * Real.sin (t / 2),
    Real.cos (t * (Real.sqrt 2 / 2)), 0,
    -u.im * Real.sin (t * (Real.sqrt 2 / 2)),
    -u.re * Real.sin (t * (Real.sqrt 2 / 2))]

@[simp] theorem orbit_zero (u : ℂ) : orbit u 0 = x0 := by
  simp [orbit, x0]

private theorem unit_coords {u : ℂ} (hu : ‖u‖ = 1) : u.re ^ 2 + u.im ^ 2 = 1 := by
  have h := Complex.sq_norm u
  rw [hu] at h
  simp only [Complex.normSq_apply] at h
  nlinarith [h]

theorem orbit_mem {u : ℂ} (hu : ‖u‖ = 1) (t : ℝ) : orbit u t ∈ Xset := by
  rw [mem_Xset_iff_normalization]
  funext i
  have h := unit_coords hu
  fin_cases i <;> simp [normalization, normal, orbit]
  · nlinarith [Real.cos_sq_add_sin_sq (t / 2),
      congrArg (fun z => z * Real.sin (t / 2) ^ 2) h]
  · nlinarith [Real.cos_sq_add_sin_sq (t * (Real.sqrt 2 / 2)),
      congrArg (fun z => z * Real.sin (t * (Real.sqrt 2 / 2)) ^ 2) h]

theorem orbit_deriv {u : ℂ} (hu : ‖u‖ = 1) (t : ℝ) :
    HasDerivAt (orbit u) (vf (orbit u t) u) t := by
  have hc := ((hasDerivAt_id t).div_const 2).cos
  have hs := ((hasDerivAt_id t).div_const 2).sin
  have hc2 := ((hasDerivAt_id t).mul_const (Real.sqrt 2 / 2)).cos
  have hs2 := ((hasDerivAt_id t).mul_const (Real.sqrt 2 / 2)).sin
  have h := unit_coords hu
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  case' «0» => convert hc using 1
  case' «1» => convert hasDerivAt_const t (0 : ℝ) using 1
  case' «2» => convert hs.const_mul (-u.im) using 1
  case' «3» => convert hs.const_mul (-u.re) using 1
  case' «4» => convert hc2 using 1
  case' «5» => convert hasDerivAt_const t (0 : ℝ) using 1
  case' «6» => convert hs2.const_mul (-u.im) using 1
  case' «7» => convert hs2.const_mul (-u.re) using 1
  all_goals simp [orbit, vf_eq_act, act]
  all_goals ring_nf
  all_goals first
    | linear_combination -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * t * (1/2)) / 2) * h
    | linear_combination -(Real.sin (t * (1/2)) / 2) * h

def positive (u : ℂ) (hu : ‖u‖ = 1) (d : ℝ) (hd : 0 ≤ d) : PhysicalSegment := by
  have hc : Continuous (orbit u) :=
    continuous_iff_continuousAt.mpr fun t => (orbit_deriv hu t).continuousAt
  have hv : Continuous (fun t => vf (orbit u t) u) :=
    continuous_vf.comp (hc.prodMk continuous_const)
  exact {
    duration := d
    duration_nonneg := hd
    path := orbit u
    control := fun _ => u
    control_measurable := measurable_const
    control_bound := fun _ _ => hu.le
    path_mem := fun t _ => orbit_mem hu t
    velocity_integrable := hv.intervalIntegrable _ _
    integralEquation := fun s _ => by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => orbit_deriv hu t) (hv.intervalIntegrable _ _)]
      abel }

theorem orbit_neg (u : ℂ) (t : ℝ) : orbit (-u) (-t) = orbit u t := by
  simp [orbit, neg_div, neg_mul, Real.cos_neg, Real.sin_neg]

theorem orbit_inverse (u : ℂ) (t : ℝ) : orbit u (-t) = inverse (orbit u t) := by
  simp [orbit, inverse, neg_div, neg_mul, Real.cos_neg, Real.sin_neg]

theorem orbit_contDiff (u : ℂ) : ContDiff ℝ ⊤ (orbit u) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [orbit] <;> fun_prop

def signed (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) : PhysicalSegment :=
  if ht : 0 ≤ t then positive u hu t ht
  else positive (-u) (by simpa using hu) (-t) (by linarith)

@[simp] theorem signed_duration (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) :
    (signed u hu t).duration = |t| := by
  by_cases ht : 0 ≤ t
  · simp [signed, ht, positive, abs_of_nonneg ht]
  · simp [signed, ht, positive, abs_of_neg (lt_of_not_ge ht)]

@[simp] theorem signed_initial (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) :
    (signed u hu t).path 0 = x0 := by
  by_cases ht : 0 ≤ t <;> simp [signed, ht, positive]

@[simp] theorem signed_terminal (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) :
    (signed u hu t).path (signed u hu t).duration = orbit u t := by
  by_cases ht : 0 ≤ t <;> simp [signed, ht, positive, orbit_neg]

theorem signed_unit (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) :
    (signed u hu t).UnitControl := by
  intro s hs
  by_cases ht : 0 ≤ t <;> simp [signed, ht, positive, hu]

end CZExposure.ShortPulse
