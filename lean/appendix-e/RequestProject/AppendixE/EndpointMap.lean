module
public import RequestProject.AppendixE.SignedRootPulse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! The six independent pulse parameters and their local inverse. -/
@[expose] public section
noncomputable section
namespace CZExposure.EndpointMap
open ControlLie PulseWords PulseExpansion SignedRootPulse
open scoped Topology

/-- A linear change of the usual six imaginary/excited-state chart coordinates.
It makes the bracket basis the coordinate basis at the origin. -/
def chartLM : State →ₗ[ℝ] Params where
  toFun x := bracketCoordinates ![-x 3, -x 2, x 1, -x 7, -x 6, x 5]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [bracketCoordinates] <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp [bracketCoordinates] <;> ring

def chart : State →L[ℝ] Params := chartLM.toContinuousLinearMap

theorem chart_origin : chart x0 = 0 := by
  ext i
  fin_cases i <;> simp [chart, chartLM, bracketCoordinates, x0]

theorem chart_bracket (i : Fin 6) :
    chart (bracketFields i x0) = Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [chart, chartLM, bracketCoordinates, bracketFields,
      driveX_eq_act, driveY_eq_act, bracket2_eq_act, bracket3X_eq_act,
      bracket3Y_eq_act, bracket4_eq_act, act, x0] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

/-- The head acts last; the six-word list below is in reverse chronological order. -/
def state : List (Fin 6) → Params → State
  | [], _ => x0
  | i :: is, p => curve (six i) (orders i) (p i) (state is p)

def differential (is : List (Fin 6)) : Params →L[ℝ] State :=
  (is.map fun i => (ContinuousLinearMap.proj i).smulRight (bracketFields i x0)).sum

theorem state_zero (is : List (Fin 6)) : state is 0 = x0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [state, six_zero, ih]

theorem state_contDiff (is : List (Fin 6)) : ContDiff ℝ 1 (state is) := by
  induction is with
  | nil => exact contDiff_const
  | cons i is ih =>
    exact ((six_contDiff i).comp (ContinuousLinearMap.proj i).contDiff).clm_apply ih

theorem state_deriv (is : List (Fin 6)) :
    HasFDerivAt (state is) (differential is) 0 := by
  induction is with
  | nil => simpa only [state, differential, List.map_nil, List.sum_nil] using
      hasFDerivAt_const (𝕜 := ℝ) x0 (0 : Params)
  | cons i is ih =>
    have hc := (six_deriv_zero i).hasFDerivAt.comp (0 : Params)
      (ContinuousLinearMap.proj i : Params →L[ℝ] ℝ).hasFDerivAt
    have h := hc.clm_apply ih
    convert h using 1
    ext p j
    simp [differential, six_zero, state_zero, leading_field, add_comm]

def indices : List (Fin 6) := [5, 4, 3, 2, 1, 0]
def endpoint (p : Params) : State := state indices p
def coordinates (p : Params) : Params := chart (endpoint p)

theorem coordinates_zero : coordinates 0 = 0 := by
  simp [coordinates, endpoint, state_zero, chart_origin]

theorem coordinates_contDiff : ContDiff ℝ 1 coordinates :=
  chart.contDiff.comp (state_contDiff indices)

theorem chart_differential : chart.comp (differential indices) =
    ContinuousLinearMap.id ℝ Params := by
  ext p j
  simp [differential, indices, chart_bracket]
  fin_cases j <;> simp

theorem coordinates_deriv :
    HasFDerivAt coordinates (ContinuousLinearMap.id ℝ Params) 0 := by
  simpa only [chart_differential] using
    chart.hasFDerivAt.comp 0 (state_deriv indices)

theorem coordinates_strictDeriv :
    HasStrictFDerivAt coordinates
      (ContinuousLinearEquiv.refl ℝ Params : Params →L[ℝ] Params) 0 :=
  coordinates_contDiff.contDiffAt.hasStrictFDerivAt' coordinates_deriv (by decide)

/-- The inverse is supplied by the inverse function theorem, not an extra hypothesis. -/
def parameters : Params → Params :=
  coordinates_strictDeriv.localInverse coordinates (ContinuousLinearEquiv.refl ℝ Params) 0

theorem parameters_zero : parameters 0 = 0 := by
  simpa only [coordinates_zero] using coordinates_strictDeriv.localInverse_apply_image

theorem parameters_right_inverse :
    ∀ᶠ q in 𝓝 (0 : Params), coordinates (parameters q) = q := by
  simpa only [coordinates_zero] using coordinates_strictDeriv.eventually_right_inverse

theorem parameters_left_inverse :
    ∀ᶠ p in 𝓝 (0 : Params), parameters (coordinates p) = p :=
  coordinates_strictDeriv.eventually_left_inverse

theorem parameters_deriv :
    HasStrictFDerivAt parameters (ContinuousLinearMap.id ℝ Params) 0 := by
  simpa only [coordinates_zero] using coordinates_strictDeriv.to_localInverse

theorem parameters_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ q in 𝓝 (0 : Params), ‖parameters q‖ ≤ C * ‖q‖ := by
  have h := parameters_deriv.hasFDerivAt.isBigO_sub
  rcases h.exists_pos with ⟨C, hC, hb⟩
  exact ⟨C, hC, by simpa [parameters_zero] using hb.bound⟩

theorem origin_mem : x0 ∈ Xset := by
  rw [mem_Xset_iff_normalization]
  ext i
  fin_cases i <;> simp [normalization, normal, x0]

theorem curve_mem (i : Fin 6) (s : ℝ) {x : State} (hx : x ∈ Xset) :
    curve (six i) (orders i) s x ∈ Xset := by
  let P := (physical (six i) (orders i) s x hx).val
  rw [← physical_terminal (six i) (orders i) s x hx]
  exact P.path_mem P.duration ⟨P.duration_nonneg, le_rfl⟩

theorem state_mem (is : List (Fin 6)) (p : Params) : state is p ∈ Xset := by
  induction is with
  | nil => exact origin_mem
  | cons i is ih => exact curve_mem i (p i) ih

set_option maxHeartbeats 2000000 in
/-- The omitted real ground-state coordinates are determined by normalization
on the positive-real-part chart. -/
theorem chart_injective {x y : State} (hx : x ∈ Xset) (hy : y ∈ Xset)
    (hx0 : 0 < x 0) (hy0 : 0 < y 0) (hx4 : 0 < x 4) (hy4 : 0 < y 4)
    (h : chart x = chart y) : x = y := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp [chart, chartLM, bracketCoordinates] at h0 h1 h2 h3 h4 h5
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have e3 : x 3 = y 3 := by linarith
  have e2 : x 2 = y 2 := by linarith
  have e1 : x 1 = y 1 := by linarith
  have e7 : x 7 = y 7 := by
    apply (mul_left_cancel₀ hs)
    linarith
  have e6 : x 6 = y 6 := by
    apply (mul_left_cancel₀ hs)
    linarith
  have e5 : x 5 = y 5 := by linarith
  have nx := (mem_Xset_iff_normalization x).mp hx
  have ny := (mem_Xset_iff_normalization y).mp hy
  have nx0 := congrFun nx 0
  have ny0 := congrFun ny 0
  have nx1 := congrFun nx 1
  have ny1 := congrFun ny 1
  simp [normalization, normal, e1, e2, e3, e5, e6, e7] at nx0 ny0 nx1 ny1
  have e0 : x 0 = y 0 := by nlinarith
  have e4 : x 4 = y 4 := by nlinarith
  ext i
  fin_cases i <;> assumption

theorem exact_endpoint :
    ∀ᶠ y in 𝓝 x0, y ∈ Xset → endpoint (parameters (chart y)) = y := by
  have hp : ContinuousAt parameters 0 := parameters_deriv.continuousAt
  have he : ContinuousAt endpoint 0 := (state_contDiff indices).continuous.continuousAt
  have hc : ContinuousAt chart x0 := chart.continuous.continuousAt
  have ht : ContinuousAt (fun y => endpoint (parameters (chart y))) x0 := by
    exact (he.comp_of_eq hp parameters_zero).comp_of_eq hc chart_origin
  have ht0 : endpoint (parameters (chart x0)) = x0 := by
    simp [chart_origin, parameters_zero, endpoint, state_zero]
  have hpos0 : Set.Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) := isOpen_Ioi.mem_nhds (by norm_num)
  have hy0 : ∀ᶠ y : State in 𝓝 x0, 0 < y 0 := by
    exact (continuous_apply 0).continuousAt.preimage_mem_nhds (by simpa [x0] using hpos0)
  have hy4 : ∀ᶠ y : State in 𝓝 x0, 0 < y 4 := by
    exact (continuous_apply 4).continuousAt.preimage_mem_nhds (by simpa [x0] using hpos0)
  have hz0 := ht (by simpa [ht0] using hy0)
  have hz4 := ht (by simpa [ht0] using hy4)
  have hi := hc (by simpa [chart_origin] using parameters_right_inverse)
  filter_upwards [hy0, hy4, hz0, hz4, hi] with y hy0 hy4 hz0 hz4 hi
  intro hy
  exact chart_injective (state_mem indices _) hy hz0 hy0 hz4 hy4 hi

end CZExposure.EndpointMap
