module
public import RequestProject.AppendixE.ExposureCoords

/-!
# Control averaging for the `B`-field (Appendix E 2, Step 4)

The velocity `u ↦ B(y, u)` is `ℝ`-linear in the control on the whole ambient space:
off the zero-cost face it is a scalar multiple of `DJ(x) f_u(x)` with `f_u` real-linear in
`u`, and on the face it is identically `0`. Linear packaging lets Bochner
integration commute with `B`, so the balance integrand of a control marginal is
the integrand evaluated at the mean control.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- The vector field is additive in the control. -/
theorem vf_add_control (x : State) (u v : ℂ) :
    vf x (u + v) = vf x u + vf x v := by
  funext i
  fin_cases i <;> simp [vf, fC, mul_add, add_mul, map_add]

/-- The vector field is real-homogeneous in the control: conjugation is real
linear, so a real scalar passes through both `u` and `ū`. -/
theorem vf_smul_control (x : State) (a : ℝ) (u : ℂ) :
    vf x (a • u) = a • vf x u := by
  funext i
  fin_cases i <;>
    simp [vf, fC, Complex.real_smul, map_mul, Complex.conj_ofReal, Pi.smul_apply,
      smul_eq_mul] <;>
    ring

/-- The control-to-velocity map as a real continuous linear map. -/
def vfControlCLM (x : State) : ℂ →L[ℝ] State :=
  ({ toFun := vf x
     map_add' := vf_add_control x
     map_smul' := vf_smul_control x } : ℂ →ₗ[ℝ] State).toContinuousLinearMap

@[simp] theorem vfControlCLM_apply (x : State) (u : ℂ) :
    vfControlCLM x u = vf x u := rfl

/-- The `B`-field as a real continuous linear map of the control, valid on the
whole ambient space: it is `0` exactly where `B` is `0`. -/
def BfieldControlCLM (y : Fin 11 → ℝ) : ℂ →L[ℝ] (Fin 11 → ℝ) :=
  if 0 < y 2 then
    let x : State := fun i => y (i.succ.succ.succ) / y 2
    ((cost x)⁻¹ • fderiv ℝ Jmap x).comp (vfControlCLM x)
  else 0

@[simp] theorem BfieldControlCLM_apply (y : Fin 11 → ℝ) (u : ℂ) :
    BfieldControlCLM y u = Bfield y u := by
  unfold BfieldControlCLM Bfield
  split_ifs with h
  · rfl
  · rfl

/-- The mean velocity is the velocity of the mean control, on every ambient `y`
(including the zero-cost face, where both sides are `0`). -/
theorem integral_Bfield (y : Fin 11 → ℝ) {μ : Measure ℂ}
    (hμ : Integrable (fun u : ℂ => u) μ) :
    (∫ u, Bfield y u ∂μ) = Bfield y (∫ u, u ∂μ) := by
  have h := (BfieldControlCLM y).integral_comp_comm (φ := fun u : ℂ => u) hμ
  simpa only [BfieldControlCLM_apply] using h

/-- A control marginal supported on the closed unit disk has an integrable
identity. -/
theorem integrable_control_of_disk_support {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hu : ∀ᵐ u ∂μ, ‖u‖ ≤ 1) : Integrable (fun u : ℂ => u) μ :=
  (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable hu

/-- The mean of a probability measure on the closed unit disk lies in the disk. -/
theorem norm_mean_control_le_one {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hu : ∀ᵐ u ∂μ, ‖u‖ ≤ 1) : ‖∫ u, u ∂μ‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) hu
  rwa [probReal_univ, mul_one] at h

/-- Linearity lifts through the test-function derivative: the balance integrand
of a control marginal equals the integrand at the mean control. The derivative
`fderiv ℝ ψ y` is a continuous linear map for every `ψ`, differentiable or not. -/
theorem integral_balance_Bfield (y : Fin 11 → ℝ) (ψ : (Fin 11 → ℝ) → ℝ)
    {μ : Measure ℂ} (hμ : Integrable (fun u : ℂ => u) μ) :
    (∫ u, fderiv ℝ ψ y (Bfield y u) ∂μ) =
      fderiv ℝ ψ y (Bfield y (∫ u, u ∂μ)) := by
  have h := ((fderiv ℝ ψ y).comp (BfieldControlCLM y)).integral_comp_comm
    (φ := fun u : ℂ => u) hμ
  simpa only [ContinuousLinearMap.comp_apply, BfieldControlCLM_apply] using h

end CZExposure
