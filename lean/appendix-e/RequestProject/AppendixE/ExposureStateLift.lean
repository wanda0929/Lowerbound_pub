module
public import RequestProject.AppendixE.ExposureCurrent

/-!
# Physical-state lift from exposure coordinates

`exposureStateLift` recovers the 8-dimensional `State` from the 11 exposure
coordinates when `y 2 = c(x)² > 0`: `x_i = y_{i+3} / y 2`.  It is `C¹` on
`y 2 ≠ 0`, and differentiating the local identity `lift ∘ J = id` gives
`D lift (J x) ∘ DJ x = id`.  Consequently lifting `y' = B(y,u)` yields
`x' = f_u(x) / c(x)`.  The running cost is `√(y 2)`, not `y 2`.  The lift is
a total function (real division at `y 2 = 0`); inverse claims are only on
`0 < y 2`.  No Pulse reconstruction claim.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set
open scoped Topology

/-- State recovered from exposure coordinates: `x_i = y_{i+3} / y 2`.
Total function; meaningful only where `y 2 > 0`. -/
def exposureStateLift (y : Fin 11 → ℝ) : State :=
  fun i => y i.succ.succ.succ / y 2

/-- State recovered from the Euclidean ambient space of exposure
coordinates. -/
def euclideanStateLift (z : ExposureEuclidean) : State :=
  exposureStateLift (exposureEuclideanEquiv.symm z)

/-- Running cost read from the exposure coordinates, not squared cost. -/
def euclideanExposureCost (z : ExposureEuclidean) : ℝ :=
  Real.sqrt ((exposureEuclideanEquiv.symm z) 2)

theorem exposureStateLift_Jmap {x : State} (hc : cost x ≠ 0) :
    exposureStateLift (Jmap x) = x := by
  funext i
  simp only [exposureStateLift, Jmap_two]
  have hnum : Jmap x i.succ.succ.succ = cost x ^ 2 * x i := by
    simp only [Jmap, Fin.cons_succ]
  rw [hnum]
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hc)

theorem contDiffAt_exposureStateLift {y : Fin 11 → ℝ} (hy : y 2 ≠ 0) :
    ContDiffAt ℝ 1 exposureStateLift y := by
  apply contDiffAt_pi.mpr
  intro i
  have hf : ContDiffAt ℝ 1 (fun y : Fin 11 → ℝ => y i.succ.succ.succ) y := by
    fun_prop
  have hg : ContDiffAt ℝ 1 (fun y : Fin 11 → ℝ => y 2) y := by fun_prop
  exact hf.div hg hy

theorem differentiableAt_exposureStateLift {y : Fin 11 → ℝ} (hy : y 2 ≠ 0) :
    DifferentiableAt ℝ exposureStateLift y :=
  (contDiffAt_exposureStateLift hy).differentiableAt one_ne_zero

theorem fderiv_exposureStateLift_Jmap {x : State} (hc : cost x ≠ 0)
    (w : State) :
    fderiv ℝ exposureStateLift (Jmap x) (fderiv ℝ Jmap x w) = w := by
  have hne : ∀ᶠ x' in 𝓝 x, cost x' ≠ 0 :=
    (contDiff_cost.continuous.continuousAt).eventually_ne hc
  have heq : (exposureStateLift ∘ Jmap) =ᶠ[𝓝 x] id := by
    filter_upwards [hne] with x' hx'
    exact exposureStateLift_Jmap hx'
  have hid : HasFDerivAt (exposureStateLift ∘ Jmap)
      (ContinuousLinearMap.id ℝ State) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq heq
  have hJ := (contDiff_Jmap.differentiable (by simp) x).hasFDerivAt
  have hLift := (differentiableAt_exposureStateLift (y := Jmap x)
    (by rw [Jmap_two]; exact pow_ne_zero 2 hc)).hasFDerivAt
  have hcomp := hLift.comp x hJ
  have heqCLM := hcomp.unique hid
  have := congrArg (fun L : State →L[ℝ] State => L w) heqCLM
  simpa using this

theorem exposureStateLift_mem_Xset {y : Fin 11 → ℝ}
    (hy : y ∈ Yset) (hpos : 0 < y 2) : exposureStateLift y ∈ Xset := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Jmap_two] at hpos
  have hc : 0 < cost x := by nlinarith [cost_nonneg x]
  rw [exposureStateLift_Jmap hc.ne']
  exact hx

theorem Jmap_exposureStateLift {y : Fin 11 → ℝ}
    (hy : y ∈ Yset) (hpos : 0 < y 2) : Jmap (exposureStateLift y) = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Jmap_two] at hpos
  have hc : 0 < cost x := by nlinarith [cost_nonneg x]
  rw [exposureStateLift_Jmap hc.ne']

theorem cost_exposureStateLift {y : Fin 11 → ℝ}
    (hy : y ∈ Yset) (hpos : 0 < y 2) :
    cost (exposureStateLift y) = Real.sqrt (y 2) := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Jmap_two] at hpos ⊢
  have hc : 0 < cost x := by nlinarith [cost_nonneg x]
  rw [exposureStateLift_Jmap hc.ne', Real.sqrt_sq (cost_nonneg x)]

theorem fderiv_exposureStateLift_Bfield {y : Fin 11 → ℝ}
    (hy : y ∈ Yset) (hpos : 0 < y 2) (u : ℂ) :
    fderiv ℝ exposureStateLift y (Bfield y u) =
      (cost (exposureStateLift y))⁻¹ • vf (exposureStateLift y) u := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Jmap_two] at hpos
  have hc : 0 < cost x := by nlinarith [cost_nonneg x]
  rw [exposureStateLift_Jmap hc.ne', Bfield_Jmap_of_pos hc u,
    (fderiv ℝ exposureStateLift (Jmap x)).map_smul,
    fderiv_exposureStateLift_Jmap hc.ne' (vf x u)]

theorem continuous_euclideanExposureCost : Continuous euclideanExposureCost :=
  Real.continuous_sqrt.comp
    ((continuous_apply (2 : Fin 11)).comp exposureEuclideanEquiv.symm.continuous)

theorem euclideanStateLift_spec {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) (hpos : 0 < euclideanExposureCost z) :
    euclideanStateLift z ∈ Xset ∧
      exposureEuclideanEquiv (Jmap (euclideanStateLift z)) = z ∧
      cost (euclideanStateLift z) = euclideanExposureCost z := by
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [euclideanExposureCost, exposureEuclideanEquiv.symm_apply_apply]
    at hpos ⊢
  rw [Real.sqrt_pos] at hpos
  simp only [euclideanStateLift, exposureEuclideanEquiv.symm_apply_apply]
  exact ⟨exposureStateLift_mem_Xset hy hpos,
    congrArg exposureEuclideanEquiv (Jmap_exposureStateLift hy hpos),
    cost_exposureStateLift hy hpos⟩

theorem contDiffAt_euclideanStateLift {z : ExposureEuclidean}
    (hpos : 0 < euclideanExposureCost z) :
    ContDiffAt ℝ 1 euclideanStateLift z :=
  (contDiffAt_exposureStateLift
    (ne_of_gt (Real.sqrt_pos.mp hpos))).comp z
    exposureEuclideanEquiv.symm.toContinuousLinearMap.contDiff.contDiffAt

theorem differentiableAt_euclideanStateLift {z : ExposureEuclidean}
    (hpos : 0 < euclideanExposureCost z) :
    DifferentiableAt ℝ euclideanStateLift z :=
  (contDiffAt_euclideanStateLift hpos).differentiableAt one_ne_zero

theorem fderiv_euclideanStateLift_Bfield {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) (hpos : 0 < euclideanExposureCost z)
    (u : ℂ) :
    fderiv ℝ euclideanStateLift z (euclideanBfield z u) =
      (cost (euclideanStateLift z))⁻¹ • vf (euclideanStateLift z) u := by
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [euclideanExposureCost, exposureEuclideanEquiv.symm_apply_apply]
    at hpos
  have hy2 : y 2 ≠ 0 := (Real.sqrt_pos.mp hpos).ne'
  have hd : HasFDerivAt euclideanStateLift
      ((fderiv ℝ exposureStateLift y).comp
        exposureEuclideanEquiv.symm.toContinuousLinearMap)
      (exposureEuclideanEquiv y) :=
    (differentiableAt_exposureStateLift hy2).hasFDerivAt.comp _
      exposureEuclideanEquiv.symm.toContinuousLinearMap.hasFDerivAt
  calc fderiv ℝ euclideanStateLift (exposureEuclideanEquiv y)
        (euclideanBfield (exposureEuclideanEquiv y) u)
      = fderiv ℝ exposureStateLift y (Bfield y u) := by
        rw [euclideanBfield_equiv, hd.fderiv]
        simp
    _ = (cost (euclideanStateLift (exposureEuclideanEquiv y)))⁻¹ •
          vf (euclideanStateLift (exposureEuclideanEquiv y)) u := by
        rw [fderiv_exposureStateLift_Bfield hy (Real.sqrt_pos.mp hpos) u]
        rfl

theorem hasDerivAt_lifted_exposure_path {y : ℝ → ExposureEuclidean} {t : ℝ}
    (u : ℂ) (hy : y t ∈ euclideanExposureDomain)
    (hpos : 0 < euclideanExposureCost (y t))
    (hode : HasDerivAt y (euclideanBfield (y t) u) t) :
    HasDerivAt (fun r => euclideanStateLift (y r))
      ((cost (euclideanStateLift (y t)))⁻¹ •
        vf (euclideanStateLift (y t)) u) t := by
  have h := (differentiableAt_euclideanStateLift hpos).hasFDerivAt
    |>.comp_hasDerivAt t hode
  rwa [fderiv_euclideanStateLift_Bfield hy hpos u] at h

end CZExposure
