module
public import RequestProject.AppendixE.PhysicalClockInverse
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Physical-time realization of a positive-cost segment

Reparametrize by the inverse physical clock: `x(s) = lift(ψ(s))`,
`v(s) = u(ψ(s))`.  The inverse derivative is `ψ' = c(x)` on `(0,D)`, so the
lifted ODE `ẋ = f_u/c` becomes `x' = vf(x,v)` a.e.; scalar FTC on each
coordinate upgrades this to the integral equation on all of `[0,D]`, and
the same FTC on `ψ` itself yields `∫₀^D c(x) = b − a` exactly — the
physical exposure is the retained exposure-length.  Disk controls and
arbitrary retained endpoints; no `Pulse` claim.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set
open scoped Topology

namespace PositiveExposureSegment

variable (S : PositiveExposureSegment)

def physicalPath : ℝ → State := S.liftedState ∘ S.clockInverseReal
def physicalControl : ℝ → ℂ := S.u ∘ S.clockInverseReal
def physicalExposure : ℝ :=
  ∫ s in (0 : ℝ)..S.duration, cost (S.physicalPath s)

theorem exists_lipschitz_physicalPath :
    ∃ K : NNReal, LipschitzWith K S.physicalPath := by
  obtain ⟨K, hK⟩ := S.exists_lipschitzOnWith_liftedState
  refine ⟨K, LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  have h1 : dist (S.liftedState (S.clockInverseReal s))
      (S.liftedState (S.clockInverseReal t)) ≤
      K * dist (S.clockInverseReal s) (S.clockInverseReal t) :=
    hK.dist_le_mul _ (S.clockInverseReal_mem s) _ (S.clockInverseReal_mem t)
  have h2 := S.lipschitz_clockInverseReal.dist_le_mul s t
  calc dist (S.physicalPath s) (S.physicalPath t)
      = dist (S.liftedState (S.clockInverseReal s))
          (S.liftedState (S.clockInverseReal t)) := rfl
    _ ≤ K * (1 * dist s t) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg K))
    _ = K * dist s t := by rw [one_mul]

theorem physicalPath_mem (s : ℝ) : S.physicalPath s ∈ Xset :=
  S.liftedState_mem (S.clockInverseReal_mem s)

theorem physicalPath_zero : S.physicalPath 0 = S.liftedState S.a := by
  simp [physicalPath, Function.comp_apply, S.clockInverseReal_zero]

theorem physicalPath_terminal :
    S.physicalPath S.duration = S.liftedState S.b := by
  simp [physicalPath, Function.comp_apply, S.clockInverseReal_terminal]

theorem measurable_physicalControl : Measurable S.physicalControl :=
  S.u_measurable.comp S.continuous_clockInverseReal.measurable

theorem physicalControl_bound (s : ℝ) : ‖S.physicalControl s‖ ≤ 1 :=
  S.u_bound _

theorem cost_physicalPath_pos (s : ℝ) : 0 < cost (S.physicalPath s) := by
  rw [show cost (S.physicalPath s) =
      cost (S.liftedState (S.clockInverseReal s)) from rfl,
    S.cost_liftedState (S.clockInverseReal_mem s)]
  exact S.cost_pos (S.clockInverseReal_mem s)

/-- Inverse-function theorem at interior times: `ψ' = c(x)`. -/
theorem hasDerivAt_clockInverseReal {s : ℝ}
    (hs : s ∈ Set.Ioo 0 S.duration) :
    HasDerivAt S.clockInverseReal (cost (S.physicalPath s)) s := by
  have hmem := S.clockInverseReal_mem s
  have hf : HasDerivAt S.clock (S.clockRate (S.clockInverseReal s))
      (S.clockInverseReal s) := S.hasDerivAt_clock hmem
  have hf' : S.clockRate (S.clockInverseReal s) ≠ 0 := by
    show (euclideanExposureCost (S.y (S.clockInverseReal s)))⁻¹ ≠ 0
    exact inv_ne_zero (S.cost_pos hmem).ne'
  have hg : ContinuousAt S.clockInverseReal s :=
    S.continuous_clockInverseReal.continuousAt
  have hfg : ∀ᶠ r in 𝓝 s, S.clock (S.clockInverseReal r) = r := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact S.clock_clockInverseReal (Set.Ioo_subset_Icc_self hr)
  have h := HasDerivAt.of_local_left_inverse hg hf hf' hfg
  have hder : (S.clockRate (S.clockInverseReal s))⁻¹ =
      cost (S.physicalPath s) := by
    show ((euclideanExposureCost (S.y (S.clockInverseReal s)))⁻¹)⁻¹ = _
    rw [inv_inv, ← S.cost_liftedState hmem]
    rfl
  rwa [hder] at h

theorem ae_hasDerivAt_clockInverseReal :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 S.duration)),
      HasDerivAt S.clockInverseReal (cost (S.physicalPath s)) s := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Ioo_ae_eq_Icc : Set.Ioo 0 S.duration =ᵐ[volume]
      Set.Icc 0 S.duration)] with _s hs hmem
  have hs' : _s ∈ Set.Ioo 0 S.duration := by
    show Set.Ioo 0 S.duration _s
    rw [hmem]
    exact hs
  exact S.hasDerivAt_clockInverseReal hs'

theorem ae_hasDerivAt_physicalPath :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 S.duration)),
      HasDerivAt S.physicalPath
        (vf (S.physicalPath s) (S.physicalControl s)) s := by
  filter_upwards [S.clockInverseReal_ae_transfer S.ae_hasDerivAt_liftedState,
    S.ae_hasDerivAt_clockInverseReal] with s hL hI
  have hne : cost (S.liftedState (S.clockInverseReal s)) ≠ 0 := by
    rw [S.cost_liftedState (S.clockInverseReal_mem s)]
    exact (S.cost_pos (S.clockInverseReal_mem s)).ne'
  exact (hL.scomp s hI).congr_deriv (by
    show cost (S.liftedState (S.clockInverseReal s)) •
        ((cost (S.liftedState (S.clockInverseReal s)))⁻¹ •
          vf (S.liftedState (S.clockInverseReal s))
            (S.u (S.clockInverseReal s))) =
      vf (S.physicalPath s) (S.physicalControl s)
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rfl)

/-- Scalar FTC bridge: a globally Lipschitz real function with prescribed
a.e. derivative is absolutely continuous, its a.e. derivative is interval
integrable, and the integral is the increment. -/
private theorem integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt
    {f g : ℝ → ℝ} {a b : ℝ} {K : NNReal}
    (hab : a ≤ b) (hf : LipschitzWith K f)
    (hg : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (g t) t) :
    IntervalIntegrable g volume a b ∧ (∫ t in a..b, g t) = f b - f a := by
  have hAC : AbsolutelyContinuousOnInterval f a b :=
    (hf.lipschitzOnWith.mono (Set.subset_univ _)).absolutelyContinuousOnInterval
  have hsub : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      HasDerivAt f (g t) t :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      Set.Ioc_subset_Icc_self hg
  rw [← Set.uIoc_of_le hab] at hsub
  have hEq : deriv f =ᵐ[volume.restrict (Set.uIoc a b)] g :=
    hsub.mono fun t ht => ht.deriv
  exact ⟨hAC.intervalIntegrable_deriv.congr_ae hEq,
    (intervalIntegral.integral_congr_ae_restrict hEq).symm.trans
      hAC.integral_deriv_eq_sub⟩

private theorem lipschitz_physicalPath_coord (i : Fin 8) :
    ∃ K : NNReal, LipschitzWith K (fun s => S.physicalPath s i) := by
  obtain ⟨K, hK⟩ := S.exists_lipschitz_physicalPath
  exact ⟨_, ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).lipschitz).comp hK⟩

private theorem ae_hasDerivAt_physicalPath_coord (i : Fin 8) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 S.duration)),
      HasDerivAt (fun r => S.physicalPath r i)
        (vf (S.physicalPath s) (S.physicalControl s) i) s :=
  S.ae_hasDerivAt_physicalPath.mono fun _ h => (hasDerivAt_pi.mp h) i

theorem intervalIntegrable_physicalVelocity (i : Fin 8) :
    IntervalIntegrable
      (fun s => vf (S.physicalPath s) (S.physicalControl s) i)
      volume 0 S.duration := by
  obtain ⟨K, hK⟩ := S.lipschitz_physicalPath_coord i
  exact (integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt
    S.duration_bounds.1.le hK
    (S.ae_hasDerivAt_physicalPath_coord i)).1

theorem physicalPath_integralEquation {s : ℝ}
    (hs : s ∈ Set.Icc 0 S.duration) (i : Fin 8) :
    S.physicalPath s i = S.physicalPath 0 i +
      ∫ r in (0 : ℝ)..s, vf (S.physicalPath r) (S.physicalControl r) i := by
  obtain ⟨K, hK⟩ := S.lipschitz_physicalPath_coord i
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 s)),
      HasDerivAt (fun t => S.physicalPath t i)
        (vf (S.physicalPath r) (S.physicalControl r) i) r :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc_right hs.2) (S.ae_hasDerivAt_physicalPath_coord i)
  have h := (integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt hs.1 hK hae).2
  linarith

theorem intervalIntegrable_cost_physicalPath :
    IntervalIntegrable (fun s => cost (S.physicalPath s))
      volume 0 S.duration := by
  have h := integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt
    S.duration_bounds.1.le S.lipschitz_clockInverseReal
    S.ae_hasDerivAt_clockInverseReal
  exact h.1

theorem integral_cost_physicalPath {s : ℝ} (hs : s ∈ Set.Icc 0 S.duration) :
    (∫ r in (0 : ℝ)..s, cost (S.physicalPath r)) =
      S.clockInverseReal s - S.a := by
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 s)),
      HasDerivAt S.clockInverseReal (cost (S.physicalPath r)) r :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc_right hs.2) S.ae_hasDerivAt_clockInverseReal
  have h := (integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt hs.1
    S.lipschitz_clockInverseReal hae).2
  rw [S.clockInverseReal_zero] at h
  exact h

theorem physicalExposure_eq : S.physicalExposure = S.b - S.a := by
  rw [physicalExposure,
    S.integral_cost_physicalPath
      (Set.right_mem_Icc.mpr S.duration_bounds.1.le),
    S.clockInverseReal_terminal]

/-- A supplied positive-cost segment realizes a finite physical-time
trajectory: disk controls, integral-form dynamics everywhere on `[0,D]`,
domain membership, and exact physical exposure `b − a`. -/
theorem exists_physical_realization :
    ∃ D : ℝ, 0 < D ∧ D ≤ (S.b - S.a) / S.cutoff ∧
      ∃ x : ℝ → State, ∃ u : ℝ → ℂ,
        (∃ K : NNReal, LipschitzWith K x) ∧
        Measurable u ∧ (∀ s, ‖u s‖ ≤ 1) ∧
        (∀ s ∈ Set.Icc 0 D, x s ∈ Xset) ∧
        x 0 = S.liftedState S.a ∧ x D = S.liftedState S.b ∧
        (∀ i : Fin 8, IntervalIntegrable
          (fun s => vf (x s) (u s) i) volume 0 D) ∧
        (∀ s ∈ Set.Icc 0 D, ∀ i : Fin 8,
          x s i = x 0 i + ∫ r in (0 : ℝ)..s, vf (x r) (u r) i) ∧
        (∫ s in (0 : ℝ)..D, cost (x s)) = S.b - S.a := by
  refine ⟨S.duration, S.duration_bounds.1, S.duration_bounds.2,
    S.physicalPath, S.physicalControl, S.exists_lipschitz_physicalPath,
    S.measurable_physicalControl, S.physicalControl_bound,
    fun s _ => S.physicalPath_mem s,
    S.physicalPath_zero, S.physicalPath_terminal,
    S.intervalIntegrable_physicalVelocity,
    fun s hs => S.physicalPath_integralEquation hs,
    S.physicalExposure_eq⟩

end PositiveExposureSegment

end CZExposure
