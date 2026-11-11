module
public import RequestProject.AppendixE.ExposureClockTransport
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# The a.e. ODE for the exposure-time curve (Appendix E support)

Using the exact inverse-clock measure transport of
`ExposureClockTransport.lean`, the Lebesgue differentiation theorem for the
clock, `HasDerivAt.of_local_left_inverse`, and the vector-valued chain rule
`HasDerivAt.scomp`, we prove:

* `HasDerivAt clockInverseReal ‖v‖` a.e. on the exposure interval;
* conditional on `γ.IsDirectedBy F` (the a.e. tangent identity, itself still
  an external input), the reparameterized curve satisfies
  `d/dt exposurePathReal = euclideanBfield (exposurePathReal t) (exposureControl t)`
  for a.e. `t` in `[0, exposureTime.toReal]`;
* `exists_exposure_time_trajectory` packages this as an exposure-time
  trajectory from a supplied decomposition + arc realization + tangency.

This is NOT a physical `Pulse`, does not assert finite physical duration
(`exposureTime` is a weighted cost), and does not close `Cstar ≤ pRelaxed`.
Decomposition existence, arc realization, and tangent alignment remain open
geometric inputs.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set intervalIntegral
open scoped Topology

namespace EuclideanArc

/-- The reparameterized curve as a total function on ℝ (constant extension
through the clamped inverse outside `[0,T]`). -/
def exposurePathReal (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    ℝ → ExposureEuclidean :=
  γ.path ∘ γ.clockInverseReal F hfinite hdom

/-- The averaged control evaluated along the exposure-time curve. -/
def exposureControl (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    ℝ → ℂ :=
  F.control ∘ γ.exposurePathReal F hfinite hdom

theorem exposurePathReal_of_mem (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (γ.exposureTime F).toReal) :
    γ.exposurePathReal F hfinite hdom t =
      γ.reparameterizedPath F hfinite hdom ⟨t, ht⟩ := by
  show γ.path (γ.clockInverseReal F hfinite hdom t) =
    γ.path (γ.clockInverse F hfinite hdom ⟨t, ht⟩ : ℝ)
  rw [γ.clockInverseReal_of_mem F hfinite hdom ht]

theorem exists_lipschitz_exposurePathReal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    ∃ K : NNReal, 0 < K ∧
      LipschitzWith K (γ.exposurePathReal F hfinite hdom) := by
  obtain ⟨K, hK, hbound⟩ := F.velocity_bounded
  refine ⟨K, hK, ?_⟩
  have hcomp := γ.lipschitz.comp
    (γ.lipschitz_clockInverseReal F hfinite hdom hK
      (fun s hs => hbound _ (hdom hs)))
  exact hcomp.weaken (one_mul K).le

theorem exposurePathReal_mem_domain (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : ℝ) :
    γ.exposurePathReal F hfinite hdom t ∈ euclideanExposureDomain :=
  hdom (γ.clockInverseReal_mem F hfinite hdom t)

theorem exposurePathReal_zero (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    γ.exposurePathReal F hfinite hdom 0 = γ.path 0 := by
  rw [γ.exposurePathReal_of_mem F hfinite hdom
      (Set.left_mem_Icc.mpr ENNReal.toReal_nonneg)]
  exact γ.reparameterizedPath_zero F hfinite hdom

theorem exposurePathReal_terminal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    γ.exposurePathReal F hfinite hdom (γ.exposureTime F).toReal = γ.path γ.length := by
  rw [γ.exposurePathReal_of_mem F hfinite hdom
      (Set.right_mem_Icc.mpr ENNReal.toReal_nonneg)]
  exact γ.reparameterizedPath_terminal F hfinite hdom

theorem measurable_exposureControl (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    Measurable (γ.exposureControl F hfinite hdom) :=
  F.measurable_control.comp
    (γ.lipschitz.continuous.comp
      (γ.continuous_clockInverseReal F hfinite hdom)).measurable

theorem exposureControl_bound (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : ℝ) :
    ‖γ.exposureControl F hfinite hdom t‖ ≤ 1 :=
  F.control_bound _

theorem hasDerivAt_clockInverseReal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (γ.exposureTime F).toReal)
    (hc : HasDerivAt (γ.exposureClock F)
      (γ.inverseSpeed F (γ.clockInverseReal F hfinite hdom t))
      (γ.clockInverseReal F hfinite hdom t))
    (hv : F.velocity (γ.path (γ.clockInverseReal F hfinite hdom t)) ≠ 0) :
    HasDerivAt (γ.clockInverseReal F hfinite hdom)
      ‖F.velocity (γ.path (γ.clockInverseReal F hfinite hdom t))‖ t := by
  have hcont : ContinuousAt (γ.clockInverseReal F hfinite hdom) t :=
    (γ.continuous_clockInverseReal F hfinite hdom).continuousAt
  have hne : γ.inverseSpeed F (γ.clockInverseReal F hfinite hdom t) ≠ 0 :=
    inv_ne_zero (norm_pos_iff.mpr hv).ne'
  have hfg : ∀ᶠ y in 𝓝 t,
      γ.exposureClock F (γ.clockInverseReal F hfinite hdom y) = y := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact γ.exposureClock_clockInverseReal F hfinite hdom
      (Set.Ioo_subset_Icc_self hy)
  have h := hc.of_local_left_inverse hcont hne hfg
  simpa only [EuclideanArc.inverseSpeed, inv_inv] using h

theorem ae_hasDerivAt_clockInverseReal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    ∀ᵐ t ∂γ.exposureParameterMeasure F,
      HasDerivAt (γ.clockInverseReal F hfinite hdom)
        ‖F.velocity (γ.path (γ.clockInverseReal F hfinite hdom t))‖ t := by
  have h1 := γ.clockInverseReal_ae_transfer F hfinite hdom
    (γ.ae_hasDerivAt_exposureClock F hfinite)
  have h2 := γ.clockInverseReal_ae_transfer F hfinite hdom
    (γ.ae_velocity_ne_zero F hfinite)
  have h3 : ∀ᵐ t ∂γ.exposureParameterMeasure F,
      t ∈ Set.Ioo 0 (γ.exposureTime F).toReal := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae Ioo_ae_eq_Icc] with t ht hmem
    exact hmem.mpr ht
  filter_upwards [h1, h2, h3] with t hd hv ht
  exact γ.hasDerivAt_clockInverseReal F hfinite hdom ht hd hv

theorem ae_hasDerivAt_exposurePathReal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (hdir : γ.IsDirectedBy F) :
    ∀ᵐ t ∂γ.exposureParameterMeasure F,
      HasDerivAt (γ.exposurePathReal F hfinite hdom)
        (euclideanBfield (γ.exposurePathReal F hfinite hdom t)
          (γ.exposureControl F hfinite hdom t)) t := by
  have hpath := γ.clockInverseReal_ae_transfer F hfinite hdom hdir
  have hinv := γ.ae_hasDerivAt_clockInverseReal F hfinite hdom
  have hv := γ.clockInverseReal_ae_transfer F hfinite hdom
    (γ.ae_velocity_ne_zero F hfinite)
  filter_upwards [hpath, hinv, hv] with t hpt hit hvt
  have hvv : ‖F.velocity (γ.path (γ.clockInverseReal F hfinite hdom t))‖ ≠ 0 :=
    (norm_pos_iff.mpr hvt).ne'
  have hcomp := hpt.scomp t hit
  simp only [EuclideanArc.inverseSpeed, smul_smul, mul_inv_cancel₀ hvv,
    one_smul] at hcomp
  exact hcomp

end EuclideanArc

namespace ExposureArcRealization

variable {F : EuclideanExposureFlow} {A : Type*} [MeasurableSpace A]
    {D : ExposureMeasureDecomposition F A}

/-- Conditional exposure-time trajectory: from a decomposition, an arc
realization, and a.e. tangency of the realized arcs, extract an explicit
finite-duration Lipschitz curve with disk-valued measurable control obeying
the Euclidean field equation a.e. on its interval.  This is a weighted-cost
trajectory, not a physical `Pulse`, and does not establish `Cstar ≤ pRelaxed`. -/
theorem exists_exposure_time_trajectory (R : ExposureArcRealization D)
    (hdir : ∀ᵐ a ∂D.ensemble, (R.arc a).IsDirectedBy F) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T ≤ F.stateMeasure Set.univ ∧
      ∃ y : ℝ → ExposureEuclidean, ∃ u : ℝ → ℂ,
        Measurable u ∧ (∀ t, ‖u t‖ ≤ 1) ∧
        (∃ K : NNReal, LipschitzWith K y) ∧
        y 0 = exposureEuclideanEquiv y0 ∧
        y T = exposureEuclideanEquiv yPi ∧
        (∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
          HasDerivAt y (euclideanBfield (y t) (u t)) t := by
  obtain ⟨γ, hdirγ, hp0, hpT, hdom, hvel, hle, hlt⟩ :=
    R.exists_arc_le_exposure_mass (fun γ => γ.IsDirectedBy F) hdir
  obtain ⟨K, hK, hlip⟩ := γ.exists_lipschitz_exposurePathReal F hlt hdom
  refine ⟨(γ.exposureTime F).toReal,
    γ.exposureTime_toReal_pos F hlt hdom, ?_,
    γ.exposurePathReal F hlt hdom, γ.exposureControl F hlt hdom,
    γ.measurable_exposureControl F hlt hdom,
    γ.exposureControl_bound F hlt hdom, ⟨K, hlip⟩,
    (γ.exposurePathReal_zero F hlt hdom).trans hp0,
    (γ.exposurePathReal_terminal F hlt hdom).trans hpT,
    fun t _ => γ.exposurePathReal_mem_domain F hlt hdom t,
    γ.ae_hasDerivAt_exposurePathReal F hlt hdom hdirγ⟩
  rw [ENNReal.ofReal_toReal hlt.ne]
  exact hle

end ExposureArcRealization

end CZExposure
