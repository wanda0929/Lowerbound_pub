import RequestProject.AppendixE.ActiveDynamics
import RequestProject.AppendixE.PhaseTransport
import LowerBoundCZ.Reductions

noncomputable section

namespace CZExposure

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

/-- A complex amplitude projection, with the real normed-space structure
used by the integral trajectory model. -/
def amplitudeCLM (i j : Fin 8) : State →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))

@[simp] theorem amplitudeCLM_apply (i j : Fin 8) (x : State) :
    amplitudeCLM i j x = ⟨x i, x j⟩ := by
  apply Complex.ext <;> simp [amplitudeCLM, Complex.mul_re, Complex.mul_im]

namespace PhysicalSegment

/-- Extension is only a device for the global Lipschitz hypothesis in the
existing phase-transport theorem. The trajectory is unchanged on its interval. -/
theorem exists_lipschitz_extension (P : PhysicalSegment) :
    ∃ x : ℝ → State, LipschitzWith 1 x ∧
      (∀ t ∈ Icc 0 P.duration, x t = P.path t) ∧
      (∀ᵐ t ∂(volume.restrict (Icc 0 P.duration)),
        HasDerivAt x (vf (x t) (P.control t)) t) := by
  obtain ⟨x, hx, heq⟩ := P.path_lipschitzOn.extend_pi
  refine ⟨x, hx, (fun t ht => (heq ht).symm), ?_⟩
  have hio : ∀ᵐ t ∂(volume.restrict (Icc 0 P.duration)),
      t ∈ Ioo 0 P.duration := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [P.ae_hasDerivAt_path, hio] with t ht hi
  have he : x =ᶠ[𝓝 t] P.path := by
    filter_upwards [Ioo_mem_nhds hi.1 hi.2] with s hs
    exact (heq (Ioo_subset_Icc_self hs)).symm
  rw [← heq (Ioo_subset_Icc_self hi)]
  exact ht.congr_of_eventuallyEq he

/-- The actual quotient and synchronization-error derivatives. There is no
extra differentiability assumption: it follows from the integral equation. -/
theorem ae_stereographic_dynamics (P : PhysicalSegment) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 P.duration)),
      g1 (P.path t) ≠ 0 → g2 (P.path t) ≠ 0 →
      HasDerivAt
        (fun s => r2 (P.path s) / g2 (P.path s) -
          (Real.sqrt 2 : ℂ) * (r1 (P.path s) / g1 (P.path s)))
        ((Complex.I / (Real.sqrt 2 : ℂ)) * P.control t *
          ((r2 (P.path t) / g2 (P.path t)) ^ 2 -
           (r1 (P.path t) / g1 (P.path t)) ^ 2)) t := by
  filter_upwards [P.ae_hasDerivAt_path] with t ht
  intro h1 h2
  have hg1 := (amplitudeCLM 0 1).hasFDerivAt.comp_hasDerivAt t ht
  have hr1 := (amplitudeCLM 2 3).hasFDerivAt.comp_hasDerivAt t ht
  have hg2 := (amplitudeCLM 4 5).hasFDerivAt.comp_hasDerivAt t ht
  have hr2 := (amplitudeCLM 6 7).hasFDerivAt.comp_hasDerivAt t ht
  simp only [Function.comp_def, amplitudeCLM_apply] at hg1 hr1 hg2 hr2
  change HasDerivAt (fun s => g1 (P.path s)) (fC (P.path t) (P.control t) 0) t at hg1
  change HasDerivAt (fun s => r1 (P.path s)) (fC (P.path t) (P.control t) 1) t at hr1
  change HasDerivAt (fun s => g2 (P.path s)) (fC (P.path t) (P.control t) 2) t at hg2
  change HasDerivAt (fun s => r2 (P.path s)) (fC (P.path t) (P.control t) 3) t at hr2
  have h := (hr2.div hg2 h2).sub ((hr1.div hg1 h1).const_mul (Real.sqrt 2 : ℂ))
  convert h using 1
  dsimp [fC]
  have hv1 : -(Complex.I / 2) * (P.control t * r1 (P.path t)) =
      LowerBoundCZ.groundVel 1 (P.control t) (r1 (P.path t)) := by
    simp [LowerBoundCZ.groundVel, LowerBoundCZ.kappa_one]; ring
  have hv2 : -(Complex.I / 2) * ((Real.sqrt 2 : ℂ) * P.control t * r2 (P.path t)) =
      LowerBoundCZ.groundVel 2 (P.control t) (r2 (P.path t)) := by
    simp [LowerBoundCZ.groundVel, LowerBoundCZ.kappa_two]; ring
  have hv3 : -(Complex.I / 2) * (conj (P.control t) * g1 (P.path t)) =
      LowerBoundCZ.rydbergVel 1 (P.control t) (g1 (P.path t)) := by
    simp [LowerBoundCZ.rydbergVel, LowerBoundCZ.kappa_one]; ring
  have hv4 : -(Complex.I / 2) * ((Real.sqrt 2 : ℂ) * conj (P.control t) * g2 (P.path t)) =
      LowerBoundCZ.rydbergVel 2 (P.control t) (g2 (P.path t)) := by
    simp [LowerBoundCZ.rydbergVel, LowerBoundCZ.kappa_two]; ring
  rw [hv1, hv2, hv3, hv4, LowerBoundCZ.riccati _ _ _ _ h1,
    LowerBoundCZ.riccati _ _ _ _ h2, LowerBoundCZ.syncError_deriv]
  rfl

/-- A phase of any nonvanishing linear amplitude on a closed subinterval.
Its angular velocity is integrable because the amplitude stays away from
zero on this compact interval; this is proved, not an added hypothesis. -/
theorem amplitude_phase_lift (P : PhysicalSegment) (G : State →L[ℝ] ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ P.duration)
    (hne : ∀ t ∈ Icc a b, G (P.path t) ≠ 0) :
    ∃ θ : ℝ → ℝ, AbsolutelyContinuousOnInterval θ a b ∧
      (∀ t ∈ Icc a b, phaseFactor (θ t) = complexUnitPhase (G (P.path t))) ∧
      (∀ᵐ t ∂(volume.restrict (Icc a b)),
        HasDerivAt θ ((G (vf (P.path t) (P.control t)) / G (P.path t)).im) t) := by
  obtain ⟨x, hx, heq, hode⟩ := P.exists_lipschitz_extension
  have hsub : Icc a b ⊆ Icc 0 P.duration := Icc_subset_Icc ha hb
  have hxe : ∀ t ∈ Icc a b, x t = P.path t := fun t ht => heq t (hsub ht)
  have hne' : ∀ t ∈ Icc a b, G (x t) ≠ 0 := by
    intro t ht
    rw [hxe t ht]
    exact hne t ht
  have hv : IntervalIntegrable (fun t => G (vf (P.path t) (P.control t))) volume a b := by
    have hv := P.velocity_integrable_subinterval ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩
    rw [intervalIntegrable_iff] at hv ⊢
    exact G.integrable_comp hv
  have hinv : ContinuousOn (fun t => (G (x t))⁻¹) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (G.continuous.comp hx.continuous).continuousOn.inv₀ hne'
  have hint : IntervalIntegrable
      (fun t => (G (vf (P.path t) (P.control t)) / G (x t)).im) volume a b := by
    have hmul := hv.mul_continuousOn hinv
    rw [intervalIntegrable_iff] at hmul ⊢
    simpa [div_eq_mul_inv] using Complex.imCLM.integrable_comp hmul
  have hode' : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      HasDerivAt (fun s => G (x s)) (G (vf (P.path t) (P.control t))) t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hode,
      ae_restrict_mem measurableSet_Icc] with t ht hi
    simpa [Function.comp_def, hxe t hi] using G.hasFDerivAt.comp_hasDerivAt t ht
  obtain ⟨_, hac, hd, hp, _⟩ :=
    complexPhaseLift_spec hab (G.lipschitz.comp hx) hne' hode' hint
  refine ⟨_, hac, ?_, ?_⟩
  · intro t ht
    simpa [hxe t ht] using hp t ht
  · filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht hi
    simpa [hxe t hi] using ht

/-- Appendix D's two velocities for the integral-form physical model,
on every closed interval on which both ground amplitudes are nonzero.
The phases are genuine absolutely continuous lifts, not principal arguments. -/
theorem appendixD (P : PhysicalSegment) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ P.duration)
    (h1 : ∀ t ∈ Icc a b, g1 (P.path t) ≠ 0)
    (h2 : ∀ t ∈ Icc a b, g2 (P.path t) ≠ 0) :
    ∃ Φ1 Φ2 : ℝ → ℝ,
      AbsolutelyContinuousOnInterval Φ1 a b ∧
      AbsolutelyContinuousOnInterval Φ2 a b ∧
      (∀ t ∈ Icc a b, phaseFactor (Φ1 t) = complexUnitPhase (g1 (P.path t))) ∧
      (∀ t ∈ Icc a b, phaseFactor (Φ2 t) = complexUnitPhase (g2 (P.path t))) ∧
      (∀ᵐ t ∂(volume.restrict (Icc a b)),
        let z1 := r1 (P.path t) / g1 (P.path t)
        let z2 := r2 (P.path t) / g2 (P.path t)
        HasDerivAt (fun s => Φ2 s - 2 * Φ1 s)
          (-(1 / Real.sqrt 2) * (P.control t * (z2 - (Real.sqrt 2 : ℂ) * z1)).re) t ∧
        HasDerivAt
          (fun s => r2 (P.path s) / g2 (P.path s) -
            (Real.sqrt 2 : ℂ) * (r1 (P.path s) / g1 (P.path s)))
          ((Complex.I / (Real.sqrt 2 : ℂ)) * P.control t * (z2 ^ 2 - z1 ^ 2)) t) := by
  obtain ⟨Φ1, hac1, hp1, hd1⟩ := P.amplitude_phase_lift (amplitudeCLM 0 1) ha hab hb
    (by simpa only [amplitudeCLM_apply] using h1)
  obtain ⟨Φ2, hac2, hp2, hd2⟩ := P.amplitude_phase_lift (amplitudeCLM 4 5) ha hab hb
    (by simpa only [amplitudeCLM_apply] using h2)
  simp only [amplitudeCLM_apply] at hp1 hp2
  refine ⟨Φ1, Φ2, hac1, hac2, hp1, hp2, ?_⟩
  filter_upwards [hd1, hd2, ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc ha hb) P.ae_stereographic_dynamics]
    with t ht1 ht2 hi hw
  refine ⟨?_, hw (h1 t hi) (h2 t hi)⟩
  have hd := ht2.sub (ht1.const_mul 2)
  convert hd using 1
  simp only [amplitudeCLM_apply]
  change _ = (fC (P.path t) (P.control t) 2 / g2 (P.path t)).im -
    2 * (fC (P.path t) (P.control t) 0 / g1 (P.path t)).im
  have hv1 : fC (P.path t) (P.control t) 0 =
      LowerBoundCZ.groundVel 1 (P.control t) (r1 (P.path t)) := by
    simp [fC, LowerBoundCZ.groundVel, LowerBoundCZ.kappa_one]; ring
  have hv2 : fC (P.path t) (P.control t) 2 =
      LowerBoundCZ.groundVel 2 (P.control t) (r2 (P.path t)) := by
    simp [fC, LowerBoundCZ.groundVel, LowerBoundCZ.kappa_two]; ring
  rw [hv1, hv2, LowerBoundCZ.phase_vel _ _ _ _ (h1 t hi),
    LowerBoundCZ.phase_vel _ _ _ _ (h2 t hi)]
  simp only [LowerBoundCZ.kappa_one, LowerBoundCZ.kappa_two, LowerBoundCZ.stereo,
    mul_sub, Complex.sub_re, ← mul_assoc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  ring_nf
  simp [hs]

end PhysicalSegment
end CZExposure
