module
public import RequestProject.AppendixE.ActiveExposure
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Active-time dynamics

The normalized control drives the active-time path.  The Lipschitz
clock maps original null sets to null sets (`hausdorffMeasure` in
dimension `1` is Lebesgue measure), so arbitrary original a.e.
predicates transfer to selector times.  The image of the zero-control
set is null: where the clock derivative equals the control amplitude,
zero control forces derivative zero, and mathlib's one-dimensional
Sard lemma applies. The null set where this derivative identity fails
is handled by the null-image bound.

Rademacher's theorem differentiates the `1`-Lipschitz active-time
path a.e.  The chain rule for `x = Y ∘ A` together with cancellation
of the nonzero selected amplitude identifies its physical velocity
a.e., and the scalar absolutely-continuous FTC upgrades this to the
all-time integral equation.  The selector is never differentiated.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PhysicalSegment

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

variable (P : PhysicalSegment)

/-- No measurability assumption on `N`: null outer measure suffices. -/
theorem activeClock_image_null {N : Set ℝ}
    (hsub : N ⊆ Set.Icc 0 P.duration) (hN : volume N = 0) :
    volume (P.activeClock '' N) = 0 := by
  have h := (P.lipschitzOn_activeClock.mono hsub).hausdorffMeasure_image_le
    (d := 1) zero_le_one
  rw [MeasureTheory.hausdorffMeasure_real] at h
  simp only [hN] at h
  exact le_antisymm (by simpa using h) (zero_le _)

/-- Transfer ANY original a.e. predicate through the chosen selector. -/
theorem activeTimeSelector_ae_transfer {Q : ℝ → Prop}
    (hQ : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)), Q t) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      Q (P.activeTimeSelector s) := by
  classical
  let N : Set ℝ := {t | t ∈ Set.Icc 0 P.duration ∧ ¬Q t}
  have hN : volume N = 0 := by
    simpa only [N, Classical.not_imp] using
      (ae_iff.mp ((ae_restrict_iff' measurableSet_Icc).mp hQ))
  have hImage := P.activeClock_image_null (fun t ht => ht.1) hN
  have hsub : {s | s ∈ Set.Icc 0 P.activeDuration ∧
      ¬Q (P.activeTimeSelector s)} ⊆ P.activeClock '' N := by
    rintro s ⟨hs, hsQ⟩
    exact ⟨P.activeTimeSelector s,
      ⟨P.activeTimeSelector_mem s, hsQ⟩,
      P.activeClock_activeTimeSelector_of_mem hs⟩
  have hBad := measure_mono_null hsub hImage
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  apply ae_iff.mpr
  simpa only [Classical.not_imp] using hBad

/-- The clock derivative, a.e. on the closed interval (endpoints are
null, so the `uIoc` statement extends). -/
theorem ae_hasDerivAt_activeClock_onInterval :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)),
      HasDerivAt P.activeClock ‖P.control t‖ t := by
  have h := P.ae_hasDerivAt_activeClock
  rw [Set.uIoc_of_le P.duration_nonneg] at h
  have h' := (ae_restrict_iff' measurableSet_Ioc).mpr h
  rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at h'

/-- The image of the zero-control set is null, even though the clock
need not satisfy its derivative formula everywhere: split into points
where `A' = ‖u‖` (hence `0` on the zero-control set, so the
`1`-dimensional Sard lemma applies) and the null exception set. -/
theorem activeClock_zero_control_image_null :
    volume (P.activeClock ''
      {t | t ∈ Set.Icc 0 P.duration ∧ P.control t = 0}) = 0 := by
  classical
  set Z := {t | t ∈ Set.Icc 0 P.duration ∧ P.control t = 0} with hZ
  set N := {t | t ∈ Set.Icc 0 P.duration ∧
    ¬HasDerivAt P.activeClock ‖P.control t‖ t} with hN
  have hNv : volume N = 0 := by
    have h := (ae_restrict_iff' measurableSet_Icc).mp
      P.ae_hasDerivAt_activeClock_onInterval
    apply ae_iff.mp at h
    simpa only [hN, Classical.not_imp] using h
  have hNImage := P.activeClock_image_null (fun t ht => ht.1) hNv
  have hT : volume (P.activeClock '' (Z ∩ Nᶜ)) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := volume) (f := P.activeClock) (s := Z ∩ Nᶜ)
      (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
    · intro t ht
      have h0 : ‖P.control t‖ = 0 := by
        rw [ht.1.2]; exact norm_zero
      have hd : HasDerivAt P.activeClock ‖P.control t‖ t := by
        have hnot : t ∉ N := ht.2
        simp only [hN, Set.mem_setOf_eq, not_and, not_not] at hnot
        exact hnot ht.1.1
      rw [h0] at hd
      have hf := hd.hasFDerivAt
      rw [show (ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ) :
          ℝ →L[ℝ] ℝ) = 0 from by ext r; simp] at hf
      exact hf.hasFDerivWithinAt
    · intro t _
      simp
  have hunion : P.activeClock '' Z ⊆
      P.activeClock '' (Z ∩ Nᶜ) ∪ P.activeClock '' N := by
    rintro s ⟨t, ht, rfl⟩
    by_cases hd : HasDerivAt P.activeClock ‖P.control t‖ t
    · left
      exact ⟨t, ⟨ht, fun h => absurd hd h.2⟩, rfl⟩
    · right
      exact ⟨t, ⟨ht.1, hd⟩, rfl⟩
  exact measure_mono_null hunion (measure_union_null hT hNImage)

/-- At almost every active time the selected original control is
nonzero. -/
theorem ae_selected_control_ne_zero :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      P.control (P.activeTimeSelector s) ≠ 0 := by
  have hsub : {s | s ∈ Set.Icc 0 P.activeDuration ∧
      P.control (P.activeTimeSelector s) = 0} ⊆
      P.activeClock ''
        {t | t ∈ Set.Icc 0 P.duration ∧ P.control t = 0} := by
    rintro s ⟨hs, h0⟩
    exact ⟨P.activeTimeSelector s,
      ⟨P.activeTimeSelector_mem s, h0⟩,
      P.activeClock_activeTimeSelector_of_mem hs⟩
  have hBad := measure_mono_null hsub P.activeClock_zero_control_image_null
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  apply ae_iff.mpr
  simpa only [Classical.not_imp, not_ne_iff] using hBad

/-- The selected time is in the open interval a.e.: the two
endpoints are null. -/
theorem ae_selected_time_mem_interior :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      P.activeTimeSelector s ∈ Set.Ioo 0 P.duration := by
  have hIoo : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)),
      t ∈ Set.Ioo 0 P.duration := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    apply ae_iff.mpr
    have hsub : {t | t ∈ Set.Icc 0 P.duration ∧
        t ∉ Set.Ioo 0 P.duration} ⊆ ({0, P.duration} : Set ℝ) := by
      intro t ht
      rcases lt_or_eq_of_le ht.1.1 with h0 | h0
      · rcases lt_or_eq_of_le ht.1.2 with hD | hD
        · exact absurd ⟨h0, hD⟩ ht.2
        · exact Or.inr hD
      · exact Or.inl h0.symm
    have h0D : volume ({0, P.duration} : Set ℝ) = 0 := by
      rw [show ({0, P.duration} : Set ℝ) = {0} ∪ {P.duration} from rfl]
      exact measure_union_null (measure_singleton (x := (0 : ℝ)))
        (measure_singleton (x := P.duration))
    have hNull := measure_mono_null hsub h0D
    simpa only [Classical.not_imp] using hNull
  exact P.activeTimeSelector_ae_transfer hIoo

/-- The original a.e. ODE, derived from the all-time integral
equation coordinate by coordinate — no differentiability
assumption on the path is added. -/
theorem ae_hasDerivAt_path :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)),
      HasDerivAt P.path (vf (P.path t) (P.control t)) t := by
  have hcoord : ∀ i : Fin 8,
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)),
        HasDerivAt (fun x => P.path x i)
          (vf (P.path t) (P.control t) i) t := by
    intro i
    have hvi : IntervalIntegrable
        (fun t => vf (P.path t) (P.control t) i) volume 0 P.duration := by
      have h := P.velocity_integrable
      rw [intervalIntegrable_iff] at h ⊢
      exact (integrable_pi_iff).mp h i
    have h := hvi.ae_hasDerivAt_integral
    have hIoc : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)),
        t ∈ Set.Ioo 0 P.duration := by
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      apply ae_iff.mpr
      have hsub : {t | t ∈ Set.Icc 0 P.duration ∧
          t ∉ Set.Ioo 0 P.duration} ⊆ ({0, P.duration} : Set ℝ) := by
        intro t ht
        rcases lt_or_eq_of_le ht.1.1 with h0 | h0
        · rcases lt_or_eq_of_le ht.1.2 with hD | hD
          · exact absurd ⟨h0, hD⟩ ht.2
          · exact Or.inr hD
        · exact Or.inl h0.symm
      have h0D : volume ({0, P.duration} : Set ℝ) = 0 := by
        rw [show ({0, P.duration} : Set ℝ) = {0} ∪ {P.duration} from rfl]
        exact measure_union_null (measure_singleton (x := (0 : ℝ)))
          (measure_singleton (x := P.duration))
      have hNull := measure_mono_null hsub h0D
      simpa only [Classical.not_imp] using hNull
    have hR : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 P.duration)),
        HasDerivAt (fun x => P.path 0 i + ∫ r in (0:ℝ)..x,
          vf (P.path r) (P.control r) i)
          (vf (P.path t) (P.control t) i) t := by
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ioc]
        with t ht htI
      exact (ht (Set.mem_uIcc.mpr (Or.inl (Set.Ioc_subset_Icc_self htI)))
        0 (Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, P.duration_nonneg⟩))).const_add _
    filter_upwards [hR, hIoc] with t ht htI
    have hloc : (fun x => P.path x i) =ᶠ[𝓝 t]
        (fun x => P.path 0 i + ∫ r in (0:ℝ)..x,
          vf (P.path r) (P.control r) i) := by
      filter_upwards [Ioo_mem_nhds htI.1 htI.2] with r hr
      have heq := P.integralEquation r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      have h2 : (∫ q in (0:ℝ)..r, vf (P.path q) (P.control q)) i =
          ∫ q in (0:ℝ)..r, vf (P.path q) (P.control q) i :=
        ((ContinuousLinearMap.proj i : State →L[ℝ]
          ℝ).intervalIntegral_comp_comm
          (P.velocity_integrable_subinterval
            (Set.left_mem_Icc.mpr P.duration_nonneg)
            ⟨le_of_lt hr.1, le_of_lt hr.2⟩)).symm
      rw [heq, Pi.add_apply, h2]
    exact ht.congr_of_eventuallyEq hloc
  filter_upwards [ae_all_iff.mpr hcoord] with t ht
  exact hasDerivAt_pi.mpr ht

/-- The active-time ODE a.e.: at a good active time `s`, writing
`t = σ(s)`, the chain rule on `x = Y ∘ A` identifies
`‖u(t)‖ • deriv Y(s)` with the physical velocity; cancelling the
nonzero real scalar finishes. -/
theorem ae_hasDerivAt_activePath :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      HasDerivAt P.activePath (vf (P.activePath s) (P.activeControl s)) s := by
  have hdiff : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      DifferentiableAt ℝ P.activePath s :=
    ae_restrict_of_ae (P.lipschitz_activePath.ae_differentiableAt
      (μ := volume))
  have hODE : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      HasDerivAt P.path (vf (P.path (P.activeTimeSelector s))
        (P.control (P.activeTimeSelector s))) (P.activeTimeSelector s) :=
    P.activeTimeSelector_ae_transfer P.ae_hasDerivAt_path
  have hCLK : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      HasDerivAt P.activeClock
        ‖P.control (P.activeTimeSelector s)‖ (P.activeTimeSelector s) :=
    P.activeTimeSelector_ae_transfer P.ae_hasDerivAt_activeClock_onInterval
  filter_upwards [hdiff, hODE, hCLK, P.ae_selected_time_mem_interior,
    P.ae_selected_control_ne_zero, ae_restrict_mem measurableSet_Icc]
    with s hdiff hODE hCLK htIoo hNE hs
  have hAs : P.activeClock (P.activeTimeSelector s) = s :=
    P.activeClock_activeTimeSelector_of_mem hs
  have htIcc := P.activeTimeSelector_mem s
  have hYAt : HasDerivAt P.activePath (deriv P.activePath s)
      (P.activeClock (P.activeTimeSelector s)) := by
    rw [hAs]
    exact hdiff.hasDerivAt
  have hcomp := hYAt.scomp (P.activeTimeSelector s) hCLK
  have hloc : P.path =ᶠ[𝓝 (P.activeTimeSelector s)]
      (P.activePath ∘ P.activeClock) := by
    filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with r hr
    exact (P.activePath_activeClock
      ⟨le_of_lt hr.1, le_of_lt hr.2⟩).symm
  have hpath' := hcomp.congr_of_eventuallyEq hloc
  have heq := hpath'.unique hODE
  rw [vf_controlDirection] at heq
  have hcancel : deriv P.activePath s = vf (P.path (P.activeTimeSelector s))
      (controlDirection (P.control (P.activeTimeSelector s))) := by
    have hne : ‖P.control (P.activeTimeSelector s)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hNE
    have harg := congrArg (fun v : State =>
      ‖P.control (P.activeTimeSelector s)‖⁻¹ • v) heq
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using harg
  have hDerivEq : vf (P.activePath s) (P.activeControl s) =
      deriv P.activePath s := by
    have h1 : P.path (P.activeTimeSelector s) = P.activePath s := rfl
    rw [h1] at hcancel
    exact hcancel.symm
  have hY := hdiff.hasDerivAt
  rwa [← hDerivEq] at hY

/-- Scalar FTC helper: a Lipschitz function with a.e. derivative `g`
satisfies the integral equation (as in PhysicalReparam, restated here
since that helper is private). -/
private theorem integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt
    {f g : ℝ → ℝ} {a b : ℝ} {K : NNReal}
    (hab : a ≤ b) (hf : LipschitzWith K f)
    (hg : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (g t) t) :
    IntervalIntegrable g volume a b ∧ (∫ t in a..b, g t) = f b - f a := by
  have hAC : AbsolutelyContinuousOnInterval f a b :=
    (hf.lipschitzOnWith.mono (Set.subset_univ _)).absolutelyContinuousOnInterval
  have hsub : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), HasDerivAt f (g t) t :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      Set.Ioc_subset_Icc_self hg
  rw [← Set.uIoc_of_le hab] at hsub
  have hEq : deriv f =ᵐ[volume.restrict (Set.uIoc a b)] g :=
    hsub.mono fun t ht => ht.deriv
  exact ⟨hAC.intervalIntegrable_deriv.congr_ae hEq,
    (intervalIntegral.integral_congr_ae_restrict hEq).symm.trans
      hAC.integral_deriv_eq_sub⟩

private theorem lipschitz_activePath_coord (i : Fin 8) :
    ∃ K : NNReal, LipschitzWith K (fun s => P.activePath s i) :=
  ⟨_, (ContinuousLinearMap.proj i : State →L[ℝ] ℝ).lipschitz.comp
    P.lipschitz_activePath⟩

theorem intervalIntegrable_activeVelocity_coord (i : Fin 8) :
    IntervalIntegrable (fun s => vf (P.activePath s) (P.activeControl s) i)
      volume 0 P.activeDuration := by
  obtain ⟨K, hK⟩ := P.lipschitz_activePath_coord i
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 P.activeDuration)),
      HasDerivAt (fun x => P.activePath x i)
        (vf (P.activePath s) (P.activeControl s) i) s :=
    P.ae_hasDerivAt_activePath.mono fun s h => (hasDerivAt_pi.mp h) i
  exact (integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt
    P.activeDuration_bounds.1 hK hae).1

theorem intervalIntegrable_activeVelocity :
    IntervalIntegrable (fun s => vf (P.activePath s) (P.activeControl s))
      volume 0 P.activeDuration := by
  rw [intervalIntegrable_iff]
  apply integrable_pi_iff.mpr
  intro i
  have h := P.intervalIntegrable_activeVelocity_coord i
  rwa [intervalIntegrable_iff] at h

theorem activePath_integralEquation_coord {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.activeDuration) (i : Fin 8) :
    P.activePath s i = P.activePath 0 i +
      ∫ r in (0:ℝ)..s, vf (P.activePath r) (P.activeControl r) i := by
  obtain ⟨K, hK⟩ := P.lipschitz_activePath_coord i
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 s)),
      HasDerivAt (fun x => P.activePath x i)
        (vf (P.activePath r) (P.activeControl r) i) r :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc_right hs.2)
      (P.ae_hasDerivAt_activePath.mono fun r h => (hasDerivAt_pi.mp h) i)
  have key := integrable_and_integral_eq_of_lipschitz_ae_hasDerivAt
    hs.1 hK hae
  rw [key.2]
  ring

theorem activePath_integralEquation {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.activeDuration) :
    P.activePath s = P.activePath 0 +
      ∫ r in (0:ℝ)..s, vf (P.activePath r) (P.activeControl r) := by
  funext i
  rw [Pi.add_apply, P.activePath_integralEquation_coord hs i]
  congr 1
  have hproj := ((ContinuousLinearMap.proj i : State →L[ℝ]
    ℝ).intervalIntegral_comp_comm
    (P.intervalIntegrable_activeVelocity.mono_set
      (uIcc_subset_uIcc_of_mem
        (Set.left_mem_Icc.mpr P.activeDuration_bounds.1) hs)))
  exact hproj

end CZExposure.PhysicalSegment
