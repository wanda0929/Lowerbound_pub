module
public import RequestProject.AppendixE.ExposureDisintegration
public import RequestProject.AppendixE.VectorMeasureBounds
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Averaged exposure flow as a finite-variation vector measure (Appendix E support)

The averaged exposure flow produced by `exists_averaged_exposure_flow` is
transported to `EuclideanSpace ℝ (Fin 11)` along the canonical continuous
linear equivalence.  The scalar state measure retains the exposure mass;
the induced vector measure `μ.withDensityᵥ v` has finite variation dominated
by `μ.withDensity (‖v ·‖ₑ)`, vanishes off the compact image of `Yset`, and its
density-defined action on gradients gives the weak source–sink boundary
`ψ(z_π) - ψ(z_0)`.

This constructs the vector measure and its density-defined action.  A formal
identification with the current framework used by Paolini–Stepanov, cycle
removal, and path extraction are still outstanding.  In particular the norm
mass of the vector measure is distinct from the exposure budget: only an
upper bound is proved here.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-- Euclidean-space copy of the ambient exposure state space. -/
abbrev ExposureEuclidean := EuclideanSpace ℝ (Fin 11)

/-- Canonical continuous linear equivalence between the function space
`Fin 11 → ℝ` (sup norm) and its Euclidean-space copy. -/
def exposureEuclideanEquiv : (Fin 11 → ℝ) ≃L[ℝ] ExposureEuclidean :=
  (EuclideanSpace.equiv (Fin 11) ℝ).symm

/-- The compact domain in Euclidean coordinates. -/
def euclideanExposureDomain : Set ExposureEuclidean := exposureEuclideanEquiv '' Yset

/-- The B-field read in Euclidean coordinates. -/
def euclideanBfield (z : ExposureEuclidean) (u : ℂ) : ExposureEuclidean :=
  exposureEuclideanEquiv (Bfield (exposureEuclideanEquiv.symm z) u)

theorem isCompact_euclideanExposureDomain : IsCompact euclideanExposureDomain :=
  isCompact_Yset.image exposureEuclideanEquiv.continuous

theorem measurable_euclideanBfield :
    Measurable (fun p : ExposureEuclidean × ℂ => euclideanBfield p.1 p.2) := by
  have h1 : Measurable (fun p : ExposureEuclidean × ℂ =>
      Bfield (exposureEuclideanEquiv.symm p.1) p.2) :=
    measurable_Bfield.comp
      ((exposureEuclideanEquiv.symm.continuous.measurable.comp
        measurable_fst).prodMk measurable_snd)
  exact exposureEuclideanEquiv.continuous.measurable.comp h1

@[simp] theorem euclideanBfield_equiv (y : Fin 11 → ℝ) (u : ℂ) :
    euclideanBfield (exposureEuclideanEquiv y) u =
      exposureEuclideanEquiv (Bfield y u) := by
  simp [euclideanBfield]

theorem fderiv_comp_exposureEuclideanEquiv {ψ : ExposureEuclidean → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (y w : Fin 11 → ℝ) :
    fderiv ℝ (fun y' => ψ (exposureEuclideanEquiv y')) y w =
      fderiv ℝ ψ (exposureEuclideanEquiv y) (exposureEuclideanEquiv w) := by
  have hdiff : DifferentiableAt ℝ ψ (exposureEuclideanEquiv y) :=
    (hψ.differentiable one_ne_zero) _
  have hmap : HasFDerivAt (fun y' => exposureEuclideanEquiv y')
      exposureEuclideanEquiv.toContinuousLinearMap y :=
    exposureEuclideanEquiv.toContinuousLinearMap.hasFDerivAt
  have hcomp := (hdiff.hasFDerivAt.comp y hmap).fderiv
  rw [show (fun y' => ψ (exposureEuclideanEquiv y')) =
      ψ ∘ ⇑exposureEuclideanEquiv from rfl, hcomp, ContinuousLinearMap.comp_apply]
  rfl

/-- Averaged exposure flow in Euclidean coordinates.  The scalar measure
retains exposure mass; the vector measure constructed below has its own
variation.  This is bundled verified flow data, not an axiom asserting a
normal metric current. -/
structure EuclideanExposureFlow where
  stateMeasure : Measure ExposureEuclidean
  finite_stateMeasure : IsFiniteMeasure stateMeasure
  control : ExposureEuclidean → ℂ
  measurable_control : Measurable control
  control_bound : ∀ z, ‖control z‖ ≤ 1
  support : stateMeasure euclideanExposureDomainᶜ = 0
  velocity_integrable : Integrable (fun z => euclideanBfield z (control z)) stateMeasure
  balance : ∀ ψ : ExposureEuclidean → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    Integrable (fun z => fderiv ℝ ψ z (euclideanBfield z (control z))) stateMeasure ∧
    (∫ z, fderiv ℝ ψ z (euclideanBfield z (control z)) ∂stateMeasure) =
      ψ (exposureEuclideanEquiv yPi) - ψ (exposureEuclideanEquiv y0)

theorem exists_euclidean_exposure_flow (ν : Measure ExposureAmbient)
    (hν : IsExposureRecord ν) :
    ∃ F : EuclideanExposureFlow,
      F.stateMeasure = Measure.map exposureEuclideanEquiv ν.fst ∧
      F.stateMeasure Set.univ = ν Set.univ := by
  letI : IsFiniteMeasure ν := hν.1
  obtain ⟨ubar, hmeas_u, hbound_u, hfst0, hvel, hbal, hmass⟩ :=
    exists_averaged_exposure_flow ν hν
  have he_meas : Measurable exposureEuclideanEquiv :=
    exposureEuclideanEquiv.continuous.measurable
  have hfst_fin : IsFiniteMeasure ν.fst :=
    ⟨by rw [hmass]; exact hν.1.measure_univ_lt_top⟩
  haveI : IsFiniteMeasure (Measure.map exposureEuclideanEquiv ν.fst) :=
    ⟨by rw [Measure.map_apply he_meas MeasurableSet.univ, Set.preimage_univ]
        exact hfst_fin.measure_univ_lt_top⟩
  have hemb : MeasurableEmbedding ⇑exposureEuclideanEquiv := by
    refine ⟨?_, he_meas, fun s hs => ?_⟩
    · exact exposureEuclideanEquiv.injective
    · have hset : ⇑exposureEuclideanEquiv '' s =
          ⇑exposureEuclideanEquiv.symm ⁻¹' s := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          show exposureEuclideanEquiv.symm (exposureEuclideanEquiv y) ∈ s
          rw [exposureEuclideanEquiv.symm_apply_apply]
          exact hy
        · intro hz
          exact ⟨exposureEuclideanEquiv.symm z, hz,
            exposureEuclideanEquiv.apply_symm_apply z⟩
      rw [hset]
      exact exposureEuclideanEquiv.symm.continuous.measurable hs
  have hctrl_meas : Measurable (fun z : ExposureEuclidean =>
      ubar (exposureEuclideanEquiv.symm z)) :=
    hmeas_u.comp exposureEuclideanEquiv.symm.continuous.measurable
  have hpre : exposureEuclideanEquiv ⁻¹' (euclideanExposureDomain)ᶜ = Ysetᶜ := by
    rw [euclideanExposureDomain, Set.preimage_compl]
    congr 1
    exact Function.Injective.preimage_image exposureEuclideanEquiv.injective _
  have hsupp : (Measure.map exposureEuclideanEquiv ν.fst)
      euclideanExposureDomainᶜ = 0 := by
    rw [Measure.map_apply he_meas isCompact_euclideanExposureDomain.measurableSet.compl,
      hpre]
    exact hfst0
  have hvel' : Integrable
      (fun z => euclideanBfield z (ubar (exposureEuclideanEquiv.symm z)))
      (Measure.map exposureEuclideanEquiv ν.fst) := by
    have hcomp : Integrable (fun y => exposureEuclideanEquiv (Bfield y (ubar y))) ν.fst :=
      exposureEuclideanEquiv.toContinuousLinearMap.integrable_comp hvel
    exact hemb.integrable_map_iff.mpr hcomp
  refine ⟨⟨Measure.map exposureEuclideanEquiv ν.fst, inferInstance,
    fun z => ubar (exposureEuclideanEquiv.symm z), hctrl_meas,
    fun z => hbound_u _, hsupp, hvel', ?_⟩, rfl, ?_⟩
  · intro ψ hψ hψc
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun y => ψ (exposureEuclideanEquiv y)) :=
      hψ.comp exposureEuclideanEquiv.toContinuousLinearMap.contDiff
    have hχc : HasCompactSupport (fun y => ψ (exposureEuclideanEquiv y)) :=
      hψc.comp_homeomorph exposureEuclideanEquiv.toHomeomorph
    obtain ⟨hintχ, hbalχ⟩ := hbal _ hχ hχc
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hχ1 : ContDiff ℝ 1 (fun y => ψ (exposureEuclideanEquiv y)) :=
      hχ.of_le (by simp)
    have hg_meas : Measurable (fun z : ExposureEuclidean =>
        fderiv ℝ ψ z (euclideanBfield z (ubar (exposureEuclideanEquiv.symm z)))) := by
      have hfd : Continuous (fun z : ExposureEuclidean => fderiv ℝ ψ z) :=
        hψ1.continuous_fderiv one_ne_zero
      have hB : Measurable (fun z : ExposureEuclidean =>
          euclideanBfield z (ubar (exposureEuclideanEquiv.symm z))) :=
        measurable_euclideanBfield.comp (measurable_id.prodMk hctrl_meas)
      exact ((Continuous.clm_apply continuous_fst continuous_snd).measurable).comp
        (hfd.measurable.prodMk hB)
    have hge : (fun z : ExposureEuclidean =>
        fderiv ℝ ψ z (euclideanBfield z (ubar (exposureEuclideanEquiv.symm z))))
        ∘ exposureEuclideanEquiv =
        (fun y => fderiv ℝ (fun y' => ψ (exposureEuclideanEquiv y')) y
          (Bfield y (ubar y))) := by
      funext y
      simp only [Function.comp_apply]
      show fderiv ℝ ψ (exposureEuclideanEquiv y)
          (euclideanBfield (exposureEuclideanEquiv y)
            (ubar (exposureEuclideanEquiv.symm (exposureEuclideanEquiv y)))) = _
      rw [exposureEuclideanEquiv.symm_apply_apply, euclideanBfield_equiv,
        ← fderiv_comp_exposureEuclideanEquiv hψ1 y]
    constructor
    · refine hemb.integrable_map_iff.mpr ?_
      rw [hge]
      exact hintχ
    · rw [integral_map he_meas.aemeasurable hg_meas.aestronglyMeasurable]
      have hpt : (fun y => fderiv ℝ ψ (exposureEuclideanEquiv y)
          (euclideanBfield (exposureEuclideanEquiv y)
            (ubar (exposureEuclideanEquiv.symm (exposureEuclideanEquiv y))))) =
          fun y => fderiv ℝ (fun y' => ψ (exposureEuclideanEquiv y')) y
            (Bfield y (ubar y)) := by
        funext y
        show fderiv ℝ ψ (exposureEuclideanEquiv y)
            (euclideanBfield (exposureEuclideanEquiv y)
              (ubar (exposureEuclideanEquiv.symm (exposureEuclideanEquiv y)))) = _
        rw [exposureEuclideanEquiv.symm_apply_apply, euclideanBfield_equiv,
          ← fderiv_comp_exposureEuclideanEquiv hψ1 y]
      rw [hpt, hbalχ]
  · rw [Measure.map_apply he_meas MeasurableSet.univ, Set.preimage_univ]
    exact hmass

namespace EuclideanExposureFlow

/-- The Euclidean velocity field of the flow. -/
def velocity (F : EuclideanExposureFlow) (z : ExposureEuclidean) : ExposureEuclidean :=
  euclideanBfield z (F.control z)

/-- The vector measure with density `F.velocity`. -/
def vectorMeasure (F : EuclideanExposureFlow) :
    VectorMeasure ExposureEuclidean ExposureEuclidean :=
  F.stateMeasure.withDensityᵥ F.velocity

/-- A dominating measure for vector variation; no equality is asserted. -/
def massBound (F : EuclideanExposureFlow) : Measure ExposureEuclidean :=
  F.stateMeasure.withDensity (fun z => ‖F.velocity z‖ₑ)

/-- Evaluation on a one-form whenever the displayed integrand is integrable. -/
def action (F : EuclideanExposureFlow)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) : ℝ :=
  ∫ z, ω z (F.velocity z) ∂F.stateMeasure

/-- The weak boundary action on gradients. -/
def boundary (F : EuclideanExposureFlow) (ψ : ExposureEuclidean → ℝ) : ℝ :=
  F.action (fun z => fderiv ℝ ψ z)

theorem measurable_velocity (F : EuclideanExposureFlow) : Measurable F.velocity :=
  measurable_euclideanBfield.comp (measurable_id.prodMk F.measurable_control)

theorem vectorMeasure_apply (F : EuclideanExposureFlow) {s : Set ExposureEuclidean}
    (hs : MeasurableSet s) :
    F.vectorMeasure s = ∫ z in s, F.velocity z ∂F.stateMeasure :=
  withDensityᵥ_apply F.velocity_integrable hs

theorem variation_le_massBound (F : EuclideanExposureFlow) :
    F.vectorMeasure.variation ≤ F.massBound :=
  withDensity_vectorMeasure_variation_le F.velocity_integrable

theorem massBound_univ_lt_top (F : EuclideanExposureFlow) :
    F.massBound Set.univ < ⊤ := by
  show (F.stateMeasure.withDensity fun z => ‖F.velocity z‖ₑ) Set.univ < ⊤
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact F.velocity_integrable.hasFiniteIntegral

theorem variation_univ_lt_top (F : EuclideanExposureFlow) :
    F.vectorMeasure.variation Set.univ < ⊤ :=
  lt_of_le_of_lt (variation_le_massBound F Set.univ) (massBound_univ_lt_top F)

theorem variation_support (F : EuclideanExposureFlow) :
    F.vectorMeasure.variation euclideanExposureDomainᶜ = 0 := by
  have hs0 : F.massBound euclideanExposureDomainᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ F.support
  exact le_antisymm ((variation_le_massBound F _).trans hs0.le) (zero_le _)

/-- Almost-everywhere operator-norm bound for the action integrand. -/
private theorem action_bound_ae (F : EuclideanExposureFlow)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)}
    {C : ℝ} (hbound : ∀ z ∈ euclideanExposureDomain, ‖ω z‖ ≤ C) :
    ∀ᵐ z ∂F.stateMeasure, ‖ω z (F.velocity z)‖ ≤ C * ‖F.velocity z‖ := by
  have hdom : ∀ᵐ z ∂F.stateMeasure, z ∈ euclideanExposureDomain :=
    mem_ae_iff.mpr F.support
  filter_upwards [hdom] with z hz
  calc ‖ω z (F.velocity z)‖ ≤ ‖ω z‖ * ‖F.velocity z‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖F.velocity z‖ := mul_le_mul_of_nonneg_right (hbound z hz) (norm_nonneg _)

/-- Measurability of the action integrand. -/
private theorem measurable_action_integrand (F : EuclideanExposureFlow)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)} (hω : Measurable ω) :
    Measurable fun z => ω z (F.velocity z) :=
  ((Continuous.clm_apply continuous_fst continuous_snd).measurable).comp
    (hω.prodMk F.measurable_velocity)

theorem action_integrable_of_bound (F : EuclideanExposureFlow)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)} (hω : Measurable ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ euclideanExposureDomain, ‖ω z‖ ≤ C) :
    Integrable (fun z => ω z (F.velocity z)) F.stateMeasure := by
  refine (F.velocity_integrable.norm.const_mul C).mono'
    (measurable_action_integrand F hω).aestronglyMeasurable ?_
  filter_upwards [action_bound_ae F hbound] with z hz
  simpa using hz

theorem action_add (F : EuclideanExposureFlow)
    (ω η : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ))
    (hω : Integrable (fun z => ω z (F.velocity z)) F.stateMeasure)
    (hη : Integrable (fun z => η z (F.velocity z)) F.stateMeasure) :
    F.action (ω + η) = F.action ω + F.action η := by
  simp only [action, Pi.add_apply, ContinuousLinearMap.add_apply]
  exact integral_add hω hη

theorem action_smul (F : EuclideanExposureFlow) (a : ℝ)
    (ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)) :
    F.action (a • ω) = a * F.action ω := by
  simp only [action, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact integral_const_mul a _

theorem action_norm_le (F : EuclideanExposureFlow)
    {ω : ExposureEuclidean → (ExposureEuclidean →L[ℝ] ℝ)} (hω : Measurable ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ euclideanExposureDomain, ‖ω z‖ ≤ C) :
    |F.action ω| ≤ C * ∫ z, ‖F.velocity z‖ ∂F.stateMeasure := by
  have h := norm_integral_le_of_norm_le (F.velocity_integrable.norm.const_mul C)
    (action_bound_ae F hbound)
  rw [integral_const_mul] at h
  rwa [Real.norm_eq_abs] at h

theorem boundary_eq (F : EuclideanExposureFlow) {ψ : ExposureEuclidean → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    F.boundary ψ = ψ (exposureEuclideanEquiv yPi) - ψ (exposureEuclideanEquiv y0) :=
  (F.balance ψ hψ hψc).2

theorem boundary_norm_le (F : EuclideanExposureFlow) {ψ : ExposureEuclidean → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {C : ℝ}
    (hstart : |ψ (exposureEuclideanEquiv y0)| ≤ C)
    (htarget : |ψ (exposureEuclideanEquiv yPi)| ≤ C) :
    |F.boundary ψ| ≤ 2 * C := by
  rw [boundary_eq F hψ hψc]
  calc |ψ (exposureEuclideanEquiv yPi) - ψ (exposureEuclideanEquiv y0)|
      ≤ |ψ (exposureEuclideanEquiv yPi)| + |ψ (exposureEuclideanEquiv y0)| := abs_sub _ _
    _ ≤ C + C := add_le_add htarget hstart
    _ = 2 * C := by ring

/-- Inverse Euclidean speed for the later exposure-time reparameterization.
It takes value infinity at zero speed. This definition does not construct a path. -/
def exposureTimeWeight (F : EuclideanExposureFlow) (z : ExposureEuclidean) : ENNReal :=
  (‖F.velocity z‖ₑ)⁻¹

theorem measurable_exposureTimeWeight (F : EuclideanExposureFlow) :
    Measurable F.exposureTimeWeight :=
  F.measurable_velocity.enorm.inv

theorem exposureTimeWeight_eq_top_of_velocity_eq_zero (F : EuclideanExposureFlow)
    {z : ExposureEuclidean} (hz : F.velocity z = 0) :
    F.exposureTimeWeight z = ⊤ := by
  simp [exposureTimeWeight, hz]

/-- Inverse-speed weighting cancels the velocity density up to a factor at most one,
including on the zero-velocity set. -/
theorem weighted_massBound_le (F : EuclideanExposureFlow) :
    (∫⁻ z, F.exposureTimeWeight z ∂F.massBound) ≤ F.stateMeasure Set.univ := by
  show (∫⁻ z, F.exposureTimeWeight z
      ∂(F.stateMeasure.withDensity fun z => ‖F.velocity z‖ₑ)) ≤ F.stateMeasure Set.univ
  rw [lintegral_withDensity_eq_lintegral_mul _ F.measurable_velocity.enorm
    F.measurable_exposureTimeWeight]
  calc ∫⁻ z, ‖F.velocity z‖ₑ * F.exposureTimeWeight z ∂F.stateMeasure
      ≤ ∫⁻ _, 1 ∂F.stateMeasure := lintegral_mono fun z => by
          show ‖F.velocity z‖ₑ * (‖F.velocity z‖ₑ)⁻¹ ≤ 1
          exact ENNReal.mul_inv_le_one _
    _ = F.stateMeasure Set.univ := by rw [lintegral_const, one_mul]

/-- The inverse-speed mass of the current's variation is dominated by the scalar
exposure mass. -/
theorem weighted_variation_le (F : EuclideanExposureFlow) :
    (∫⁻ z, F.exposureTimeWeight z ∂F.vectorMeasure.variation) ≤
      F.stateMeasure Set.univ :=
  (lintegral_mono' F.variation_le_massBound (le_refl _)).trans F.weighted_massBound_le

/-- The bound also holds after any mass-decreasing cycle removal. The premise is
an explicit measure domination, not an assumed existence of an acyclic current. -/
theorem weighted_submeasure_le (F : EuclideanExposureFlow)
    {m : Measure ExposureEuclidean} (hm : m ≤ F.vectorMeasure.variation) :
    (∫⁻ z, F.exposureTimeWeight z ∂m) ≤ F.stateMeasure Set.univ :=
  (lintegral_mono' hm (le_refl _)).trans F.weighted_variation_le

theorem weighted_submeasure_lt_top (F : EuclideanExposureFlow)
    {m : Measure ExposureEuclidean} (hm : m ≤ F.vectorMeasure.variation) :
    (∫⁻ z, F.exposureTimeWeight z ∂m) < ⊤ :=
  (F.weighted_submeasure_le hm).trans_lt F.finite_stateMeasure.measure_univ_lt_top

/-- Conditional selection step: given a probability decomposition with the
weighted-mass identity, some good component has finite time no greater than the
exposure mass. No decomposition or trajectory existence is assumed globally. -/
theorem exists_component_le_exposure_mass (F : EuclideanExposureFlow)
    {A : Type*} [MeasurableSpace A] (η : Measure A) [IsProbabilityMeasure η]
    (componentTime : A → ENNReal) (Good : A → Prop)
    (hTime : AEMeasurable componentTime η) (hGood : ∀ᵐ a ∂η, Good a)
    {m : Measure ExposureEuclidean} (hm : m ≤ F.vectorMeasure.variation)
    (haverage : (∫⁻ a, componentTime a ∂η) = (∫⁻ z, F.exposureTimeWeight z ∂m)) :
    ∃ a, Good a ∧ componentTime a ≤ F.stateMeasure Set.univ ∧ componentTime a < ⊤ := by
  have hN : η {a | ¬Good a} = 0 := ae_iff.mp hGood
  obtain ⟨a, haN, hale⟩ := exists_notMem_null_le_lintegral hTime hN
  have hGooda : Good a := by simpa using haN
  have hbound : componentTime a ≤ F.stateMeasure Set.univ := by
    calc componentTime a ≤ ∫⁻ a', componentTime a' ∂η := hale
      _ = ∫⁻ z, F.exposureTimeWeight z ∂m := haverage
      _ ≤ F.stateMeasure Set.univ := F.weighted_submeasure_le hm
  exact ⟨a, hGooda, hbound, hbound.trans_lt F.finite_stateMeasure.measure_univ_lt_top⟩

end EuclideanExposureFlow

/-- The averaged flow packaged as a finite-variation vector measure with
compact support and the weak source–sink boundary. -/
theorem exists_exposure_current (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν) :
    ∃ F : EuclideanExposureFlow,
      F.stateMeasure = Measure.map exposureEuclideanEquiv ν.fst ∧
      F.stateMeasure Set.univ = ν Set.univ ∧
      F.vectorMeasure.variation Set.univ < ⊤ ∧
      F.vectorMeasure.variation euclideanExposureDomainᶜ = 0 ∧
      ∀ ψ : ExposureEuclidean → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        F.boundary ψ = ψ (exposureEuclideanEquiv yPi) - ψ (exposureEuclideanEquiv y0) := by
  obtain ⟨F, hmap, hmass⟩ := exists_euclidean_exposure_flow ν hν
  exact ⟨F, hmap, hmass, EuclideanExposureFlow.variation_univ_lt_top F,
    EuclideanExposureFlow.variation_support F,
    fun ψ hψ hψc => EuclideanExposureFlow.boundary_eq F hψ hψc⟩

end CZExposure
