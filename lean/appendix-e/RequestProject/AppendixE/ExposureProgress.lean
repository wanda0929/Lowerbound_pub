module
public import RequestProject.AppendixE.ExcursionSelection

/-!
# Progress observable on the exposure path

The complex progress observable `z` is read from the first two exposure
coordinates.  Its exposure-time velocity satisfies `‖z'‖ ≤ 4√c` (from
`norm_fderiv_zObs_vf_le`, `‖Dz(vf)‖ ≤ 4c√c`), including at zero cost.
On `X`, `‖z‖ ≥ 1 − 6c`, so the angular-rate integrand `Im(z'/z)` is
well-defined and bounded by `8√β` whenever `c ≤ β ≤ 1/12`.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set ComplexConjugate

/-- Progress coordinate read from the Euclidean exposure space:
`w ↦ (e.symm w).0 + i·(e.symm w).1`. -/
def euclideanProgressCLM : ExposureEuclidean →L[ℝ] ℂ :=
  ((Complex.ofRealCLM.comp (ContinuousLinearMap.proj (0 : Fin 11))) +
    (Complex.I : ℂ) •
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (1 : Fin 11)))).comp
    exposureEuclideanEquiv.symm.toContinuousLinearMap

/-- The complex progress observable along an exposure trajectory. -/
def exposureProgressPath (y : ℝ → ExposureEuclidean) : ℝ → ℂ :=
  euclideanProgressCLM ∘ y

/-- The B-field velocity of the progress observable. -/
def exposureProgressVelocity (y : ℝ → ExposureEuclidean) (u : ℝ → ℂ)
    (t : ℝ) : ℂ := euclideanProgressCLM (euclideanBfield (y t) (u t))

/-- `Im(z'/z)` evaluated at a Euclidean exposure point. -/
def euclideanAngularRate (z : ExposureEuclidean) (u : ℂ) : ℝ :=
  (euclideanProgressCLM (euclideanBfield z u) / euclideanProgressCLM z).im

private theorem euclideanProgressCLM_re (w : ExposureEuclidean) :
    (euclideanProgressCLM w).re = (exposureEuclideanEquiv.symm w) 0 := by
  simp [euclideanProgressCLM]

private theorem euclideanProgressCLM_im (w : ExposureEuclidean) :
    (euclideanProgressCLM w).im = (exposureEuclideanEquiv.symm w) 1 := by
  simp [euclideanProgressCLM]

theorem euclideanProgressCLM_Jmap (x : State) :
    euclideanProgressCLM (exposureEuclideanEquiv (Jmap x)) = zObs x := by
  apply Complex.ext
  · rw [euclideanProgressCLM_re, exposureEuclideanEquiv.symm_apply_apply]
    show Jmap x 0 = (zObs x).re
    simp [Jmap]
  · rw [euclideanProgressCLM_im, exposureEuclideanEquiv.symm_apply_apply]
    show Jmap x 1 = (zObs x).im
    simp [Jmap]

theorem euclideanProgressCLM_fderiv_Jmap (x v : State) :
    euclideanProgressCLM (exposureEuclideanEquiv (fderiv ℝ Jmap x v)) =
      fderiv ℝ zObs x v := by
  apply Complex.ext
  · rw [euclideanProgressCLM_re, exposureEuclideanEquiv.symm_apply_apply,
      fderiv_Jmap_apply_eq, fderiv_Jmap_zero]
  · rw [euclideanProgressCLM_im, exposureEuclideanEquiv.symm_apply_apply,
      fderiv_Jmap_apply_eq]
    exact fderiv_Jmap_one x v

private theorem euclideanExposureCost_euclideanEquiv_Jmap (x : State) :
    euclideanExposureCost (exposureEuclideanEquiv (Jmap x)) = cost x := by
  show Real.sqrt ((exposureEuclideanEquiv.symm
    (exposureEuclideanEquiv (Jmap x))) 2) = _
  rw [exposureEuclideanEquiv.symm_apply_apply, Jmap_two,
    Real.sqrt_sq (cost_nonneg x)]

theorem euclideanExposureCost_le_one {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) : euclideanExposureCost z ≤ 1 := by
  obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hz
  rw [euclideanExposureCost_euclideanEquiv_Jmap]
  exact cost_le_one hx

/-- `‖z'‖ ≤ 4√c` in exposure time, including at zero cost. -/
theorem norm_euclideanProgress_Bfield_le {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖euclideanProgressCLM (euclideanBfield z u)‖ ≤
      4 * Real.sqrt (euclideanExposureCost z) := by
  obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hz
  rw [euclideanExposureCost_euclideanEquiv_Jmap, euclideanBfield_equiv]
  rcases eq_or_ne (cost x) 0 with hc | hc
  · rw [Bfield_Jmap_of_zero hc u]
    simp [hc]
  · have hcpos : 0 < cost x := lt_of_le_of_ne' (cost_nonneg x) hc
    rw [Bfield_Jmap_of_pos hcpos u]
    calc ‖euclideanProgressCLM (exposureEuclideanEquiv
            ((cost x)⁻¹ • fderiv ℝ Jmap x (vf x u)))‖
        = ‖(cost x)⁻¹ • fderiv ℝ zObs x (vf x u)‖ := by
          rw [exposureEuclideanEquiv.map_smul,
            euclideanProgressCLM.map_smul, euclideanProgressCLM_fderiv_Jmap]
      _ = |(cost x)⁻¹| * ‖fderiv ℝ zObs x (vf x u)‖ := norm_smul _ _
      _ ≤ |(cost x)⁻¹| * (4 * cost x * Real.sqrt (cost x)) :=
          mul_le_mul_of_nonneg_left (norm_fderiv_zObs_vf_le hx hu)
            (abs_nonneg _)
      _ = 4 * Real.sqrt (cost x) := by
          rw [abs_of_nonneg (inv_nonneg.mpr (cost_nonneg x))]
          field_simp

/-- `‖zObs x‖ ≥ 1 − 6c(x)` on `X`. -/
theorem norm_zObs_ge_one_sub_six_cost {x : State} (hx : x ∈ Xset) :
    1 - 6 * cost x ≤ ‖zObs x‖ := by
  have ⟨hs1, hs2⟩ := hx
  have h1a : (0:ℝ) ≤ 1 - ‖r1 x‖ ^ 2 := by
    have h := mul_le_mul (norm_r1_le_one hx) (norm_r1_le_one hx)
      (norm_nonneg _) (by norm_num)
    linarith
  have h1b : (0:ℝ) ≤ 1 - ‖r2 x‖ ^ 2 := by
    have h := mul_le_mul (norm_r2_le_one hx) (norm_r2_le_one hx)
      (norm_nonneg _) (by norm_num)
    linarith
  have hsqrt_le : (1 - ‖r2 x‖ ^ 2) ≤ Real.sqrt (1 - ‖r2 x‖ ^ 2) := by
    rw [Real.le_sqrt h1b]
    · nlinarith [sq_nonneg (‖r2 x‖)]
    · exact h1b
  have hA : (1 - ‖r2 x‖ ^ 2) * (1 - ‖r1 x‖ ^ 2) ≤
      ‖conj (g2 x) * g1 x ^ 2‖ := by
    rw [norm_mul, norm_pow, Complex.norm_conj]
    have hg1 : ‖g1 x‖ ^ 2 = 1 - ‖r1 x‖ ^ 2 := by linarith
    have hg2 : Real.sqrt (‖g2 x‖ ^ 2) = Real.sqrt (1 - ‖r2 x‖ ^ 2) := by
      rw [show (1 - ‖r2 x‖ ^ 2) = ‖g2 x‖ ^ 2 by linarith]
    have hg2' : ‖g2 x‖ = Real.sqrt (1 - ‖r2 x‖ ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (g2 x)), hg2]
    rw [hg2', hg1]
    exact mul_le_mul_of_nonneg_right hsqrt_le h1a
  have hB : ‖(Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖ ≤ 2 * cost x := by
    have hb1 : ‖(Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖ =
        Real.sqrt 2 * ‖r2 x‖ * ‖g1 x‖ * ‖r1 x‖ := by
      simp [Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), mul_assoc]
    have hb2 : Real.sqrt 2 * ‖r2 x‖ * ‖g1 x‖ * ‖r1 x‖ ≤
        Real.sqrt 2 * ‖r2 x‖ * 1 * ‖r1 x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_g1_le_one hx)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
        (norm_nonneg (r1 x))
    have hb3 : Real.sqrt 2 * ‖r2 x‖ * 1 * ‖r1 x‖ ≤ 2 * cost x := by
      have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      have hc : 2 * cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 2 := by
        rw [show cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4 from rfl]
        ring
      rw [hc]
      nlinarith [sq_nonneg (Real.sqrt 2 * ‖r1 x‖ - ‖r2 x‖),
        Real.sqrt_nonneg (2 : ℝ), norm_nonneg (r1 x), norm_nonneg (r2 x)]
    rw [hb1]
    exact hb2.trans hb3
  have hsum : ‖conj (g2 x) * g1 x ^ 2‖ ≤ ‖zObs x‖ +
      ‖(Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x‖ := by
    have h : conj (g2 x) * g1 x ^ 2 =
        zObs x - ((Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x) := by
      rw [zObs]; ring
    rw [h]
    exact norm_sub_le _ _
  have hab : ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2 ≤ 4 * cost x := by
    have hc : 4 * cost x = 2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2 := by
      rw [show cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4 from rfl]
      ring
    rw [hc]
    nlinarith [sq_nonneg (‖r1 x‖)]
  nlinarith

theorem norm_euclideanProgress_ge_half {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) {β : ℝ}
    (hc : euclideanExposureCost z ≤ β) (hβ : β ≤ 1/12) :
    (1/2 : ℝ) ≤ ‖euclideanProgressCLM z‖ := by
  obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hz
  rw [euclideanExposureCost_euclideanEquiv_Jmap] at hc
  rw [euclideanProgressCLM_Jmap]
  have h := norm_zObs_ge_one_sub_six_cost hx
  linarith

theorem abs_euclideanAngularRate_le {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) {u : ℂ} (hu : ‖u‖ ≤ 1)
    {β : ℝ} (hc : euclideanExposureCost z ≤ β) (hβ : β ≤ 1/12) :
    |euclideanAngularRate z u| ≤ 8 * Real.sqrt β := by
  have hhalf := norm_euclideanProgress_ge_half hz hc hβ
  have hnz : 0 < ‖euclideanProgressCLM z‖ := by linarith
  have hN : ‖euclideanProgressCLM (euclideanBfield z u)‖ ≤
      4 * Real.sqrt β := (norm_euclideanProgress_Bfield_le hz hu).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by norm_num))
  calc |euclideanAngularRate z u|
      ≤ ‖euclideanProgressCLM (euclideanBfield z u)‖ /
          ‖euclideanProgressCLM z‖ := by
        show |(euclideanProgressCLM (euclideanBfield z u) /
            euclideanProgressCLM z).im| ≤ _
        exact (Complex.abs_im_le_norm _).trans_eq (norm_div _ _)
    _ ≤ (4 * Real.sqrt β) / (1 / 2) := by
        gcongr
    _ = 8 * Real.sqrt β := by rw [div_eq_mul_inv]; ring

theorem measurable_exposureProgressVelocity {y : ℝ → ExposureEuclidean}
    {u : ℝ → ℂ} (hy : Measurable y) (hu : Measurable u) :
    Measurable (exposureProgressVelocity y u) :=
  euclideanProgressCLM.continuous.measurable.comp
    (measurable_euclideanBfield.comp (hy.prodMk hu))

theorem measurable_exposureAngularRate {y : ℝ → ExposureEuclidean}
    {u : ℝ → ℂ} (hy : Measurable y) (hu : Measurable u) :
    Measurable (fun t => euclideanAngularRate (y t) (u t)) := by
  simp only [euclideanAngularRate]
  exact Complex.continuous_im.measurable.comp
    ((measurable_exposureProgressVelocity hy hu).div
      (euclideanProgressCLM.continuous.measurable.comp hy))

theorem integrableOn_exposureProgressVelocity {T : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
    (hy : Continuous y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain) :
    IntegrableOn (exposureProgressVelocity y u) (Set.Icc 0 T) := by
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    (measurable_exposureProgressVelocity hy.measurable hu).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have h1 := Real.sqrt_le_sqrt
    (euclideanExposureCost_le_one (hdom t ht))
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 4 by norm_num)
  rw [Real.sqrt_one, mul_one] at h2
  exact (norm_euclideanProgress_Bfield_le (hdom t ht) (hub t)).trans h2

theorem ae_hasDerivAt_exposureProgressPath {T : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ}
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt (exposureProgressPath y) (exposureProgressVelocity y u t) t :=
  hode.mono fun t ht => euclideanProgressCLM.hasFDerivAt.comp_hasDerivAt t ht

private theorem scalar_ftc_of_lipschitz_ae_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ}
    {K : NNReal}
    (hab : a ≤ b) (hf : LipschitzWith K f)
    (hg : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (g t) t) :
    IntervalIntegrable g volume a b ∧ (∫ t in a..b, g t) = f b - f a := by
  have hAC :=
    (hf.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval
  have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]
    exact Set.Ioc_subset_Icc_self
  have hder : deriv f =ᵐ[volume.restrict (Set.uIoc a b)] g := by
    have hg' := MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hg
    exact hg'.mono fun t ht => ht.deriv
  exact ⟨hAC.intervalIntegrable_deriv.congr_ae hder,
    (intervalIntegral.integral_congr_ae_restrict hder).symm.trans
      hAC.integral_deriv_eq_sub⟩

theorem integral_exposureProgressVelocity {T a b : ℝ}
    {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hy : LipschitzWith K y) (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ t in a..b, exposureProgressVelocity y u t) =
      exposureProgressPath y b - exposureProgressPath y a := by
  have hode' : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      HasDerivAt (exposureProgressPath y) (exposureProgressVelocity y u t) t :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc ha hb) (ae_hasDerivAt_exposureProgressPath hode)
  have hcomp : ∀ L : ℂ →L[ℝ] ℝ,
      IntervalIntegrable (fun t => L (exposureProgressVelocity y u t))
          volume a b ∧
        (∫ t in a..b, L (exposureProgressVelocity y u t)) =
          L (exposureProgressPath y b) - L (exposureProgressPath y a) := by
    intro L
    have hf : LipschitzWith _ (fun t => L ((euclideanProgressCLM ∘ y) t)) :=
      (L.lipschitz.comp euclideanProgressCLM.lipschitz).comp hy
    have hg : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
        HasDerivAt (fun t => L ((euclideanProgressCLM ∘ y) t))
          (L (exposureProgressVelocity y u t)) t :=
      hode'.mono fun t ht => L.hasFDerivAt.comp_hasDerivAt t ht
    exact scalar_ftc_of_lipschitz_ae_hasDerivAt hab hf hg
  have hInt : IntervalIntegrable (exposureProgressVelocity y u) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((integrableOn_exposureProgressVelocity hy.continuous hu hub hdom).mono_set
        (Set.Icc_subset_Icc ha hb))
  apply Complex.ext
  · show Complex.reCLM (∫ t in a..b, exposureProgressVelocity y u t) =
        (exposureProgressPath y b - exposureProgressPath y a).re
    have e : (exposureProgressPath y b - exposureProgressPath y a).re =
        Complex.reCLM (exposureProgressPath y b) -
          Complex.reCLM (exposureProgressPath y a) :=
      map_sub Complex.reCLM _ _
    have h2 := (hcomp Complex.reCLM).2
    rw [e, ← h2]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      Complex.reCLM hInt).symm
  · show Complex.imCLM (∫ t in a..b, exposureProgressVelocity y u t) =
        (exposureProgressPath y b - exposureProgressPath y a).im
    have e : (exposureProgressPath y b - exposureProgressPath y a).im =
        Complex.imCLM (exposureProgressPath y b) -
          Complex.imCLM (exposureProgressPath y a) :=
      map_sub Complex.imCLM _ _
    have h2 := (hcomp Complex.imCLM).2
    rw [e, ← h2]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      Complex.imCLM hInt).symm

end CZExposure
