module
public import RequestProject.AppendixE.ExposureStateLift

/-!
# Sharp cost-growth bound and the `c√c` height

`dc(vf_u) = Re(conj r₁ · fC₁) + ½ Re(conj r₂ · fC₃)`; on `X` with `‖u‖ ≤ 1`,
`‖fC₁‖ ≤ 1/2` and `‖fC₃‖ ≤ √2/2`, giving
`|dc| ≤ ‖r₁‖/2 + √2‖r₂‖/4 ≤ √c` — sharper than the coarse `6√c` bound of
`abs_fderiv_cost_vf_le`, which is retained unchanged. For the squared-cost
coordinate `q = c²` this yields `|q'| ≤ 2√√q`, and regularizing the height
`g_ε(q) = √(q+ε)·√√(q+ε)` (derivative `3/(4√√(q+ε))`) upgrades `H(c) = c√c`
to a `3/2`-Lipschitz function on the entire exposure-time interval,
including zero-cost times.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set ComplexConjugate Filter
open scoped Topology

/-- The height `H(c) = c^{3/2}` for nonnegative `c`, written as `c·√c`. -/
def costThreeHalves (c : ℝ) : ℝ := c * Real.sqrt c

/-- Squared-cost coordinate read from the Euclidean exposure space. -/
def euclideanSquaredCostCLM : ExposureEuclidean →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (2 : Fin 11)).comp
    exposureEuclideanEquiv.symm.toContinuousLinearMap

theorem continuous_costThreeHalves : Continuous costThreeHalves :=
  continuous_id.mul Real.continuous_sqrt

theorem monotoneOn_costThreeHalves : MonotoneOn costThreeHalves (Set.Ici 0) := by
  intro a ha b hb hab
  show a * Real.sqrt a ≤ b * Real.sqrt b
  exact mul_le_mul hab (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg a) hb

theorem strictMonoOn_costThreeHalves : StrictMonoOn costThreeHalves (Set.Ici 0) := by
  intro a ha b hb hab
  show a * Real.sqrt a < b * Real.sqrt b
  have hsqrt : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha hab
  have h1 := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hsqrt)
  have h2 := mul_nonneg (sub_nonneg.mpr hab.le) (Real.sqrt_nonneg a)
  have h3 := mul_nonneg ha (sub_nonneg.mpr hsqrt.le)
  nlinarith

/-- Sharp bound on the cost derivative along `vf`: `|dc| ≤ √c`.
(Stronger than `abs_fderiv_cost_vf_le`'s coarse factor `6`.) -/
theorem abs_fderiv_cost_vf_le_sqrt {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |fderiv ℝ cost x (vf x u)| ≤ Real.sqrt (cost x) := by
  have hfC1 : ‖fC x u 1‖ ≤ 1 / 2 := by
    rw [show ‖fC x u 1‖ = 2⁻¹ * (‖u‖ * ‖g1 x‖) by simp [fC]]
    have hp : ‖u‖ * ‖g1 x‖ ≤ 1 * 1 :=
      mul_le_mul hu (norm_g1_le_one hx) (norm_nonneg _) (by norm_num)
    linarith
  have hfC3 : ‖fC x u 3‖ ≤ Real.sqrt 2 / 2 := by
    rw [show ‖fC x u 3‖ = 2⁻¹ * (Real.sqrt 2 * (‖u‖ * ‖g2 x‖)) by
      simp [fC, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg 2), mul_assoc]]
    have hp : ‖u‖ * ‖g2 x‖ ≤ 1 :=
      (mul_le_mul hu (norm_g2_le_one hx) (norm_nonneg _)
        (by norm_num)).trans_eq (mul_one 1)
    have hv : Real.sqrt 2 * (‖u‖ * ‖g2 x‖) ≤ Real.sqrt 2 * 1 :=
      mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg 2)
    linarith
  have hre : fderiv ℝ cost x (vf x u) =
      (conj (r1 x) * fC x u 1).re +
        (conj (r2 x) * fC x u 3).re / 2 := by
    rw [fderiv_cost_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      neg_mul, sub_neg_eq_add]
    rfl
  have hle : |fderiv ℝ cost x (vf x u)| ≤
      ‖r1 x‖ / 2 + Real.sqrt 2 * ‖r2 x‖ / 4 := by
    rw [hre]
    calc |(conj (r1 x) * fC x u 1).re +
        (conj (r2 x) * fC x u 3).re / 2|
        ≤ |(conj (r1 x) * fC x u 1).re| +
          |(conj (r2 x) * fC x u 3).re| / 2 := by
          have h := abs_add_le (conj (r1 x) * fC x u 1).re
            ((conj (r2 x) * fC x u 3).re / 2)
          rwa [abs_div, abs_two] at h
      _ ≤ ‖r1 x‖ * ‖fC x u 1‖ + (‖r2 x‖ * ‖fC x u 3‖) / 2 := by
          have h1 : |(conj (r1 x) * fC x u 1).re| ≤
              ‖r1 x‖ * ‖fC x u 1‖ :=
            (Complex.abs_re_le_norm _).trans
              (by rw [norm_mul, Complex.norm_conj])
          have h2 : |(conj (r2 x) * fC x u 3).re| ≤
              ‖r2 x‖ * ‖fC x u 3‖ :=
            (Complex.abs_re_le_norm _).trans
              (by rw [norm_mul, Complex.norm_conj])
          linarith
      _ ≤ ‖r1 x‖ * (1 / 2) + (‖r2 x‖ * (Real.sqrt 2 / 2)) / 2 := by
          have h1 : ‖r1 x‖ * ‖fC x u 1‖ ≤ ‖r1 x‖ * (1 / 2) :=
            mul_le_mul_of_nonneg_left hfC1 (norm_nonneg _)
          have h2 : ‖r2 x‖ * ‖fC x u 3‖ ≤ ‖r2 x‖ * (Real.sqrt 2 / 2) :=
            mul_le_mul_of_nonneg_left hfC3 (norm_nonneg _)
          linarith
      _ = ‖r1 x‖ / 2 + Real.sqrt 2 * ‖r2 x‖ / 4 := by ring
  have hnonneg : 0 ≤ ‖r1 x‖ / 2 + Real.sqrt 2 * ‖r2 x‖ / 4 := by positivity
  have hsq : (‖r1 x‖ / 2 + Real.sqrt 2 * ‖r2 x‖ / 4) ^ 2 ≤ cost x := by
    rw [show cost x = (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4 from rfl]
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 2 * ‖r1 x‖ - ‖r2 x‖)]
  calc |fderiv ℝ cost x (vf x u)|
      ≤ ‖r1 x‖ / 2 + Real.sqrt 2 * ‖r2 x‖ / 4 := hle
    _ = Real.sqrt ((‖r1 x‖ / 2 + Real.sqrt 2 * ‖r2 x‖ / 4) ^ 2) :=
        (Real.sqrt_sq hnonneg).symm
    _ ≤ Real.sqrt (cost x) := Real.sqrt_le_sqrt hsq

theorem euclideanSquaredCostCLM_nonneg {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) : 0 ≤ euclideanSquaredCostCLM z := by
  obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hz
  show 0 ≤ (exposureEuclideanEquiv.symm (exposureEuclideanEquiv (Jmap x))) 2
  rw [exposureEuclideanEquiv.symm_apply_apply, Jmap_two]
  positivity

/-- The squared-cost coordinate of the B-field: `|q'| ≤ 2√√q = 2√c`. -/
theorem abs_euclideanSquaredCostCLM_Bfield_le {z : ExposureEuclidean}
    (hz : z ∈ euclideanExposureDomain) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |euclideanSquaredCostCLM (euclideanBfield z u)| ≤
      2 * Real.sqrt (euclideanExposureCost z) := by
  obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hz
  have hcost : euclideanExposureCost (exposureEuclideanEquiv (Jmap x)) =
      cost x := by
    show Real.sqrt
        ((exposureEuclideanEquiv.symm (exposureEuclideanEquiv (Jmap x))) 2) = _
    rw [exposureEuclideanEquiv.symm_apply_apply, Jmap_two,
      Real.sqrt_sq (cost_nonneg x)]
  rw [hcost]
  show |(exposureEuclideanEquiv.symm
      (euclideanBfield (exposureEuclideanEquiv (Jmap x)) u)) 2| ≤ _
  rw [euclideanBfield_equiv, exposureEuclideanEquiv.symm_apply_apply]
  rcases eq_or_ne (cost x) 0 with hc | hc
  · rw [Bfield_Jmap_of_zero hc u]
    simp [hc]
  · have hcpos : 0 < cost x := lt_of_le_of_ne' (cost_nonneg x) hc
    rw [Bfield_Jmap_of_pos hcpos u]
    have heq : fderiv ℝ Jmap x (vf x u) 2 =
        2 * cost x * fderiv ℝ cost x (vf x u) := by
      rw [fderiv_Jmap_apply_eq]
      show fderiv ℝ (fun y => Jmap y 2) x (vf x u) = _
      rw [show (fun y : State => Jmap y 2) =
        (fun y : State => Jmap y (Fin.succ (Fin.succ 0))) from rfl]
      exact fderiv_Jmap_two' x (vf x u)
    have hval : ((cost x)⁻¹ • fderiv ℝ Jmap x (vf x u)) 2 =
        2 * fderiv ℝ cost x (vf x u) := by
      rw [Pi.smul_apply, smul_eq_mul, heq]
      field_simp
    rw [hval, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_fderiv_cost_vf_le_sqrt hx hu)
      (by norm_num)

private def regularizedHeight (ε q : ℝ) : ℝ :=
  Real.sqrt (q + ε) * Real.sqrt (Real.sqrt (q + ε))

private theorem hasDerivAt_regularizedHeight {ε q : ℝ} (hε : 0 < ε)
    (hq : 0 ≤ q) :
    HasDerivAt (regularizedHeight ε)
      (3 / (4 * Real.sqrt (Real.sqrt (q + ε)))) q := by
  have hqε : q + ε ≠ 0 := by linarith
  have hA : Real.sqrt (q + ε) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have hB : Real.sqrt (Real.sqrt (q + ε)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))).ne'
  have hq' : HasDerivAt (fun q : ℝ => q + ε) 1 q :=
    (hasDerivAt_id q).add_const ε
  have hA' : HasDerivAt (fun q : ℝ => Real.sqrt (q + ε))
      (1 / (2 * Real.sqrt (q + ε))) q := hq'.sqrt hqε
  have hB' : HasDerivAt (fun q : ℝ => Real.sqrt (Real.sqrt (q + ε)))
      ((1 / (2 * Real.sqrt (q + ε))) /
        (2 * Real.sqrt (Real.sqrt (q + ε)))) q := hA'.sqrt hA
  have h := hA'.mul hB'
  have hrr : Real.sqrt (Real.sqrt (q + ε)) *
      Real.sqrt (Real.sqrt (q + ε)) ≠ 0 := mul_ne_zero hB hB
  have hder : (1 / (2 * Real.sqrt (q + ε))) *
        Real.sqrt (Real.sqrt (q + ε)) +
      Real.sqrt (q + ε) * ((1 / (2 * Real.sqrt (q + ε))) /
        (2 * Real.sqrt (Real.sqrt (q + ε)))) =
      3 / (4 * Real.sqrt (Real.sqrt (q + ε))) := by
    have hs := Real.mul_self_sqrt (Real.sqrt_nonneg (q + ε))
    field_simp
    nlinarith [hs]
  rwa [hder] at h

private theorem contDiffAt_regularizedHeight {ε q : ℝ} (hε : 0 < ε)
    (hq : 0 ≤ q) :
    ContDiffAt ℝ 1 (regularizedHeight ε) q := by
  have hqε : q + ε ≠ 0 := by linarith
  have hA : Real.sqrt (q + ε) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have h1 : ContDiffAt ℝ 1 (fun q : ℝ => Real.sqrt (q + ε)) q :=
    ((contDiffAt_id.add contDiffAt_const).sqrt hqε)
  exact h1.mul (h1.sqrt hA)

/-- Upgrade an already-Lipschitz scalar function with an a.e. derivative
bound to the sharp constant (absolute continuity + FTC). -/
private theorem lipschitzOnWith_of_lipschitzOn_ae_deriv_le {f : ℝ → ℝ}
    {T : ℝ} {K A : NNReal}
    (hf : LipschitzOnWith K f (Set.Icc 0 T))
    (hder : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), |deriv f t| ≤ A) :
    LipschitzOnWith A f (Set.Icc 0 T) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  have hsub : Set.uIcc s t ⊆ Set.Icc 0 T := by
    intro x hx
    exact ⟨(le_min hs.1 ht.1).trans hx.1, hx.2.trans (max_le hs.2 ht.2)⟩
  have hAC : AbsolutelyContinuousOnInterval f s t :=
    (hf.mono hsub).absolutelyContinuousOnInterval
  have hIoc : ∀ᵐ x ∂(volume.restrict (Set.uIoc s t)), |deriv f x| ≤ A :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (Set.uIoc_subset_uIcc.trans hsub) hder
  have hnorm : ‖∫ x in s..t, deriv f x‖ ≤ A * |t - s| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    exact (ae_restrict_iff' measurableSet_uIoc).mp hIoc
  have hsub' : |f s - f t| = |∫ x in s..t, deriv f x| := by
    rw [hAC.integral_deriv_eq_sub, abs_sub_comm]
  rw [Real.dist_eq, hsub']
  calc |∫ x in s..t, deriv f x|
      = ‖∫ x in s..t, deriv f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ (A : ℝ) * |t - s| := hnorm
    _ = (A : ℝ) * dist s t := by rw [Real.dist_eq, abs_sub_comm]

/-- The `c√c` height is `3/2`-Lipschitz on the whole exposure-time
interval, including at zero-cost times (ε-regularization argument). -/
theorem lipschitzOn_costThreeHalves_exposure
    {T : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (_hT : 0 ≤ T) (hy : LipschitzWith K y)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hu : ∀ t, ‖u t‖ ≤ 1)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t) :
    LipschitzOnWith (3 / 2 : NNReal)
      (fun t => costThreeHalves (euclideanExposureCost (y t)))
      (Set.Icc 0 T) := by
  set q := fun t => euclideanSquaredCostCLM (y t) with hqdef
  have hq_lip : LipschitzWith _ q :=
    euclideanSquaredCostCLM.lipschitz.comp hy
  have hq_nn : ∀ t ∈ Set.Icc 0 T, 0 ≤ q t :=
    fun t ht => euclideanSquaredCostCLM_nonneg (hdom t ht)
  have hqCost : ∀ t, Real.sqrt (q t) = euclideanExposureCost (y t) :=
    fun _ => rfl
  have hbound : ∀ ε : ℝ, 0 < ε → ∃ C : NNReal,
      LipschitzOnWith C (fun t => regularizedHeight ε (q t)) (Set.Icc 0 T) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
        |deriv (fun t => regularizedHeight ε (q t)) t| ≤ 3 / 2 := by
    intro ε hε
    have hpre : ∃ C : NNReal, LipschitzOnWith C
        (fun t => regularizedHeight ε (q t)) (Set.Icc 0 T) := by
      apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
      intro t ht
      obtain ⟨C', U, hU, hLip⟩ :=
        (contDiffAt_regularizedHeight hε (hq_nn t ht)).exists_lipschitzOnWith
      have hmem : q ⁻¹' U ∈ 𝓝 t :=
        hq_lip.continuous.continuousAt.preimage_mem_nhds hU
      refine ⟨C' * (‖euclideanSquaredCostCLM‖₊ * K), q ⁻¹' U,
        nhdsWithin_le_nhds hmem, ?_⟩
      exact hLip.comp hq_lip.lipschitzOnWith (fun r hr => hr)
    obtain ⟨C, hC⟩ := hpre
    refine ⟨C, hC, ?_⟩
    filter_upwards [hode, ae_restrict_mem measurableSet_Icc] with t ht htm
    have hq' : HasDerivAt q
        (euclideanSquaredCostCLM (euclideanBfield (y t) (u t))) t :=
      euclideanSquaredCostCLM.hasFDerivAt.comp_hasDerivAt t ht
    have hqb := abs_euclideanSquaredCostCLM_Bfield_le (hdom t htm) (hu t)
    have hg := hasDerivAt_regularizedHeight hε (hq_nn t htm)
    have hder := (hg.scomp t hq').deriv
    show |deriv (regularizedHeight ε ∘ q) t| ≤ 3 / 2
    rw [hder, smul_eq_mul]
    have hB0 : 0 < Real.sqrt (Real.sqrt (q t + ε)) := by
      have : 0 < q t + ε := by linarith [hq_nn t htm]
      exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr this)
    have hB : Real.sqrt (euclideanExposureCost (y t)) ≤
        Real.sqrt (Real.sqrt (q t + ε)) := by
      rw [← hqCost t]
      exact Real.sqrt_le_sqrt
        (Real.sqrt_le_sqrt (le_add_of_nonneg_right hε.le))
    have hq'b : |euclideanSquaredCostCLM (euclideanBfield (y t) (u t))| ≤
        2 * Real.sqrt (Real.sqrt (q t + ε)) := hqb.trans
      (mul_le_mul_of_nonneg_left hB (by norm_num))
    calc |euclideanSquaredCostCLM (euclideanBfield (y t) (u t)) *
          (3 / (4 * Real.sqrt (Real.sqrt (q t + ε))))|
        = |euclideanSquaredCostCLM (euclideanBfield (y t) (u t))| *
          (3 / (4 * Real.sqrt (Real.sqrt (q t + ε)))) := by
          rw [abs_mul, abs_of_pos
            (div_pos (by norm_num) (mul_pos (by norm_num) hB0))]
      _ ≤ (2 * Real.sqrt (Real.sqrt (q t + ε))) *
          (3 / (4 * Real.sqrt (Real.sqrt (q t + ε)))) := by
          apply mul_le_mul hq'b (le_refl _)
            (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hB0.le))
            (mul_nonneg (by norm_num) hB0.le)
      _ = 3 / 2 := by
        rw [mul_div, div_eq_iff (mul_ne_zero (by norm_num) hB0.ne')]
        ring
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  have key : ∀ ε : ℝ, 0 < ε →
      dist (regularizedHeight ε (q s)) (regularizedHeight ε (q t)) ≤
        (3 / 2 : ℝ) * dist s t := fun ε hε => by
    obtain ⟨C, hC, hder⟩ := hbound ε hε
    have hder' : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
        |deriv (fun t => regularizedHeight ε (q t)) t| ≤ ((3 / 2 : NNReal) : ℝ) :=
      hder
    have h := lipschitzOnWith_of_lipschitzOn_ae_deriv_le (A := 3 / 2) hC hder'
    have h' := h.dist_le_mul s hs t ht
    push_cast at h'
    exact h'
  have htend : Tendsto (fun ε : ℝ =>
        dist (regularizedHeight ε (q s)) (regularizedHeight ε (q t)))
      (𝓝[>] 0) (𝓝 (dist (regularizedHeight 0 (q s))
        (regularizedHeight 0 (q t)))) := by
    apply Tendsto.dist
    · exact ((Real.continuous_sqrt.comp
          (continuous_const.add continuous_id)).mul
        (Real.continuous_sqrt.comp (Real.continuous_sqrt.comp
          (continuous_const.add continuous_id)))).continuousAt.tendsto
          |>.mono_left nhdsWithin_le_nhds
    · exact ((Real.continuous_sqrt.comp
          (continuous_const.add continuous_id)).mul
        (Real.continuous_sqrt.comp (Real.continuous_sqrt.comp
          (continuous_const.add continuous_id)))).continuousAt.tendsto
          |>.mono_left nhdsWithin_le_nhds
  have hlim := le_of_tendsto htend
    (eventually_nhdsWithin_iff.mpr
      (Filter.Eventually.of_forall fun ε hε => key ε hε))
  have hid : ∀ τ, regularizedHeight 0 (q τ) =
      costThreeHalves (euclideanExposureCost (y τ)) := fun τ => by
    show Real.sqrt (q τ + 0) * Real.sqrt (Real.sqrt (q τ + 0)) = _
    simp only [add_zero, costThreeHalves, hqCost]
  rw [hid s, hid t] at hlim
  push_cast
  exact hlim

end CZExposure
