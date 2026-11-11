module
public import Mathlib

/-! The singular derivative of |s|^a is cancelled by the factor s.
This proves C¹ regularity, including continuity of the derivative at zero. -/
@[expose] public section
noncomputable section
namespace CZExposure.RootRegularity
open Filter Topology

def root (a s : ℝ) : ℝ := |s| ^ a

theorem root_zero {a : ℝ} (ha : 0 < a) : root a 0 = 0 := by
  simp [root, Real.zero_rpow ha.ne']

theorem root_continuous {a : ℝ} (ha : 0 < a) : Continuous (root a) :=
  (Real.continuous_rpow_const ha.le).comp continuous_abs

theorem root_deriv {a s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (root a) (a * root a s / s) s := by
  have hn : |s| ≠ 0 := abs_ne_zero.mpr hs
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · convert (hasDerivAt_abs_neg hneg).rpow_const (p := a) (Or.inl hn) using 1
    rw [Real.rpow_sub_one hn]
    simp only [root, abs_of_neg hneg]
    field_simp
  · convert (hasDerivAt_abs_pos hpos).rpow_const (p := a) (Or.inl hn) using 1
    rw [Real.rpow_sub_one hn]
    simp only [root, abs_of_pos hpos]
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weighted (a : ℝ) (C : ℝ → E) (s : ℝ) : E := s • C (root a s)
def weightedDeriv (a : ℝ) (C : ℝ → E) (s : ℝ) : E :=
  C (root a s) + (a * root a s) • deriv C (root a s)

theorem weighted_zero_deriv {a : ℝ} (ha : 0 < a) {C : ℝ → E}
    (hC : ContinuousAt C 0) : HasDerivAt (weighted a C) (C 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hr : Tendsto (root a) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [root_zero ha] using (root_continuous ha).tendsto 0
  apply (hC.tendsto.comp hr).mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hn : s ≠ 0 := hs
  simp [weighted, smul_smul, hn]

theorem weighted_hasDeriv {a : ℝ} (ha : 0 < a) {C : ℝ → E}
    (hC : ContDiff ℝ 1 C) (s : ℝ) :
    HasDerivAt (weighted a C) (weightedDeriv a C s) s := by
  by_cases hs : s = 0
  · subst s
    simpa [weightedDeriv, root_zero ha] using weighted_zero_deriv ha hC.continuous.continuousAt
  · have hr := root_deriv (a := a) hs
    have hc := (hC.differentiable one_ne_zero (root a s)).hasDerivAt.scomp s hr
    convert (hasDerivAt_id s).smul hc using 1
    simp only [weightedDeriv, id_eq, one_smul, smul_smul, Function.comp_apply]
    rw [mul_div_cancel₀ _ hs]
    abel

theorem weightedDeriv_continuous {a : ℝ} (ha : 0 < a) {C : ℝ → E}
    (hC : ContDiff ℝ 1 C) : Continuous (weightedDeriv a C) := by
  have hd := (contDiff_one_iff_deriv.mp hC).2
  exact (hC.continuous.comp (root_continuous ha)).add
    ((continuous_const.mul (root_continuous ha)).smul (hd.comp (root_continuous ha)))

theorem weighted_contDiff {a : ℝ} (ha : 0 < a) {C : ℝ → E}
    (hC : ContDiff ℝ 1 C) : ContDiff ℝ 1 (weighted a C) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (weighted_hasDeriv ha hC s).differentiableAt, ?_⟩
  have hd : deriv (weighted a C) = weightedDeriv a C :=
    funext fun s => (weighted_hasDeriv ha hC s).deriv
  rw [hd]
  exact weightedDeriv_continuous ha hC

def glue (f g : ℝ → E) (s : ℝ) : E := if 0 ≤ s then f s else g s

theorem glue_hasDeriv {f g f' g' : ℝ → E}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hg : ∀ s, HasDerivAt g (g' s) s)
    (h0 : f 0 = g 0) (h1 : f' 0 = g' 0) (s : ℝ) :
    HasDerivAt (glue f g) (glue f' g' s) s := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have he : glue f g =ᶠ[𝓝 s] g := by
      filter_upwards [eventually_lt_nhds hs] with t ht
      exact if_neg (not_le.mpr ht)
    simpa [glue, not_le.mpr hs] using (hg s).congr_of_eventuallyEq he
  · subst s
    rw [hasDerivAt_iff_tendsto_slope]
    have hh := (hf 0).tendsto_slope.if' (p := fun s : ℝ => 0 ≤ s)
      (by simpa only [h1] using (hg 0).tendsto_slope)
    convert hh using 1
    · funext t
      by_cases ht : 0 ≤ t <;> simp [glue, slope, ht, h0]
    · simp [glue]
  · have he : glue f g =ᶠ[𝓝 s] f := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      exact if_pos ht.le
    simpa [glue, hs.le] using (hf s).congr_of_eventuallyEq he

theorem glue_contDiff {f g : ℝ → E} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (h0 : f 0 = g 0) (h1 : deriv f 0 = deriv g 0) : ContDiff ℝ 1 (glue f g) := by
  have hd := glue_hasDeriv (fun s => (hf.differentiable one_ne_zero s).hasDerivAt)
    (fun s => (hg.differentiable one_ne_zero s).hasDerivAt) h0 h1
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hd s).differentiableAt, ?_⟩
  have he : deriv (glue f g) = glue (deriv f) (deriv g) := funext fun s => (hd s).deriv
  rw [he]
  apply continuous_if
  · intro s hs
    have hs0 : s = 0 := by
      change s ∈ frontier (Set.Ici (0 : ℝ)) at hs
      simpa only [frontier_Ici, Set.mem_singleton_iff] using hs
    simpa only [hs0] using h1
  · exact (contDiff_one_iff_deriv.mp hf).2.continuousOn
  · exact (contDiff_one_iff_deriv.mp hg).2.continuousOn

theorem glued_weighted_contDiff {a : ℝ} (ha : 0 < a) {C D : ℝ → E}
    (hC : ContDiff ℝ 1 C) (hD : ContDiff ℝ 1 D) (h0 : C 0 = D 0) :
    ContDiff ℝ 1 (glue (weighted a C) (weighted a D)) := by
  apply glue_contDiff (weighted_contDiff ha hC) (weighted_contDiff ha hD)
  · simp [weighted]
  · rw [(weighted_zero_deriv ha hC.continuous.continuousAt).deriv,
      (weighted_zero_deriv ha hD.continuous.continuousAt).deriv, h0]

end CZExposure.RootRegularity
