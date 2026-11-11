module
public import RequestProject.AppendixE.ExposureArc
public import Mathlib.Order.Hom.Set
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The exposure clock and its inverse (Appendix E support)

For a Euclidean arc with finite `exposureTime`, a uniform bound on the
Euclidean velocity along the closed domain gives a quantitative lower
increment bound on the `exposureClock`, hence strict monotonicity, an order
isomorphism `Icc 0 length ≃o Icc 0 exposureTime.toReal`, and a Lipschitz
inverse.  Composing the path with the inverse gives the exposure-time
parameterization, still inside the compact domain with preserved endpoints.

No derivative of the reparameterized path is computed here; the
inverse/chain-rule and exceptional-set transfer are completed in
`ExposureReparamODE.lean` (`IsDirectedBy` remains an input).  The exposure
time is a weighted cost, not the physical duration.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set intervalIntegral

/-- The transported field is bounded on the Euclidean exposure domain by an
explicit bound built from the ambient `Bfield` bound and the operator norm of
the coordinate change.  The canonical equivalence is not asserted isometric. -/
theorem euclideanBfield_bounded :
    ∃ K : NNReal, 0 < K ∧
      ∀ z ∈ euclideanExposureDomain, ∀ u : ℂ, ‖u‖ ≤ 1 →
        ‖euclideanBfield z u‖ ≤ (K : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := Bfield_bounded
  refine ⟨‖exposureEuclideanEquiv.toContinuousLinearMap‖₊ * C.toNNReal + 1,
    by positivity, ?_⟩
  intro z hz u hu
  obtain ⟨y, hy, rfl⟩ := hz
  rw [euclideanBfield_equiv]
  calc ‖exposureEuclideanEquiv (Bfield y u)‖
      ≤ ‖exposureEuclideanEquiv.toContinuousLinearMap‖ * ‖Bfield y u‖ :=
        exposureEuclideanEquiv.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖exposureEuclideanEquiv.toContinuousLinearMap‖ * C :=
        mul_le_mul_of_nonneg_left (hbound y hy u hu) (norm_nonneg _)
    _ ≤ (‖exposureEuclideanEquiv.toContinuousLinearMap‖₊ * C.toNNReal + 1 :
          NNReal) := by
        rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one,
          Real.coe_toNNReal', max_eq_left hC]
        exact le_add_of_nonneg_right zero_le_one

theorem EuclideanExposureFlow.velocity_bounded (F : EuclideanExposureFlow) :
    ∃ K : NNReal, 0 < K ∧
      ∀ z ∈ euclideanExposureDomain, ‖F.velocity z‖ ≤ (K : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := euclideanBfield_bounded
  exact ⟨K, hK, fun z hz => hbound z hz _ (F.control_bound z)⟩

namespace EuclideanArc

theorem inverseSpeed_lower_bound_ae (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤) {K : NNReal}
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ)) :
    ∀ᵐ s ∂γ.parameterMeasure, (K : ℝ)⁻¹ ≤ γ.inverseSpeed F s := by
  filter_upwards [γ.ae_velocity_ne_zero F hfinite,
    ae_restrict_mem measurableSet_Icc] with s hv hs
  have hpos : 0 < ‖F.velocity (γ.path s)‖ := norm_pos_iff.mpr hv
  exact inv_anti₀ hpos (hspeed s hs)

theorem exposureClock_increment_lower_bound (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤) {K : NNReal}
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ))
    {a b : ℝ} (ha : a ∈ Set.Icc 0 γ.length)
    (hb : b ∈ Set.Icc 0 γ.length) (hab : a ≤ b) :
    (b - a) / (K : ℝ) ≤ γ.exposureClock F b - γ.exposureClock F a := by
  have hmem : ∀ x ∈ Set.Icc 0 γ.length, x ∈ Set.uIcc 0 γ.length := by
    rw [Set.uIcc_of_le γ.length_pos.le]; exact fun x hx => hx
  have h0a : IntervalIntegrable (γ.inverseSpeed F) volume 0 a :=
    (γ.intervalIntegrable_inverseSpeed F hfinite).mono_set
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc (hmem a ha))
  have h0b : IntervalIntegrable (γ.inverseSpeed F) volume 0 b :=
    (γ.intervalIntegrable_inverseSpeed F hfinite).mono_set
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc (hmem b hb))
  have hab' : IntervalIntegrable (γ.inverseSpeed F) volume a b :=
    (γ.intervalIntegrable_inverseSpeed F hfinite).mono_set
      (Set.uIcc_subset_uIcc (hmem a ha) (hmem b hb))
  have hsub : Set.Icc a b ⊆ Set.Icc 0 γ.length :=
    Set.Icc_subset_Icc ha.1 hb.2
  have hle : ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      (K : ℝ)⁻¹ ≤ γ.inverseSpeed F s :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub
      (γ.inverseSpeed_lower_bound_ae F hfinite hspeed)
  have hdiff : γ.exposureClock F b - γ.exposureClock F a =
      ∫ q in a..b, γ.inverseSpeed F q :=
    intervalIntegral.integral_interval_sub_left h0b h0a
  calc (b - a) / (K : ℝ) = (b - a) * (K : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ = ∫ q in a..b, (K : ℝ)⁻¹ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ q in a..b, γ.inverseSpeed F q :=
        intervalIntegral.integral_mono_ae_restrict hab
          intervalIntegral.intervalIntegrable_const hab' hle
    _ = γ.exposureClock F b - γ.exposureClock F a := hdiff.symm

theorem strictMonoOn_exposureClock_of_speed_bound (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    {K : NNReal} (hK : 0 < K)
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ)) :
    StrictMonoOn (γ.exposureClock F) (Set.Icc 0 γ.length) := by
  intro a ha b hb hab
  have hpos : 0 < (b - a) / (K : ℝ) :=
    div_pos (sub_pos.mpr hab) (by exact_mod_cast hK)
  exact sub_pos.mp (lt_of_lt_of_le hpos
    (γ.exposureClock_increment_lower_bound F hfinite hspeed ha hb hab.le))

theorem exposureClock_dist_lower_bound (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤) {K : NNReal}
    (hK : 0 < K)
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ))
    {a b : ℝ} (ha : a ∈ Set.Icc 0 γ.length) (hb : b ∈ Set.Icc 0 γ.length) :
    dist a b ≤ (K : ℝ) * dist (γ.exposureClock F a) (γ.exposureClock F b) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rcases le_total a b with hab | hab
  · have hmono := (γ.strictMonoOn_exposureClock_of_speed_bound F hfinite hK
      hspeed).monotoneOn ha hb hab
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub,
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
    have hinc := γ.exposureClock_increment_lower_bound F hfinite hspeed
      ha hb hab
    rw [div_le_iff₀ hK', mul_comm] at hinc
    exact hinc
  · have hmono := (γ.strictMonoOn_exposureClock_of_speed_bound F hfinite hK
      hspeed).monotoneOn hb ha hab
    rw [dist_comm a b, dist_comm (γ.exposureClock F a) (γ.exposureClock F b),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub,
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
    have hinc := γ.exposureClock_increment_lower_bound F hfinite hspeed
      hb ha hab
    rw [div_le_iff₀ hK', mul_comm] at hinc
    exact hinc

theorem strictMonoOn_exposureClock (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    StrictMonoOn (γ.exposureClock F) (Set.Icc 0 γ.length) := by
  obtain ⟨K, hK, hbound⟩ := F.velocity_bounded
  exact γ.strictMonoOn_exposureClock_of_speed_bound F hfinite hK
    (fun s hs => hbound _ (hdom hs))

theorem exposureTime_toReal_pos (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    0 < (γ.exposureTime F).toReal := by
  have h := γ.strictMonoOn_exposureClock F hfinite hdom
    (Set.left_mem_Icc.mpr γ.length_pos.le)
    (Set.right_mem_Icc.mpr γ.length_pos.le) γ.length_pos
  rw [γ.exposureClock_zero, γ.exposureClock_terminal F hfinite] at h
  exact h

theorem exposureClock_image_interval (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    γ.exposureClock F '' Set.Icc 0 γ.length =
      Set.Icc 0 (γ.exposureTime F).toReal := by
  have hcont : ContinuousOn (γ.exposureClock F) (Set.Icc 0 γ.length) := by
    have hac := (γ.absolutelyContinuous_exposureClock F hfinite).continuousOn
    rwa [Set.uIcc_of_le γ.length_pos.le] at hac
  have him := ContinuousOn.image_Icc_of_monotoneOn γ.length_pos.le hcont
    (γ.strictMonoOn_exposureClock F hfinite hdom).monotoneOn
  rw [γ.exposureClock_zero, γ.exposureClock_terminal F hfinite] at him
  exact him

/-- The clock as an order isomorphism between the parameter interval and the
exposure-time interval. -/
def clockOrderIso (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    Set.Icc (0 : ℝ) γ.length ≃o Set.Icc (0 : ℝ) (γ.exposureTime F).toReal :=
  ((γ.strictMonoOn_exposureClock F hfinite hdom).orderIso _ _).trans
    (OrderIso.setCongr _ _ (γ.exposureClock_image_interval F hfinite hdom))

@[simp] theorem coe_clockOrderIso_apply (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (s : Set.Icc (0 : ℝ) γ.length) :
    (γ.clockOrderIso F hfinite hdom s : ℝ) = γ.exposureClock F (s : ℝ) := rfl

/-- The inverse clock on the real exposure-time interval.  This is not a
global inverse on ℝ. -/
def clockInverse (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    Set.Icc (0 : ℝ) (γ.exposureTime F).toReal → Set.Icc (0 : ℝ) γ.length :=
  (γ.clockOrderIso F hfinite hdom).symm

@[simp] theorem exposureClock_clockInverse (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : Set.Icc (0 : ℝ) (γ.exposureTime F).toReal) :
    γ.exposureClock F (γ.clockInverse F hfinite hdom t : ℝ) = (t : ℝ) := by
  rw [← γ.coe_clockOrderIso_apply F hfinite hdom
        (γ.clockInverse F hfinite hdom t)]
  exact congrArg Subtype.val
    ((γ.clockOrderIso F hfinite hdom).apply_symm_apply t)

@[simp] theorem clockInverse_clockOrderIso (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (s : Set.Icc (0 : ℝ) γ.length) :
    γ.clockInverse F hfinite hdom (γ.clockOrderIso F hfinite hdom s) = s :=
  (γ.clockOrderIso F hfinite hdom).symm_apply_apply s

theorem lipschitz_clockInverse (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {K : NNReal} (hK : 0 < K)
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ)) :
    LipschitzWith K (γ.clockInverse F hfinite hdom) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := γ.exposureClock_dist_lower_bound F hfinite hK hspeed
    (γ.clockInverse F hfinite hdom x).property
    (γ.clockInverse F hfinite hdom y).property
  rw [γ.exposureClock_clockInverse F hfinite hdom x,
    γ.exposureClock_clockInverse F hfinite hdom y] at h
  exact h

theorem exists_lipschitz_clockInverse (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    ∃ K : NNReal, 0 < K ∧ LipschitzWith K (γ.clockInverse F hfinite hdom) := by
  obtain ⟨K, hK, hbound⟩ := F.velocity_bounded
  exact ⟨K, hK, γ.lipschitz_clockInverse F hfinite hdom hK
    (fun s hs => hbound _ (hdom hs))⟩

/-- The path composed with the inverse clock: the exposure-time
parameterization on `Icc 0 exposureTime.toReal`. -/
def reparameterizedPath (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : Set.Icc (0 : ℝ) (γ.exposureTime F).toReal) : ExposureEuclidean :=
  γ.path (γ.clockInverse F hfinite hdom t : ℝ)

theorem lipschitz_reparameterizedPath (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {K : NNReal} (hK : 0 < K)
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ)) :
    LipschitzWith K (γ.reparameterizedPath F hfinite hdom) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 := γ.lipschitz.dist_le_mul
    (γ.clockInverse F hfinite hdom x : ℝ) (γ.clockInverse F hfinite hdom y : ℝ)
  have h2 := (γ.lipschitz_clockInverse F hfinite hdom hK hspeed).dist_le_mul x y
  rw [NNReal.coe_one, one_mul] at h1
  exact h1.trans h2

theorem reparameterizedPath_mem_domain (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : Set.Icc (0 : ℝ) (γ.exposureTime F).toReal) :
    γ.reparameterizedPath F hfinite hdom t ∈ euclideanExposureDomain :=
  hdom (γ.clockInverse F hfinite hdom t).property

theorem clockInverse_zero (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    (γ.clockInverse F hfinite hdom
      ⟨0, le_rfl, ENNReal.toReal_nonneg⟩ : ℝ) = 0 := by
  apply (γ.strictMonoOn_exposureClock F hfinite hdom).injOn
    (γ.clockInverse F hfinite hdom _).property
    (Set.left_mem_Icc.mpr γ.length_pos.le)
  rw [γ.exposureClock_clockInverse F hfinite hdom, γ.exposureClock_zero]

theorem clockInverse_terminal (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    (γ.clockInverse F hfinite hdom
      ⟨(γ.exposureTime F).toReal, ENNReal.toReal_nonneg, le_rfl⟩ : ℝ) =
      γ.length := by
  apply (γ.strictMonoOn_exposureClock F hfinite hdom).injOn
    (γ.clockInverse F hfinite hdom _).property
    (Set.right_mem_Icc.mpr γ.length_pos.le)
  rw [γ.exposureClock_clockInverse F hfinite hdom,
    γ.exposureClock_terminal F hfinite]

theorem reparameterizedPath_zero (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    γ.reparameterizedPath F hfinite hdom
      ⟨0, le_rfl, ENNReal.toReal_nonneg⟩ = γ.path 0 := by
  show γ.path (γ.clockInverse F hfinite hdom
    ⟨0, le_rfl, ENNReal.toReal_nonneg⟩ : ℝ) = γ.path 0
  rw [γ.clockInverse_zero F hfinite hdom]

theorem reparameterizedPath_terminal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    γ.reparameterizedPath F hfinite hdom
      ⟨(γ.exposureTime F).toReal, ENNReal.toReal_nonneg, le_rfl⟩ =
      γ.path γ.length := by
  show γ.path (γ.clockInverse F hfinite hdom
    ⟨(γ.exposureTime F).toReal, ENNReal.toReal_nonneg, le_rfl⟩ : ℝ) =
      γ.path γ.length
  rw [γ.clockInverse_terminal F hfinite hdom]

end EuclideanArc

end CZExposure
