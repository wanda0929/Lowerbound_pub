import RequestProject.AppendixE.ActiveDynamics
import RequestProject.AppendixE.PulseSegment
import RequestProject.AppendixE.OverlapArea
import LowerBoundCZ.Fiber

noncomputable section

namespace CZExposure

open MeasureTheory Set Filter ComplexConjugate
open scoped Topology

/-- The exact overlap velocity, shared by the physical and fiber arguments. -/
def overlapVelocity (x : State) (u : ℂ) : ℂ :=
  -(Complex.I * (Real.sqrt 2 : ℂ) / 2) * conj (r2 x) * u * (r1 x) ^ 2

theorem PhysicalSegment.ae_overlap_dynamics (P : PhysicalSegment) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 P.duration)),
      HasDerivAt (fun s => zObs (P.path s)) (overlapVelocity (P.path t) (P.control t)) t ∧
      HasDerivAt (fun s => (zObs (P.path s)).re)
        (overlapVelocity (P.path t) (P.control t)).re t := by
  filter_upwards [P.ae_hasDerivAt_path] with t ht
  have hz := (contDiff_zObs.differentiable (by simp) (P.path t)).hasFDerivAt.comp_hasDerivAt t ht
  simp only [Function.comp_def, fderiv_zObs_vf] at hz
  change HasDerivAt (fun s => zObs (P.path s)) (overlapVelocity (P.path t) (P.control t)) t at hz
  exact ⟨hz, by simpa only [Function.comp_def, Complex.reCLM_apply] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz⟩

theorem overlap_speed_bound (x : State) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |(overlapVelocity x u).re| ≤ ‖r1 x‖ ^ 2 * Real.sqrt (‖r2 x‖ ^ 2) / Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  calc
    _ ≤ ‖overlapVelocity x u‖ := Complex.abs_re_le_norm _
    _ = (Real.sqrt 2 / 2 * ‖r2 x‖ * ‖r1 x‖ ^ 2) * ‖u‖ := by
      simp [overlapVelocity, norm_pow, Complex.norm_real,
        abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))]
      ring
    _ ≤ Real.sqrt 2 / 2 * ‖r2 x‖ * ‖r1 x‖ ^ 2 := by
      exact mul_le_of_le_one_right (by positivity) hu
    _ = _ := by
      rw [Real.sqrt_sq (norm_nonneg _)]
      apply (eq_div_iff hn.ne').mpr
      ring_nf
      simp [hs]
      ring

/-- Feasible populations give the actual infimum comparison, not a
cost/speed inequality postulated as an input. -/
theorem cFib_le_density {ξ x y : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1)
    (hξ : ξ ≤ LowerBoundCZ.fiberEnvelope x y) :
    LowerBoundCZ.cFib ξ ≤ LowerBoundCZ.fiberDensity x y := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨a, b, ha, _, hb, _, _, rfl⟩
    exact LowerBoundCZ.fiberDensity_nonneg ha hb
  · exact ⟨x, y, hx, hx1, hy, hy1, hξ, rfl⟩

theorem fiber_product_bound {ξ x y qdot : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hξ : ξ ≤ LowerBoundCZ.fiberEnvelope x y)
    (hspd : |qdot| ≤ x * Real.sqrt y / Real.sqrt 2) :
    LowerBoundCZ.cFib ξ * |qdot| ≤ (2 * x + y) / 4 := by
  by_cases hq : qdot = 0
  · simp only [hq, abs_zero, mul_zero]
    positivity
  have hpos : 0 < x * Real.sqrt y / Real.sqrt 2 :=
    (abs_pos.mpr hq).trans_le hspd
  have hx' : 0 < x := by
    by_contra h
    have : x = 0 := le_antisymm (not_lt.mp h) hx
    simp [this] at hpos
  have hy' : 0 < y := by
    by_contra h
    have : y = 0 := le_antisymm (not_lt.mp h) hy
    simp [this] at hpos
  exact (mul_le_mul_of_nonneg_right (cFib_le_density hx' hx1 hy' hy1 hξ)
    (abs_nonneg _)).trans (LowerBoundCZ.fiber_pointwise_ratio hx' hy' hspd)

theorem overlap_envelope {x : State} (hx : x ∈ Xset) :
    |(zObs x).re| ≤ LowerBoundCZ.fiberEnvelope (‖r1 x‖ ^ 2) (‖r2 x‖ ^ 2) := by
  have hnorm1 := hx.1
  have hnorm2 := hx.2
  have he1 : 1 - ‖r1 x‖ ^ 2 = ‖g1 x‖ ^ 2 := by linarith
  have he2 : 1 - ‖r2 x‖ ^ 2 = ‖g2 x‖ ^ 2 := by linarith
  calc
    _ ≤ ‖zObs x‖ := Complex.abs_re_le_norm _
    _ ≤ ‖g2 x‖ * ‖g1 x‖ ^ 2 + Real.sqrt 2 * ‖r2 x‖ * ‖g1 x‖ * ‖r1 x‖ :=
      LowerBoundCZ.abs_overlap_le_moduli _ _ _ _
    _ = _ := by
      unfold LowerBoundCZ.fiberEnvelope
      rw [he1, he2, Real.sqrt_sq (norm_nonneg _)]
      simp only [mul_assoc]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _)]
      simp only [Real.sqrt_sq (norm_nonneg _)]
      ring

/-- The fiber cost inequality at the actual physical state and velocity,
including zero populations and zero overlap speed. -/
theorem physical_fiber_product {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    LowerBoundCZ.cFib |(zObs x).re| * |(overlapVelocity x u).re| ≤ cost x := by
  exact fiber_product_bound (sq_nonneg _) (by have := hx.1; nlinarith [sq_nonneg ‖g1 x‖])
    (sq_nonneg _) (by have := hx.2; nlinarith [sq_nonneg ‖g2 x‖])
    (overlap_envelope hx) (overlap_speed_bound x hu)

theorem PhysicalSegment.ae_fiber_product (P : PhysicalSegment) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 P.duration)),
      HasDerivAt (fun s => (zObs (P.path s)).re)
        (overlapVelocity (P.path t) (P.control t)).re t ∧
      LowerBoundCZ.cFib |(zObs (P.path t)).re| *
        |(overlapVelocity (P.path t) (P.control t)).re| ≤ cost (P.path t) := by
  filter_upwards [P.ae_overlap_dynamics, ae_restrict_mem measurableSet_Icc] with t ht hi
  exact ⟨ht.2, physical_fiber_product (P.path_mem t hi) (P.control_bound t hi)⟩

/-- A smooth function of the physical overlap is absolutely continuous
along the integral trajectory. -/
theorem PhysicalSegment.overlap_composition_ac (P : PhysicalSegment)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    AbsolutelyContinuousOnInterval (fun t => F (zObs (P.path t)).re) 0 P.duration := by
  have hc : ContDiff ℝ 1 (fun x : State => F (zObs x).re) :=
    hF.comp (Complex.reCLM.contDiff.comp (contDiff_zObs.of_le (by simp)))
  obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : State) 1) (isCompact_closedBall (0 : State) 1)
  have hl : LipschitzOnWith (K * 1) (fun t => F (zObs (P.path t)).re)
      (Icc 0 P.duration) :=
    hK.comp P.path_lipschitzOn (fun t ht => Xset_subset_closedBall (P.path_mem t ht))
  rw [← uIcc_of_le P.duration_nonneg] at hl
  exact hl.absolutelyContinuousOnInterval

/-- Smooth minorants give a physical lower bound. The full measurable
density is handled below by `Pulse.fiber_integrable_and_bound`. -/
theorem Pulse.fiber_smooth_lower_bound (P : Pulse) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hminor : ∀ q : ℝ, |deriv F q| ≤ LowerBoundCZ.cFib |q|) :
    F 1 - F (-1) ≤ P.exposure := by
  let Q := P.toPhysicalSegment
  have hac : AbsolutelyContinuousOnInterval (fun t => F (zObs (P.x t)).re) 0 P.S :=
    Q.overlap_composition_ac hF
  have hder : ∀ᵐ t ∂(volume.restrict (Icc 0 P.S)),
      -deriv (fun s => F (zObs (P.x s)).re) t ≤ cost (P.x t) := by
    filter_upwards [Q.ae_fiber_product] with t ht
    have hd := ((hF.differentiable (by norm_num)) _).hasDerivAt.comp t ht.1
    change HasDerivAt (fun s => F (zObs (P.x s)).re)
      (deriv F (zObs (P.x t)).re * (overlapVelocity (P.x t) (P.u t)).re) t at hd
    rw [hd.deriv]
    have hm := mul_le_mul_of_nonneg_right (hminor (zObs (P.x t)).re)
      (abs_nonneg (overlapVelocity (P.x t) (P.u t)).re)
    have habs : -(deriv F (zObs (P.x t)).re * (overlapVelocity (P.x t) (P.u t)).re) ≤
        |deriv F (zObs (P.x t)).re| * |(overlapVelocity (P.x t) (P.u t)).re| := by
      rw [← abs_mul]
      exact neg_le_abs _
    exact habs.trans (hm.trans ht.2)
  have hi := intervalIntegral.integral_mono_ae_restrict P.S_nonneg
    hac.intervalIntegrable_deriv.neg Q.cost_intervalIntegrable hder
  simp only [Pi.neg_apply] at hi
  rw [intervalIntegral.integral_neg, hac.integral_deriv_eq_sub] at hi
  have he := P.overlap_endpoints
  simpa only [Q, Pulse.toPhysicalSegment, he.1, he.2, Complex.one_re,
    Complex.neg_re, neg_sub, Pulse.exposure] using hi

theorem fiber_smooth_lower_bound_Cstar {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hminor : ∀ q : ℝ, |deriv F q| ≤ LowerBoundCZ.cFib |q|) :
    ((F 1 - F (-1) : ℝ) : EReal) ≤ Cstar := by
  apply le_iInf
  intro P
  exact_mod_cast P.fiber_smooth_lower_bound hF hminor

theorem cFib_nonneg (ξ : ℝ) : 0 ≤ LowerBoundCZ.cFib ξ := by
  apply Real.sInf_nonneg
  rintro t ⟨x, y, hx, _, hy, _, _, rfl⟩
  exact LowerBoundCZ.fiberDensity_nonneg hx hy

/-- The fiber is nonempty at every interior level. No endpoint value
or a numerical minimizer is used in the integral argument. -/
theorem fiber_nonempty {ξ : ℝ} (hξ : ξ < 1) :
    {t | ∃ x y : ℝ, 0 < x ∧ x ≤ 1 ∧ 0 < y ∧ y ≤ 1 ∧
      ξ ≤ LowerBoundCZ.fiberEnvelope x y ∧ t = LowerBoundCZ.fiberDensity x y}.Nonempty := by
  let x : ℝ := min (1 / 2) ((1 - ξ) / 2)
  have hx : 0 < x := lt_min (by norm_num) (by linarith)
  have hxhalf : x ≤ 1 / 2 := min_le_left _ _
  have hxξ : x ≤ (1 - ξ) / 2 := min_le_right _ _
  have hx1 : x ≤ 1 := by linarith
  refine ⟨_, x, x, hx, hx1, hx, hx1, ?_, rfl⟩
  have hs0 : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
  have hss : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hs : 1 - x ≤ Real.sqrt (1 - x) := by
    nlinarith [sq_nonneg (Real.sqrt (1 - x) - (1 - x))]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1 - x by linarith)
  unfold LowerBoundCZ.fiberEnvelope
  nlinarith [sq_nonneg x, Real.sqrt_nonneg (2 * x * (1 - x) * x)]

theorem cFib_monotoneOn : MonotoneOn LowerBoundCZ.cFib (Iio 1) := by
  intro a ha b hb hab
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    rintro t ⟨x, y, hx, _, hy, _, _, rfl⟩
    exact LowerBoundCZ.fiberDensity_nonneg hx hy
  · exact fiber_nonempty hb
  · rintro t ⟨x, y, hx, hx1, hy, hy1, hξ, ht⟩
    exact ⟨x, y, hx, hx1, hy, hy1, hab.trans hξ, ht⟩

/-- Set the endpoint values to zero only in the integration weight.
This never changes `cFib`, and changes no Lebesgue integral on [-1,1]. -/
def fiberWeight (q : ℝ) : ℝ := if |q| < 1 then LowerBoundCZ.cFib |q| else 0

theorem fiberWeight_nonneg (q : ℝ) : 0 ≤ fiberWeight q := by
  unfold fiberWeight
  split_ifs <;> first | exact cFib_nonneg _ | exact le_rfl

theorem fiberWeight_le (q : ℝ) : fiberWeight q ≤ LowerBoundCZ.cFib |q| := by
  unfold fiberWeight
  split_ifs <;> first | exact le_rfl | exact cFib_nonneg _

theorem measurable_fiberWeight : Measurable fiberWeight := by
  have hm : Measurable (fun x : Iio (1 : ℝ) => LowerBoundCZ.cFib x) :=
    (show Monotone (fun x : Iio (1 : ℝ) => LowerBoundCZ.cFib x) from
      fun x y h => cFib_monotoneOn x.property y.property h).measurable
  have hmap : Measurable (fun q : {q : ℝ | |q| < 1} =>
      (⟨|q.val|, q.property⟩ : Iio (1 : ℝ))) := measurable_subtype_coe.abs.subtype_mk
  have hg : Measurable (fun q : {q : ℝ | |q| < 1} => LowerBoundCZ.cFib |q.val|) :=
    hm.comp hmap
  simpa only [fiberWeight] using hg.dite (measurable_const (a := (0 : ℝ)))
    (measurableSet_lt measurable_id.abs measurable_const)

/-- The endpoint convention in `fiberWeight` disappears from the integral. -/
theorem fiberWeight_ae_cFib : fiberWeight =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)] LowerBoundCZ.cFib := by
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  simp [fiberWeight, abs_of_pos hq.1, hq.2]

theorem fiberWeight_integral (hi : IntervalIntegrable fiberWeight volume (-1) 1) :
    IntervalIntegrable LowerBoundCZ.cFib volume 0 1 ∧
      (∫ q in (-1 : ℝ)..1, fiberWeight q) = 2 * ∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ := by
  have hp : IntervalIntegrable fiberWeight volume 0 1 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have hn : IntervalIntegrable fiberWeight volume (-1) 0 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  refine ⟨hp.congr_ae fiberWeight_ae_cFib, ?_⟩
  have he : (∫ q in (0 : ℝ)..1, fiberWeight q) = ∫ q in (-1 : ℝ)..0, fiberWeight q := by
    simpa only [fiberWeight, abs_neg, neg_zero] using
      (intervalIntegral.integral_comp_neg (f := fiberWeight) (a := (0 : ℝ)) (b := 1))
  rw [← intervalIntegral.integral_add_adjacent_intervals hn hp, ← he,
    intervalIntegral.integral_congr_ae_restrict fiberWeight_ae_cFib]
  ring

/-- Appendix B's full integral bound for every exact CZ pulse. Integrability
is a conclusion, not an assumption hiding the endpoint or limiting step. -/
theorem Pulse.fiber_integrable_and_bound (P : Pulse) :
    IntervalIntegrable LowerBoundCZ.cFib volume 0 1 ∧
      2 * (∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ) ≤ P.exposure := by
  let Q := P.toPhysicalSegment
  have hend := P.overlap_endpoints
  have h0 : (zObs (P.x 0)).re = 1 := by rw [hend.1]; rfl
  have h1 : (zObs (P.x P.S)).re = -1 := by rw [hend.2]; rfl
  have hcn : ∀ᵐ t ∂(volume.restrict (Icc 0 P.S)), 0 ≤ cost (P.x t) :=
    Eventually.of_forall (fun t => cost_nonneg _)
  have hb : ∀ᵐ t ∂(volume.restrict (Icc 0 P.S)),
      fiberWeight (zObs (P.x t)).re * |deriv (fun s => (zObs (P.x s)).re) t| ≤ cost (P.x t) := by
    filter_upwards [Q.ae_fiber_product] with t ht
    change HasDerivAt (fun s => (zObs (P.x s)).re) _ t ∧ _ at ht
    rw [ht.1.deriv]
    exact (mul_le_mul_of_nonneg_right (fiberWeight_le _) (abs_nonneg _)).trans ht.2
  obtain ⟨hi, hb⟩ := overlap_weighted_bound P.S_nonneg
    (fun F hF => Q.overlap_composition_ac hF) h0 h1
    measurable_fiberWeight fiberWeight_nonneg Q.cost_intervalIntegrable hcn hb
  obtain ⟨hfi, he⟩ := fiberWeight_integral hi
  exact ⟨hfi, he ▸ hb⟩

theorem Pulse.appendixB (P : Pulse) :
    2 * (∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ) ≤ P.exposure :=
  P.fiber_integrable_and_bound.2

theorem appendixB_Cstar :
    ((2 * (∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ) : ℝ) : EReal) ≤ Cstar := by
  apply le_iInf
  intro P
  exact_mod_cast P.appendixB

/-- The finite cutoffs in the paper converge to the same full integral.
Integrability is supplied by the physical crossing proof above. -/
theorem Pulse.fiber_truncation_limit (P : Pulse) :
    Tendsto (fun n : ℕ => 2 * ∫ ξ in (0 : ℝ)..1, min (LowerBoundCZ.cFib ξ) (n : ℝ))
      atTop (𝓝 (2 * ∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ)) := by
  have hi := P.fiber_integrable_and_bound.1
  have ht : Tendsto (fun n : ℕ => ∫ ξ in (0 : ℝ)..1, min (LowerBoundCZ.cFib ξ) (n : ℝ))
      atTop (𝓝 (∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence LowerBoundCZ.cFib
    · exact Eventually.of_forall fun n =>
        ((intervalIntegrable_iff.mp hi).aestronglyMeasurable.aemeasurable.min
          aemeasurable_const).aestronglyMeasurable
    · refine Eventually.of_forall fun n => Eventually.of_forall fun ξ _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (cFib_nonneg _) (Nat.cast_nonneg _))]
      exact min_le_left _ _
    · exact hi
    · refine Eventually.of_forall fun ξ _ => ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (LowerBoundCZ.cFib ξ)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (min_eq_left (hN.trans (Nat.cast_le.mpr hn))).symm
  exact ht.const_mul 2

end CZExposure
