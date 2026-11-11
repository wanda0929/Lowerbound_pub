module
public import RequestProject.AppendixE.ExposureClock
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Measure transport through the inverse exposure clock (Appendix E support)

For a Euclidean arc with finite `exposureTime` and domain support we prove the
exact pushforward identity

  `map clockInverseReal (ds restricted to [0,T])
    = (ds restricted to [0,L]).withDensity (weight ∘ path)`

by `Measure.ext_of_Iic` on the real line — no general Luzin-type theorem is
assumed.  This gives the correct direction of a.e. transfer from arc length to
exposure time (`clockInverseReal_ae_transfer`), which a bare Lipschitz inverse
would not supply.  We also record that the exposure clock has derivative
`inverseSpeed` a.e. by the Lebesgue differentiation theorem.

`clockInverseReal` extends the inverse constantly outside `[0,T]` via
`Set.projIcc`; all a.e. statements are only asserted on the exposure interval.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set intervalIntegral

namespace EuclideanArc

/-- The exposure-time parameter measure `dt` on `[0, exposureTime.toReal]`. -/
def exposureParameterMeasure (γ : EuclideanArc) (F : EuclideanExposureFlow) :
    Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) (γ.exposureTime F).toReal)

/-- The `ds`-parameter measure weighted by the inverse-speed density. -/
def weightedParameterMeasure (γ : EuclideanArc) (F : EuclideanExposureFlow) :
    Measure ℝ :=
  γ.parameterMeasure.withDensity (fun s => F.exposureTimeWeight (γ.path s))

/-- The inverse clock extended constantly outside `[0,T]` through `projIcc`.
The ODE is only ever asserted on the exposure interval. -/
def clockInverseReal (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : ℝ) : ℝ :=
  (γ.clockInverse F hfinite hdom
    (Set.projIcc 0 (γ.exposureTime F).toReal ENNReal.toReal_nonneg t) : ℝ)

theorem weightedParameterMeasure_univ (γ : EuclideanArc)
    (F : EuclideanExposureFlow) :
    γ.weightedParameterMeasure F Set.univ = γ.exposureTime F := by
  rw [weightedParameterMeasure,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact (γ.exposureTime_eq_lintegral F).symm

theorem clockInverseReal_mem (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    (t : ℝ) :
    γ.clockInverseReal F hfinite hdom t ∈ Set.Icc 0 γ.length :=
  (γ.clockInverse F hfinite hdom _).property

theorem clockInverseReal_of_mem (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (γ.exposureTime F).toReal) :
    γ.clockInverseReal F hfinite hdom t =
      (γ.clockInverse F hfinite hdom ⟨t, ht⟩ : ℝ) := by
  show (γ.clockInverse F hfinite hdom
    (Set.projIcc 0 (γ.exposureTime F).toReal ENNReal.toReal_nonneg t) : ℝ) =
      (γ.clockInverse F hfinite hdom ⟨t, ht⟩ : ℝ)
  rw [Set.projIcc_of_mem ENNReal.toReal_nonneg ht]

theorem lipschitz_clockInverseReal (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {K : NNReal} (hK : 0 < K)
    (hspeed : ∀ s ∈ Set.Icc 0 γ.length, ‖F.velocity (γ.path s)‖ ≤ (K : ℝ)) :
    LipschitzWith K (γ.clockInverseReal F hfinite hdom) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hproj := (LipschitzWith.projIcc
    (b := (γ.exposureTime F).toReal) ENNReal.toReal_nonneg).dist_le_mul x y
  have hinv := (γ.lipschitz_clockInverse F hfinite hdom hK hspeed).dist_le_mul
    (Set.projIcc 0 (γ.exposureTime F).toReal ENNReal.toReal_nonneg x)
    (Set.projIcc 0 (γ.exposureTime F).toReal ENNReal.toReal_nonneg y)
  calc dist (γ.clockInverseReal F hfinite hdom x)
        (γ.clockInverseReal F hfinite hdom y)
      ≤ (K : ℝ) * dist
          (Set.projIcc 0 (γ.exposureTime F).toReal ENNReal.toReal_nonneg x)
          (Set.projIcc 0 (γ.exposureTime F).toReal ENNReal.toReal_nonneg y) :=
        hinv
    _ ≤ (K : ℝ) * (1 * dist x y) :=
        mul_le_mul_of_nonneg_left hproj (NNReal.coe_nonneg K)
    _ = (K : ℝ) * dist x y := by rw [one_mul]

theorem continuous_clockInverseReal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    Continuous (γ.clockInverseReal F hfinite hdom) := by
  obtain ⟨K, hK, hbound⟩ := F.velocity_bounded
  exact (γ.lipschitz_clockInverseReal F hfinite hdom hK
    (fun s hs => hbound _ (hdom hs))).continuous

theorem exposureClock_clockInverseReal (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (γ.exposureTime F).toReal) :
    γ.exposureClock F (γ.clockInverseReal F hfinite hdom t) = t := by
  rw [γ.clockInverseReal_of_mem F hfinite hdom ht]
  exact γ.exposureClock_clockInverse F hfinite hdom ⟨t, ht⟩

theorem clockInverseReal_exposureClock (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {s : ℝ} (hs : s ∈ Set.Icc 0 γ.length) :
    γ.clockInverseReal F hfinite hdom (γ.exposureClock F s) = s := by
  have hmem : γ.exposureClock F s ∈ Set.Icc 0 (γ.exposureTime F).toReal := by
    have h := (γ.clockOrderIso F hfinite hdom ⟨s, hs⟩).property
    rw [γ.coe_clockOrderIso_apply] at h
    exact h
  have hsub : (⟨γ.exposureClock F s, hmem⟩ :
      Set.Icc (0 : ℝ) (γ.exposureTime F).toReal) =
      γ.clockOrderIso F hfinite hdom ⟨s, hs⟩ :=
    Subtype.ext (γ.coe_clockOrderIso_apply F hfinite hdom ⟨s, hs⟩).symm
  rw [γ.clockInverseReal_of_mem F hfinite hdom hmem, hsub]
  exact congrArg Subtype.val
    ((γ.clockOrderIso F hfinite hdom).symm_apply_apply ⟨s, hs⟩)

theorem clockInverseReal_le_iff (γ : EuclideanArc) (F : EuclideanExposureFlow)
    (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {t s : ℝ} (ht : t ∈ Set.Icc 0 (γ.exposureTime F).toReal)
    (hs : s ∈ Set.Icc 0 γ.length) :
    γ.clockInverseReal F hfinite hdom t ≤ s ↔ t ≤ γ.exposureClock F s := by
  have hsmono := γ.strictMonoOn_exposureClock F hfinite hdom
  constructor
  · intro h
    rw [← γ.exposureClock_clockInverseReal F hfinite hdom ht]
    exact (hsmono.le_iff_le (γ.clockInverseReal_mem F hfinite hdom t) hs).mpr h
  · intro h
    rw [← γ.exposureClock_clockInverseReal F hfinite hdom ht] at h
    exact (hsmono.le_iff_le (γ.clockInverseReal_mem F hfinite hdom t) hs).mp h

/-- Partial weighted integral up to `s` stays below the finite total cost. -/
theorem lintegral_exposureTimeWeight_Icc_lt_top (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    {s : ℝ} (hs : s ∈ Set.Icc 0 γ.length) :
    (∫⁻ q in Set.Icc (0 : ℝ) s, F.exposureTimeWeight (γ.path q)) < ⊤ := by
  apply lt_of_le_of_lt _ hfinite
  rw [γ.exposureTime_eq_lintegral F]
  exact lintegral_mono_set (Set.Icc_subset_Icc le_rfl hs.2)

theorem exposureClock_eq_toReal_lintegral (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    {s : ℝ} (hs : s ∈ Set.Icc 0 γ.length) :
    γ.exposureClock F s =
      (∫⁻ q in Set.Icc (0 : ℝ) s, F.exposureTimeWeight (γ.path q)).toReal := by
  have hlt := γ.lintegral_exposureTimeWeight_Icc_lt_top F hfinite hs
  have hle' : ∀ᵐ q ∂volume.restrict (Set.Icc (0 : ℝ) s),
      F.exposureTimeWeight (γ.path q) < ⊤ :=
    ae_lt_top (γ.measurable_weight_path F) hlt.ne
  show (∫ q in (0 : ℝ)..s, γ.inverseSpeed F q) = _
  rw [intervalIntegral.integral_of_le hs.1]
  show (∫ q, γ.inverseSpeed F q ∂volume.restrict (Set.Ioc 0 s)) = _
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp only [γ.inverseSpeed_eq_toReal F]
  rw [integral_toReal (γ.measurable_weight_path F).aemeasurable.restrict hle']

theorem weightedParameterMeasure_Iic (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    {s : ℝ} (hs : s ∈ Set.Icc 0 γ.length) :
    γ.weightedParameterMeasure F (Set.Iic s) =
      ENNReal.ofReal (γ.exposureClock F s) := by
  have hlt := γ.lintegral_exposureTimeWeight_Icc_lt_top F hfinite hs
  have hIcc : Set.Icc (0 : ℝ) γ.length ∩ Set.Iic s = Set.Icc 0 s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    exact ⟨fun ⟨⟨h0, _⟩, hs'⟩ => ⟨h0, hs'⟩,
      fun ⟨h0, hs'⟩ => ⟨⟨h0, le_trans hs' hs.2⟩, hs'⟩⟩
  rw [weightedParameterMeasure,
    MeasureTheory.withDensity_apply _ measurableSet_Iic]
  show (∫⁻ q, F.exposureTimeWeight (γ.path q)
    ∂(volume.restrict (Set.Icc 0 γ.length)).restrict (Set.Iic s)) = _
  rw [Measure.restrict_restrict measurableSet_Iic,
    Set.inter_comm (Set.Iic s), hIcc]
  rw [← ENNReal.ofReal_toReal hlt.ne,
    γ.exposureClock_eq_toReal_lintegral F hfinite hs]

theorem clockInverseReal_map_exposureMeasure (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain) :
    Measure.map (γ.clockInverseReal F hfinite hdom)
      (γ.exposureParameterMeasure F) = γ.weightedParameterMeasure F := by
  haveI : IsFiniteMeasure (γ.exposureParameterMeasure F) :=
    ⟨by rw [exposureParameterMeasure,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure
      (Measure.map (γ.clockInverseReal F hfinite hdom)
        (γ.exposureParameterMeasure F)) :=
    ⟨by rw [Measure.map_apply
        (γ.continuous_clockInverseReal F hfinite hdom).measurable
        MeasurableSet.univ, Set.preimage_univ]
        exact IsFiniteMeasure.measure_univ_lt_top⟩
  have hmeas := (γ.continuous_clockInverseReal F hfinite hdom).measurable
  apply Measure.ext_of_Iic
  intro s
  rcases lt_or_ge s 0 with hs0 | hs0
  · have hpre : (γ.clockInverseReal F hfinite hdom ⁻¹' Set.Iic s) ∩
        Set.Icc (0 : ℝ) (γ.exposureTime F).toReal = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro t ⟨h1, -⟩
      exact absurd (le_trans (γ.clockInverseReal_mem F hfinite hdom t).1 h1)
        (not_le.mpr hs0)
    have hIic : Set.Iic s ∩ Set.Icc (0 : ℝ) γ.length = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro t ⟨h1, ⟨h0, -⟩⟩
      exact absurd (le_trans h0 h1) (not_le.mpr hs0)
    rw [Measure.map_apply hmeas measurableSet_Iic, exposureParameterMeasure,
      Measure.restrict_apply (measurableSet_Iic.preimage hmeas), hpre,
      measure_empty, weightedParameterMeasure,
      MeasureTheory.withDensity_apply _ measurableSet_Iic,
      parameterMeasure, Measure.restrict_restrict measurableSet_Iic, hIic]
    simp
  · rcases lt_or_ge s γ.length with hsL | hsL
    · have hs : s ∈ Set.Icc 0 γ.length := ⟨hs0, hsL.le⟩
      have hclock : γ.exposureClock F s ≤ (γ.exposureTime F).toReal := by
        have h := (γ.strictMonoOn_exposureClock F hfinite hdom).monotoneOn hs
          (Set.right_mem_Icc.mpr γ.length_pos.le) hs.2
        rwa [γ.exposureClock_terminal F hfinite] at h
      have hid : (γ.clockInverseReal F hfinite hdom ⁻¹' Set.Iic s) ∩
          Set.Icc (0 : ℝ) (γ.exposureTime F).toReal =
          Set.Icc (0 : ℝ) (γ.exposureClock F s) := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, ht⟩
          exact ⟨ht.1, (γ.clockInverseReal_le_iff F hfinite hdom ht hs).mp h1⟩
        · rintro ⟨h0, h1⟩
          have ht : t ∈ Set.Icc 0 (γ.exposureTime F).toReal :=
            ⟨h0, le_trans h1 hclock⟩
          exact ⟨(γ.clockInverseReal_le_iff F hfinite hdom ht hs).mpr h1, ht⟩
      rw [Measure.map_apply hmeas measurableSet_Iic, exposureParameterMeasure,
        Measure.restrict_apply (measurableSet_Iic.preimage hmeas), hid,
        Real.volume_Icc, sub_zero]
      exact (γ.weightedParameterMeasure_Iic F hfinite hs).symm
    · have hpre : (γ.clockInverseReal F hfinite hdom ⁻¹' Set.Iic s) ∩
          Set.Icc (0 : ℝ) (γ.exposureTime F).toReal =
          Set.Icc (0 : ℝ) (γ.exposureTime F).toReal := by
        apply Set.inter_eq_right.mpr
        intro t _
        have hle := (γ.clockInverseReal_mem F hfinite hdom t).2
        exact le_trans hle hsL
      have hIic : Set.Iic s ∩ Set.Icc (0 : ℝ) γ.length = Set.Icc 0 γ.length :=
        Set.inter_eq_right.mpr (fun _ hx => le_trans hx.2 hsL)
      rw [Measure.map_apply hmeas measurableSet_Iic, exposureParameterMeasure,
        Measure.restrict_apply (measurableSet_Iic.preimage hmeas), hpre,
        Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hfinite.ne,
        weightedParameterMeasure,
        MeasureTheory.withDensity_apply _ measurableSet_Iic,
        parameterMeasure, Measure.restrict_restrict measurableSet_Iic, hIic]
      show γ.exposureTime F =
        ∫⁻ q, F.exposureTimeWeight (γ.path q) ∂γ.parameterMeasure
      exact γ.exposureTime_eq_lintegral F

theorem clockInverseReal_ae_transfer (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤)
    (hdom : Set.MapsTo γ.path (Set.Icc 0 γ.length) euclideanExposureDomain)
    {P : ℝ → Prop} (hP : ∀ᵐ s ∂γ.parameterMeasure, P s) :
    ∀ᵐ t ∂γ.exposureParameterMeasure F,
      P (γ.clockInverseReal F hfinite hdom t) := by
  have hP' : ∀ᵐ s ∂γ.weightedParameterMeasure F, P s :=
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le hP
  rw [← γ.clockInverseReal_map_exposureMeasure F hfinite hdom] at hP'
  exact MeasureTheory.ae_of_ae_map
    (γ.continuous_clockInverseReal F hfinite hdom).measurable.aemeasurable hP'

theorem ae_hasDerivAt_exposureClock (γ : EuclideanArc)
    (F : EuclideanExposureFlow) (hfinite : γ.exposureTime F < ⊤) :
    ∀ᵐ s ∂γ.parameterMeasure,
      HasDerivAt (γ.exposureClock F) (γ.inverseSpeed F s) s := by
  have h := (γ.intervalIntegrable_inverseSpeed F hfinite).ae_hasDerivAt_integral
  rw [Set.uIcc_of_le γ.length_pos.le] at h
  have h' : ∀ᵐ x ∂volume, x ∈ Set.Icc 0 γ.length →
      HasDerivAt (γ.exposureClock F) (γ.inverseSpeed F x) x := by
    filter_upwards [h] with x hx hmem
    exact hx hmem 0 (Set.left_mem_Icc.mpr γ.length_pos.le)
  exact (ae_restrict_iff' measurableSet_Icc).mpr h'

end EuclideanArc

end CZExposure
