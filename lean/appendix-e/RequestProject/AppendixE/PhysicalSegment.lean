module
public import RequestProject.AppendixE.SectorPhase

/-!
# Physical segments: integral-form trajectories

A `PhysicalSegment` packages a finite nonnegative duration, a globally
measurable control bounded by one on its interval, state-domain
membership, vector-velocity integrability, and the integral form of the
dynamics at every time.  No Lipschitz/A.C./a.e.-ODE field is assumed:
the integral equation itself yields `1`-Lipschitz regularity on the
interval, which rules out a bare a.e.-ODE (Cantor-function) loophole and
supports duration zero.

Reversal `x(D-s)`, `-u(D-s)` is proved by interval integrals — no
exceptional-set transport is used.  `rephase` applies the verified
sector-phase CLM with the *same* control, and `toPulse` bridges to
`Pulse`'s coordinate integral form with the unit-modulus, initial-state,
and exact-CZ hypotheses kept explicit.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set

/-! ## Interval helpers -/

theorem uIcc_subset_uIcc_of_mem {D a b : ℝ} (ha : a ∈ Set.Icc 0 D)
    (hb : b ∈ Set.Icc 0 D) : Set.uIcc a b ⊆ Set.uIcc 0 D := by
  intro t ht
  rcases Set.mem_uIcc.mp ht with h | h
  · exact Set.mem_uIcc.mpr (Or.inl
      ⟨le_trans ha.1 h.1, le_trans h.2 hb.2⟩)
  · exact Set.mem_uIcc.mpr (Or.inl
      ⟨le_trans hb.1 h.1, le_trans h.2 ha.2⟩)

theorem mem_Icc_of_mem_uIoc {D s t : ℝ} (hs : s ∈ Set.Icc 0 D)
    (ht : t ∈ Set.uIoc (0:ℝ) s) : t ∈ Set.Icc 0 D := by
  rw [Set.uIoc_of_le hs.1] at ht
  exact ⟨le_of_lt ht.1, le_trans ht.2 hs.2⟩

theorem mem_Icc_sub {D s : ℝ} (hs : s ∈ Set.Icc 0 D) :
    D - s ∈ Set.Icc 0 D :=
  ⟨sub_nonneg.mpr hs.2, sub_le_self _ hs.1⟩

private theorem norm_vf_le_one {x : State} (hx : x ∈ Xset) {u : ℂ}
    (hu : ‖u‖ ≤ 1) : ‖vf x u‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro i
  exact abs_vf_le_one hx hu i

/-! ## The structure -/

/-- A finite-duration physical trajectory with disk control, in integral
form. -/
structure PhysicalSegment where
  /-- the duration -/
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  /-- the physical trajectory -/
  path : ℝ → State
  /-- the control -/
  control : ℝ → ℂ
  control_measurable : Measurable control
  control_bound : ∀ s ∈ Set.Icc 0 duration, ‖control s‖ ≤ 1
  path_mem : ∀ s ∈ Set.Icc 0 duration, path s ∈ Xset
  velocity_integrable :
    IntervalIntegrable (fun s => vf (path s) (control s)) volume 0 duration
  integralEquation : ∀ s ∈ Set.Icc 0 duration,
    path s = path 0 + ∫ r in (0 : ℝ)..s, vf (path r) (control r)

namespace PhysicalSegment

/-- The physical vector field is odd in the control. -/
theorem vf_neg_control (x : State) (u : ℂ) :
    vf x (-u) = -vf x u := by
  funext i
  fin_cases i <;> simp [vf, fC, map_neg]

variable (P : PhysicalSegment)

/-- Total exposure `∫ cost ∘ path` of the segment. -/
def exposure : ℝ := ∫ s in (0 : ℝ)..P.duration, cost (P.path s)

theorem velocity_integrable_subinterval {a b : ℝ}
    (ha : a ∈ Set.Icc 0 P.duration) (hb : b ∈ Set.Icc 0 P.duration) :
    IntervalIntegrable (fun s => vf (P.path s) (P.control s)) volume a b :=
  P.velocity_integrable.mono_set (uIcc_subset_uIcc_of_mem ha hb)

theorem integral_velocity {a b : ℝ}
    (ha : a ∈ Set.Icc 0 P.duration) (hb : b ∈ Set.Icc 0 P.duration) :
    (∫ s in a..b, vf (P.path s) (P.control s)) = P.path b - P.path a := by
  have h0a := P.velocity_integrable_subinterval
    (Set.left_mem_Icc.mpr P.duration_nonneg) ha
  have h0b := P.velocity_integrable_subinterval
    (Set.left_mem_Icc.mpr P.duration_nonneg) hb
  have hsub := intervalIntegral.integral_interval_sub_left h0b h0a
  rw [P.integralEquation b hb, P.integralEquation a ha, ← hsub]
  abel

theorem path_lipschitzOn :
    LipschitzOnWith 1 P.path (Set.Icc 0 P.duration) := by
  intro s hs t ht
  have hvb : ∀ r ∈ Set.uIoc t s, ‖vf (P.path r) (P.control r)‖ ≤ 1 := by
    intro r hr
    have hrI : r ∈ Set.Icc 0 P.duration :=
      Set.uIcc_of_le P.duration_nonneg ▸
        uIcc_subset_uIcc_of_mem ht hs (Set.uIoc_subset_uIcc hr)
    exact norm_vf_le_one (P.path_mem r hrI) (P.control_bound r hrI)
  have hineq := intervalIntegral.norm_integral_le_of_norm_le_const hvb
  rw [P.integral_velocity ht hs] at hineq
  rw [edist_dist, edist_dist, dist_eq_norm, Real.dist_eq, ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal (by simpa using hineq)

theorem continuousOn_path : ContinuousOn P.path (Set.Icc 0 P.duration) :=
  P.path_lipschitzOn.continuousOn

theorem cost_intervalIntegrable :
    IntervalIntegrable (fun s => cost (P.path s)) volume 0 P.duration := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le P.duration_nonneg]
  exact ((contDiff_cost.continuous.continuousOn).comp P.continuousOn_path
    (Set.mapsTo_univ _ _)).integrableOn_Icc

theorem exposure_nonneg : 0 ≤ P.exposure := by
  refine intervalIntegral.integral_nonneg P.duration_nonneg ?_
  intro t ht
  exact cost_nonneg _

/-! ## The zero-duration segment -/

/-- The identity segment of zero duration; no dynamics outside its
degenerate interval is asserted. -/
def zero (x : State) (hx : x ∈ Xset) : PhysicalSegment where
  duration := 0
  duration_nonneg := le_rfl
  path := fun _ => x
  control := fun _ => 0
  control_measurable := measurable_const
  control_bound := fun _ _ => by simp
  path_mem := fun _ _ => hx
  velocity_integrable := by
    rw [intervalIntegrable_iff]
    simp
  integralEquation := fun s hs => by
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    simp

@[simp] theorem zero_exposure (x : State) (hx : x ∈ Xset) :
    (zero x hx).exposure = 0 := by
  simp [PhysicalSegment.exposure, zero]

/-! ## Retained-segment realization -/

/-- The verified retained physical realization, repackaged as a
`PhysicalSegment`; no new controls are fabricated. -/
def ofPositiveExposureSegment (S : PositiveExposureSegment) : PhysicalSegment where
  duration := S.duration
  duration_nonneg := S.duration_bounds.1.le
  path := S.physicalPath
  control := S.physicalControl
  control_measurable := S.measurable_physicalControl
  control_bound := fun s _ => S.physicalControl_bound s
  path_mem := fun s _ => S.physicalPath_mem s
  velocity_integrable := by
    rw [intervalIntegrable_iff]
    refine MeasureTheory.integrable_pi_iff.mpr fun i => ?_
    exact intervalIntegrable_iff.mp (S.intervalIntegrable_physicalVelocity i)
  integralEquation := by
    intro s hs
    funext i
    have hint : IntervalIntegrable (fun r => vf (S.physicalPath r)
        (S.physicalControl r)) volume 0 s := by
      rw [intervalIntegrable_iff]
      refine MeasureTheory.integrable_pi_iff.mpr fun j =>
        intervalIntegrable_iff.mp
          ((S.intervalIntegrable_physicalVelocity j).mono_set
            (uIcc_subset_uIcc_of_mem
              (Set.left_mem_Icc.mpr S.duration_bounds.1.le) hs))
    have key := (ContinuousLinearMap.proj i :
        State →L[ℝ] ℝ).intervalIntegral_comp_comm hint
    show S.physicalPath s i =
      S.physicalPath 0 i +
        (∫ r in (0:ℝ)..s, vf (S.physicalPath r) (S.physicalControl r)) i
    rw [S.physicalPath_integralEquation hs i]
    exact add_left_cancel_iff.mpr key

theorem ofPositiveExposureSegment_exposure (S : PositiveExposureSegment) :
    (ofPositiveExposureSegment S).exposure = S.b - S.a :=
  S.physicalExposure_eq

theorem ofPositiveExposureSegment_endpoints (S : PositiveExposureSegment) :
    (ofPositiveExposureSegment S).path 0 = S.liftedState S.a ∧
    (ofPositiveExposureSegment S).path S.duration = S.liftedState S.b :=
  ⟨S.physicalPath_zero, S.physicalPath_terminal⟩

/-! ## Time reversal -/

/-- The reversed segment `x(D-s)`, `-u(D-s)`. -/
def reverse : PhysicalSegment where
  duration := P.duration
  duration_nonneg := P.duration_nonneg
  path := fun s => P.path (P.duration - s)
  control := fun s => -P.control (P.duration - s)
  control_measurable := (P.control_measurable.comp
    (measurable_const.sub measurable_id)).neg
  control_bound := fun s hs => by
    rw [norm_neg]
    exact P.control_bound _ (mem_Icc_sub hs)
  path_mem := fun s hs => P.path_mem _ (mem_Icc_sub hs)
  velocity_integrable := by
    have h := (P.velocity_integrable.comp_sub_left P.duration).neg
    simp only [sub_self, sub_zero] at h
    simpa only [vf_neg_control] using h.symm
  integralEquation := by
    intro s hs
    have hDs : P.duration - s ∈ Set.Icc 0 P.duration := mem_Icc_sub hs
    have h0D : P.duration ∈ Set.Icc 0 P.duration :=
      Set.right_mem_Icc.mpr P.duration_nonneg
    have hsub := intervalIntegral.integral_interval_sub_left
      P.velocity_integrable
      (P.velocity_integrable_subinterval
        (Set.left_mem_Icc.mpr P.duration_nonneg) hDs)
    have e := intervalIntegral.integral_comp_sub_left
      (f := fun r => vf (P.path r) (P.control r)) (a := 0) (b := s)
      (d := P.duration)
    simp only [sub_zero] at e
    show P.path (P.duration - s) = P.path (P.duration - 0) +
      ∫ r in (0:ℝ)..s, vf (P.path (P.duration - r))
        (-P.control (P.duration - r))
    rw [sub_zero]
    rw [show (fun r => vf (P.path (P.duration - r))
          (-P.control (P.duration - r))) =
        fun r => -vf (P.path (P.duration - r)) (P.control (P.duration - r)) from
      funext fun r => vf_neg_control _ _]
    rw [intervalIntegral.integral_neg,
      show (∫ r in (0:ℝ)..s, vf (P.path (P.duration - r))
          (P.control (P.duration - r))) =
        ∫ r in (P.duration - s)..P.duration,
          vf (P.path r) (P.control r) from e]
    rw [P.integralEquation _ hDs, P.integralEquation _ h0D, ← hsub]
    abel

@[simp] theorem reverse_duration : P.reverse.duration = P.duration := rfl

@[simp] theorem reverse_path (s : ℝ) :
    P.reverse.path s = P.path (P.duration - s) := rfl

@[simp] theorem reverse_control (s : ℝ) :
    P.reverse.control s = -P.control (P.duration - s) := rfl

theorem reverse_endpoints :
    P.reverse.path 0 = P.path P.duration ∧
      P.reverse.path P.duration = P.path 0 := by
  simp [reverse_path]

@[simp] theorem reverse_exposure : P.reverse.exposure = P.exposure := by
  show (∫ s in (0:ℝ)..P.duration, cost (P.reverse.path s)) =
      ∫ s in (0:ℝ)..P.duration, cost (P.path s)
  have he : (fun s => cost (P.reverse.path s)) =
      fun s => cost (P.path (P.duration - s)) := rfl
  rw [he]
  have e := intervalIntegral.integral_comp_sub_left
    (f := fun s => cost (P.path s)) (a := 0) (b := P.duration)
    (d := P.duration)
  simp only [sub_self, sub_zero] at e
  exact e

/-! ## Sector-phase reparametrization -/

/-- The sector-phased segment, with the same control. -/
def rephase (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : PhysicalSegment where
  duration := P.duration
  duration_nonneg := P.duration_nonneg
  path := fun s => sectorPhase a b (P.path s)
  control := P.control
  control_measurable := P.control_measurable
  control_bound := P.control_bound
  path_mem := fun s hs => sectorPhase_mem_Xset ha hb (P.path_mem s hs)
  velocity_integrable := by
    rw [intervalIntegrable_iff]
    rw [show (fun s => vf (sectorPhase a b (P.path s)) (P.control s)) =
        fun s => (sectorPhaseCLM a b) (vf (P.path s) (P.control s)) from
      funext fun s => (sectorPhase_vf a b (P.path s) (P.control s)).symm.trans
        (sectorPhaseCLM_apply a b _).symm]
    exact (sectorPhaseCLM a b).integrable_comp
      (intervalIntegrable_iff.mp P.velocity_integrable)
  integralEquation := by
    intro s hs
    have hint : IntervalIntegrable (fun r => vf (P.path r) (P.control r))
        volume 0 s :=
      P.velocity_integrable_subinterval
        (Set.left_mem_Icc.mpr P.duration_nonneg) hs
    show sectorPhase a b (P.path s) =
      sectorPhase a b (P.path 0) +
        ∫ r in (0:ℝ)..s, vf (sectorPhase a b (P.path r)) (P.control r)
    exact sectorPhase_integralEquation a b hint (P.integralEquation s hs)

@[simp] theorem rephase_duration (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (P.rephase a b ha hb).duration = P.duration := rfl

@[simp] theorem rephase_path (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (s : ℝ) :
    (P.rephase a b ha hb).path s = sectorPhase a b (P.path s) := rfl

@[simp] theorem rephase_control (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (P.rephase a b ha hb).control = P.control := rfl

@[simp] theorem rephase_exposure (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (P.rephase a b ha hb).exposure = P.exposure := by
  show (∫ s in (0:ℝ)..P.duration,
      cost ((P.rephase a b ha hb).path s)) =
      ∫ s in (0:ℝ)..P.duration, cost (P.path s)
  apply intervalIntegral.integral_congr
  intro t _
  exact cost_sectorPhase ha hb (P.path t)

/-! ## Bridge to `Pulse` -/

/-- A segment becomes a `Pulse` once unit-modulus control, the initial
state, and exact-CZ closure are supplied explicitly.  This conversion
does not prove those hypotheses. -/
def toPulse (hunit : ∀ s ∈ Set.Icc 0 P.duration, ‖P.control s‖ = 1)
    (hstart : P.path 0 = x0) (hend : P.path P.duration ∈ XCZ) : Pulse where
  S := P.duration
  S_nonneg := P.duration_nonneg
  u := P.control
  u_measurable := P.control_measurable
  x := P.path
  u_unit := hunit
  x_mem := P.path_mem
  integrable := by
    intro i
    rw [intervalIntegrable_iff]
    exact (MeasureTheory.integrable_pi_iff.mp
      (intervalIntegrable_iff.mp P.velocity_integrable)) i
  ode := by
    intro s hs i
    have hint : IntervalIntegrable (fun t => vf (P.path t) (P.control t))
        volume 0 s :=
      P.velocity_integrable_subinterval
        (Set.left_mem_Icc.mpr P.duration_nonneg) hs
    have key := (ContinuousLinearMap.proj i :
        State →L[ℝ] ℝ).intervalIntegral_comp_comm hint
    have hpi := congrFun (P.integralEquation s hs) i
    rw [Pi.add_apply] at hpi
    rw [hpi, congrFun hstart i]
    congr 1
    exact key.symm
  terminal := hend

@[simp] theorem toPulse_exposure
    (hunit : ∀ s ∈ Set.Icc 0 P.duration, ‖P.control s‖ = 1)
    (hstart : P.path 0 = x0) (hend : P.path P.duration ∈ XCZ) :
    (P.toPulse hunit hstart hend).exposure = P.exposure := rfl

end PhysicalSegment

end CZExposure
