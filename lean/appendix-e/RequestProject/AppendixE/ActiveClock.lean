module
public import RequestProject.AppendixE.PhysicalConcatenation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Active-time clock

For every supplied `PhysicalSegment`, including zero duration and
controls that vanish on intervals or more general measurable sets,
the active clock `A(t) = ∫₀ᵗ ‖u(q)‖ dq` is nondecreasing and
`1`-Lipschitz on `[0, D]`, with `S = A(D) ∈ [0, D]`.  The state is
constant on clock fibers: `‖x(t) − x(s)‖ ≤ |A(t) − A(s)|`.

A chosen section of the clock is automatically strictly monotone
between distinct clock levels, hence its clamped extension is
monotone and measurable even though it may jump.  Composing the
state with the selector gives a globally `1`-Lipschitz active-time
path `Y` in `X` factoring `x`, with the same endpoints and image.

Normalizing the selected control (value `1` at zero) supplies a
globally measurable unit-modulus candidate.  `ActiveDynamics.lean`
proves that it drives `activePath` in integral form, and
`UnitControlRealization.lean` packages the resulting unit-control
`PhysicalSegment`.
-/

@[expose] public section

noncomputable section

namespace CZExposure.PhysicalSegment

open MeasureTheory Set
open scoped NNReal ENNReal

/-! ## Unit direction of a complex control -/

/-- Unit direction of the complex control, with value `1` at zero. -/
def controlDirection (u : ℂ) : ℂ :=
  if u = 0 then 1 else (‖u‖⁻¹ : ℝ) • u

theorem measurable_controlDirection : Measurable controlDirection := by
  unfold controlDirection
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_norm.inv.smul measurable_id)

theorem norm_controlDirection (u : ℂ) : ‖controlDirection u‖ = 1 := by
  unfold controlDirection
  split_ifs with hu
  · exact norm_one
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

theorem norm_smul_controlDirection (u : ℂ) :
    ‖u‖ • controlDirection u = u := by
  unfold controlDirection
  split_ifs with hu
  · simp [hu]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]

theorem vf_real_smul_control (x : State) (r : ℝ) (u : ℂ) :
    vf x (r • u) = r • vf x u := by
  have hC : ∀ i : Fin 4, fC x ((r : ℂ) * u) i = (r : ℂ) * fC x u i := by
    intro i
    fin_cases i <;>
      simp [fC, map_mul, Complex.conj_ofReal] <;> ring
  funext i
  fin_cases i <;>
    simp [vf, Pi.smul_apply, smul_eq_mul, hC,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]

theorem vf_controlDirection (x : State) (u : ℂ) :
    vf x u = ‖u‖ • vf x (controlDirection u) := by
  conv_lhs => rw [← norm_smul_controlDirection u]
  exact vf_real_smul_control x ‖u‖ (controlDirection u)

theorem norm_vf_le_norm_control {x : State} (hx : x ∈ Xset) (u : ℂ) :
    ‖vf x u‖ ≤ ‖u‖ := by
  rw [vf_controlDirection x u, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u)]
  have h1 : ‖vf x (controlDirection u)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    exact abs_vf_le_one hx (norm_controlDirection u).le i
  nlinarith [norm_nonneg u, h1]

variable (P : PhysicalSegment)

/-! ## The active clock -/

theorem intervalIntegrable_controlNorm :
    IntervalIntegrable (fun t => ‖P.control t‖) volume 0 P.duration := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.duration_nonneg]
  apply Integrable.mono' (g := fun _ => (1:ℝ)) (f := fun t => ‖P.control t‖)
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · exact P.control_measurable.norm.aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      P.control_bound t (Set.Ioc_subset_Icc_self ht)

theorem intervalIntegrable_controlNorm_subinterval {a b : ℝ}
    (ha : a ∈ Set.Icc 0 P.duration) (hb : b ∈ Set.Icc 0 P.duration) :
    IntervalIntegrable (fun t => ‖P.control t‖) volume a b :=
  P.intervalIntegrable_controlNorm.mono_set
    (uIcc_subset_uIcc_of_mem ha hb)

/-- The active clock `A(t) = ∫₀ᵗ ‖u‖`. -/
def activeClock (t : ℝ) : ℝ := ∫ q in (0:ℝ)..t, ‖P.control q‖

/-- The active duration `S = A(D)`. -/
def activeDuration : ℝ := P.activeClock P.duration

@[simp] theorem activeClock_zero : P.activeClock 0 = 0 := by
  simp [activeClock]

theorem activeClock_increment {s t : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) (ht : t ∈ Set.Icc 0 P.duration) :
    P.activeClock t - P.activeClock s =
      ∫ q in s..t, ‖P.control q‖ := by
  unfold activeClock
  exact intervalIntegral.integral_interval_sub_left
    (P.intervalIntegrable_controlNorm_subinterval
      (Set.left_mem_Icc.mpr P.duration_nonneg) ht)
    (P.intervalIntegrable_controlNorm_subinterval
      (Set.left_mem_Icc.mpr P.duration_nonneg) hs)

theorem activeClock_increment_bounds {s t : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) (ht : t ∈ Set.Icc 0 P.duration)
    (hst : s ≤ t) :
    0 ≤ P.activeClock t - P.activeClock s ∧
      P.activeClock t - P.activeClock s ≤ t - s := by
  rw [P.activeClock_increment hs ht]
  constructor
  · exact intervalIntegral.integral_nonneg hst
      (fun q _ => norm_nonneg _)
  · calc (∫ q in s..t, ‖P.control q‖)
        ≤ ∫ q in s..t, (1:ℝ) := by
          apply intervalIntegral.integral_mono_on hst
            (P.intervalIntegrable_controlNorm_subinterval hs ht)
            (continuous_const.intervalIntegrable s t :
              IntervalIntegrable (fun _ => (1:ℝ)) volume s t)
          intro q hq
          exact P.control_bound q
            ⟨le_trans hs.1 hq.1, le_trans hq.2 ht.2⟩
      _ = t - s := by simp

theorem monotoneOn_activeClock :
    MonotoneOn P.activeClock (Set.Icc 0 P.duration) := by
  intro s hs t ht hst
  have hb := P.activeClock_increment_bounds hs ht hst
  linarith

theorem lipschitzOn_activeClock :
    LipschitzOnWith 1 P.activeClock (Set.Icc 0 P.duration) := by
  intro s hs t ht
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    ENNReal.coe_one, one_mul]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total s t with hst | hst
  · have hb := P.activeClock_increment_bounds hs ht hst
    rw [abs_sub_comm (P.activeClock s) (P.activeClock t),
      abs_of_nonneg hb.1, abs_sub_comm s t,
      abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hb.2
  · have hb := P.activeClock_increment_bounds ht hs hst
    rw [abs_of_nonneg hb.1, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hb.2

theorem activeDuration_bounds :
    0 ≤ P.activeDuration ∧ P.activeDuration ≤ P.duration := by
  have hb := P.activeClock_increment_bounds
    (Set.left_mem_Icc.mpr P.duration_nonneg)
    (Set.right_mem_Icc.mpr P.duration_nonneg) P.duration_nonneg
  rw [activeClock_zero, sub_zero, sub_zero] at hb
  exact ⟨hb.1, hb.2⟩

theorem activeClock_image_interval :
    P.activeClock '' Set.Icc 0 P.duration =
      Set.Icc 0 P.activeDuration := by
  apply Set.Subset.antisymm
  · rintro s ⟨t, ht, rfl⟩
    have hmono := P.monotoneOn_activeClock
    have h1 := hmono (Set.left_mem_Icc.mpr P.duration_nonneg) ht ht.1
    have h2 := hmono ht (Set.right_mem_Icc.mpr P.duration_nonneg) ht.2
    rw [activeClock_zero] at h1
    exact ⟨h1, h2⟩
  · intro s hs
    have hsub : Set.Icc (P.activeClock 0) (P.activeClock P.duration) ⊆
        P.activeClock '' Set.Icc 0 P.duration :=
      intermediate_value_Icc P.duration_nonneg
        P.lipschitzOn_activeClock.continuousOn
    rw [activeClock_zero] at hsub
    exact hsub hs

theorem activeClock_mem {t : ℝ} (ht : t ∈ Set.Icc 0 P.duration) :
    P.activeClock t ∈ Set.Icc 0 P.activeDuration := by
  rw [← P.activeClock_image_interval]
  exact ⟨t, ht, rfl⟩

/-- Stronger than the elapsed-time Lipschitz estimate: the state
increment is bounded by the *active* clock increment. -/
theorem path_increment_le_activeClock {s t : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) (ht : t ∈ Set.Icc 0 P.duration)
    (hst : s ≤ t) :
    ‖P.path t - P.path s‖ ≤ P.activeClock t - P.activeClock s := by
  rw [P.activeClock_increment hs ht]
  calc ‖P.path t - P.path s‖
      = ‖∫ r in s..t, vf (P.path r) (P.control r)‖ := by
        rw [P.integral_velocity hs ht]
    _ ≤ ∫ r in s..t, ‖vf (P.path r) (P.control r)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hst
    _ ≤ ∫ r in s..t, ‖P.control r‖ := by
        apply intervalIntegral.integral_mono_on hst
          ((P.velocity_integrable_subinterval hs ht).norm)
          (P.intervalIntegrable_controlNorm_subinterval hs ht)
        intro r hr
        exact norm_vf_le_norm_control
          (P.path_mem r ⟨le_trans hs.1 hr.1, le_trans hr.2 ht.2⟩) _

theorem path_dist_le_activeClock {s t : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) (ht : t ∈ Set.Icc 0 P.duration) :
    ‖P.path t - P.path s‖ ≤ |P.activeClock t - P.activeClock s| := by
  rcases le_total s t with hst | hst
  · have hb := (P.activeClock_increment_bounds hs ht hst).1
    rw [abs_of_nonneg hb]
    exact P.path_increment_le_activeClock hs ht hst
  · have hb := (P.activeClock_increment_bounds ht hs hst).1
    rw [abs_sub_comm, abs_of_nonneg hb, norm_sub_rev]
    exact P.path_increment_le_activeClock ht hs hst

theorem path_eq_of_activeClock_eq {s t : ℝ}
    (hs : s ∈ Set.Icc 0 P.duration) (ht : t ∈ Set.Icc 0 P.duration)
    (hclock : P.activeClock s = P.activeClock t) : P.path s = P.path t := by
  have h := P.path_dist_le_activeClock hs ht
  rw [hclock, sub_self, abs_zero] at h
  have h0 := le_antisymm h (norm_nonneg _)
  rw [norm_eq_zero] at h0
  exact (sub_eq_zero.mp h0).symm

theorem path_eq_initial_of_activeDuration_zero
    (hzero : P.activeDuration = 0) {t : ℝ}
    (ht : t ∈ Set.Icc 0 P.duration) : P.path t = P.path 0 := by
  have hle := P.monotoneOn_activeClock ht
    (Set.right_mem_Icc.mpr P.duration_nonneg) ht.2
  have hge := (P.activeClock_increment_bounds
    (Set.left_mem_Icc.mpr P.duration_nonneg) ht ht.1).1
  rw [activeClock_zero, sub_zero] at hge
  have hAt0 : P.activeClock t = 0 :=
    le_antisymm (le_trans hle (le_of_eq hzero)) hge
  have hclock : P.activeClock 0 = P.activeClock t := by
    rw [activeClock_zero, hAt0]
  exact P.path_eq_of_activeClock_eq ht
    (Set.left_mem_Icc.mpr P.duration_nonneg) hclock.symm

/-! ## The clock section and selector -/

theorem exists_activeClock_preimage (s : Set.Icc 0 P.activeDuration) :
    ∃ t : Set.Icc 0 P.duration,
      P.activeClock (t : ℝ) = (s : ℝ) := by
  have hmem : (s : ℝ) ∈ P.activeClock '' Set.Icc 0 P.duration := by
    rw [P.activeClock_image_interval]
    exact s.2
  obtain ⟨t, ht, hte⟩ := hmem
  exact ⟨⟨t, ht⟩, hte⟩

/-- A chosen section of the clock; not a continuous inverse. -/
def activeClockSection (s : Set.Icc 0 P.activeDuration) :
    Set.Icc 0 P.duration :=
  Classical.choose (P.exists_activeClock_preimage s)

theorem activeClockSection_spec (s : Set.Icc 0 P.activeDuration) :
    P.activeClock (P.activeClockSection s : ℝ) = (s : ℝ) :=
  Classical.choose_spec (P.exists_activeClock_preimage s)

theorem strictMono_activeClockSection :
    StrictMono P.activeClockSection := by
  intro s t hst
  by_contra h
  push_neg at h
  have hs := P.activeClockSection_spec s
  have ht := P.activeClockSection_spec t
  have hle : P.activeClock (P.activeClockSection t : ℝ) ≤
      P.activeClock (P.activeClockSection s : ℝ) :=
    P.monotoneOn_activeClock (P.activeClockSection t).2
      (P.activeClockSection s).2 h
  rw [ht, hs] at hle
  exact not_le.mpr hst hle

/-- The clamped real-valued selector into `[0, D]`; monotone and
measurable, possibly discontinuous. -/
def activeTimeSelector (s : ℝ) : ℝ :=
  (P.activeClockSection
    (Set.projIcc 0 P.activeDuration P.activeDuration_bounds.1 s) : ℝ)

theorem activeTimeSelector_mem (s : ℝ) :
    P.activeTimeSelector s ∈ Set.Icc 0 P.duration :=
  (P.activeClockSection _).2

theorem monotone_activeTimeSelector : Monotone P.activeTimeSelector := by
  intro s t hst
  exact P.strictMono_activeClockSection.monotone
    (Set.monotone_projIcc P.activeDuration_bounds.1 hst)

theorem measurable_activeTimeSelector :
    Measurable P.activeTimeSelector :=
  P.monotone_activeTimeSelector.measurable

theorem activeClock_activeTimeSelector (s : ℝ) :
    P.activeClock (P.activeTimeSelector s) =
      (Set.projIcc 0 P.activeDuration P.activeDuration_bounds.1 s : ℝ) :=
  P.activeClockSection_spec _

theorem activeClock_activeTimeSelector_of_mem {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.activeDuration) :
    P.activeClock (P.activeTimeSelector s) = s := by
  rw [P.activeClock_activeTimeSelector]
  rw [Set.projIcc_of_mem P.activeDuration_bounds.1 hs]

/-! ## The active-time state path and control candidate -/

/-- The state path along the selector: `Y(s) = x(σ(s))`. -/
def activePath (s : ℝ) : State := P.path (P.activeTimeSelector s)

theorem activePath_mem (s : ℝ) : P.activePath s ∈ Xset :=
  P.path_mem _ (P.activeTimeSelector_mem s)

theorem activePath_activeClock {t : ℝ} (ht : t ∈ Set.Icc 0 P.duration) :
    P.activePath (P.activeClock t) = P.path t := by
  have hclock : P.activeClock (P.activeTimeSelector (P.activeClock t)) =
      P.activeClock t :=
    P.activeClock_activeTimeSelector_of_mem (P.activeClock_mem ht)
  exact P.path_eq_of_activeClock_eq (P.activeTimeSelector_mem _) ht hclock

theorem lipschitz_activePath : LipschitzWith 1 P.activePath := by
  intro s t
  rw [edist_dist, edist_dist, Real.dist_eq, ENNReal.coe_one, one_mul]
  apply ENNReal.ofReal_le_ofReal
  calc ‖P.activePath s - P.activePath t‖
      = ‖P.path (P.activeTimeSelector s) -
          P.path (P.activeTimeSelector t)‖ := rfl
    _ ≤ |P.activeClock (P.activeTimeSelector s) -
          P.activeClock (P.activeTimeSelector t)| :=
        P.path_dist_le_activeClock (P.activeTimeSelector_mem t)
          (P.activeTimeSelector_mem s)
    _ = |(Set.projIcc 0 P.activeDuration P.activeDuration_bounds.1 s : ℝ) -
          (Set.projIcc 0 P.activeDuration
            P.activeDuration_bounds.1 t : ℝ)| := by
        rw [P.activeClock_activeTimeSelector,
          P.activeClock_activeTimeSelector]
    _ ≤ |s - t| := by
        rw [Set.coe_projIcc, Set.coe_projIcc]
        have h1 : |max 0 (min P.activeDuration s) -
            max 0 (min P.activeDuration t)| ≤
            |min P.activeDuration s - min P.activeDuration t| := by
          have h := abs_max_sub_max_le_max 0 (min P.activeDuration s)
            0 (min P.activeDuration t)
          rwa [sub_self, abs_zero, max_eq_right
            (abs_nonneg (min P.activeDuration s -
              min P.activeDuration t))] at h
        have h2 : |min P.activeDuration s - min P.activeDuration t| ≤
            |s - t| := by
          have h := abs_min_sub_min_le_max P.activeDuration s
            P.activeDuration t
          rwa [sub_self, abs_zero,
            max_eq_right (abs_nonneg (s - t))] at h
        exact h1.trans h2

@[simp] theorem activePath_zero : P.activePath 0 = P.path 0 := by
  have h0 : (0:ℝ) ∈ Set.Icc 0 P.activeDuration :=
    Set.left_mem_Icc.mpr P.activeDuration_bounds.1
  have hclock : P.activeClock (P.activeTimeSelector 0) =
      P.activeClock 0 := by
    rw [P.activeClock_activeTimeSelector_of_mem h0, activeClock_zero]
  exact P.path_eq_of_activeClock_eq (P.activeTimeSelector_mem 0)
    (Set.left_mem_Icc.mpr P.duration_nonneg) hclock

@[simp] theorem activePath_terminal :
    P.activePath P.activeDuration = P.path P.duration := by
  have hS : P.activeDuration ∈ Set.Icc 0 P.activeDuration :=
    Set.right_mem_Icc.mpr P.activeDuration_bounds.1
  have hclock : P.activeClock (P.activeTimeSelector P.activeDuration) =
      P.activeClock P.duration := by
    rw [P.activeClock_activeTimeSelector_of_mem hS]
    rfl
  exact P.path_eq_of_activeClock_eq (P.activeTimeSelector_mem _)
    (Set.right_mem_Icc.mpr P.duration_nonneg) hclock

theorem activePath_image_interval :
    P.activePath '' Set.Icc 0 P.activeDuration =
      P.path '' Set.Icc 0 P.duration := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨P.activeTimeSelector s, P.activeTimeSelector_mem s, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨P.activeClock t, P.activeClock_mem ht,
      P.activePath_activeClock ht⟩

/-- The normalized selected control: unit modulus everywhere,
measurable.  `ActiveDynamics` proves that it drives `activePath`. -/
def activeControl (s : ℝ) : ℂ :=
  controlDirection (P.control (P.activeTimeSelector s))

theorem measurable_activeControl : Measurable P.activeControl :=
  measurable_controlDirection.comp
    (P.control_measurable.comp P.measurable_activeTimeSelector)

theorem norm_activeControl (s : ℝ) : ‖P.activeControl s‖ = 1 :=
  norm_controlDirection _

end CZExposure.PhysicalSegment
