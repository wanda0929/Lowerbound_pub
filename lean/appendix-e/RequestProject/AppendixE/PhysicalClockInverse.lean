module
public import RequestProject.AppendixE.PhysicalClock
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Inverse physical clock

`σ : [a,b] ≃ [0,D]` is an order isomorphism (strict monotonicity from the
`1/c` rate bound); its real-valued inverse `ψ` is globally 1-Lipschitz after
clamping.  The forward clock is differentiable at EVERY point of `[a,b]`, so
the pinned null-image theorem
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` transports
arbitrary a.e. predicates — no measurability hypothesis needed.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set
open scoped Topology

namespace PositiveExposureSegment

variable (S : PositiveExposureSegment)

theorem continuousOn_clock : ContinuousOn S.clock (Set.Icc S.a S.b) :=
  fun _ ht => (S.hasDerivAt_clock ht).continuousAt.continuousWithinAt

theorem clock_image_interval :
    S.clock '' Set.Icc S.a S.b = Set.Icc (0 : ℝ) S.duration := by
  have h := ContinuousOn.image_Icc_of_monotoneOn S.a_lt_b.le
    S.continuousOn_clock S.strictMonoOn_clock.monotoneOn
  rw [S.clock_at_start] at h
  exact h

def clockOrderIso : Set.Icc S.a S.b ≃o Set.Icc (0 : ℝ) S.duration :=
  (S.strictMonoOn_clock.orderIso _ _).trans
    (OrderIso.setCongr _ _ S.clock_image_interval)

@[simp] theorem coe_clockOrderIso_apply (t : Set.Icc S.a S.b) :
    (S.clockOrderIso t : ℝ) = S.clock (t : ℝ) := rfl

def clockInverse : Set.Icc (0 : ℝ) S.duration → Set.Icc S.a S.b :=
  S.clockOrderIso.symm

@[simp] theorem clock_clockInverse (s : Set.Icc (0 : ℝ) S.duration) :
    S.clock (S.clockInverse s : ℝ) = (s : ℝ) :=
  congrArg Subtype.val (S.clockOrderIso.apply_symm_apply s)

theorem clock_dist_lower_bound {s t : ℝ}
    (hs : s ∈ Set.Icc S.a S.b) (ht : t ∈ Set.Icc S.a S.b) :
    dist s t ≤ dist (S.clock s) (S.clock t) := by
  rcases le_total s t with hst | hts
  · rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr
        (S.strictMonoOn_clock.monotoneOn hs ht hst)),
      abs_of_nonpos (sub_nonpos.mpr hst)]
    have h := (S.clock_increment_bounds hs ht hst).1
    linarith
  · rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hts),
      abs_of_nonneg (sub_nonneg.mpr
        (S.strictMonoOn_clock.monotoneOn ht hs hts))]
    exact (S.clock_increment_bounds ht hs hts).1

theorem lipschitz_clockInverse : LipschitzWith 1 S.clockInverse := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc dist (S.clockInverse s) (S.clockInverse t)
      ≤ dist (S.clock (S.clockInverse s : ℝ))
          (S.clock (S.clockInverse t : ℝ)) :=
        S.clock_dist_lower_bound (S.clockInverse s).property
          (S.clockInverse t).property
    _ = dist (s : ℝ) (t : ℝ) := by
        rw [S.clock_clockInverse, S.clock_clockInverse]
    _ = dist s t := rfl
    _ = 1 * dist s t := by rw [one_mul]

/-- Constant extension via clamping; inverse identities only on clock
intervals. -/
def clockInverseReal (s : ℝ) : ℝ :=
  (S.clockInverse
    (Set.projIcc 0 S.duration S.duration_bounds.1.le s) : ℝ)

theorem clockInverseReal_mem (s : ℝ) :
    S.clockInverseReal s ∈ Set.Icc S.a S.b := (S.clockInverse _).property

theorem clockInverseReal_of_mem {s : ℝ} (hs : s ∈ Set.Icc 0 S.duration) :
    S.clockInverseReal s = (S.clockInverse ⟨s, hs⟩ : ℝ) := by
  show (S.clockInverse (Set.projIcc 0 S.duration
    S.duration_bounds.1.le s) : ℝ) = _
  rw [Set.projIcc_of_mem _ hs]

theorem lipschitz_clockInverseReal : LipschitzWith 1 S.clockInverseReal := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hproj := (LipschitzWith.projIcc
    (b := S.duration) S.duration_bounds.1.le).dist_le_mul x y
  have hinv := S.lipschitz_clockInverse.dist_le_mul
    (Set.projIcc 0 S.duration S.duration_bounds.1.le x)
    (Set.projIcc 0 S.duration S.duration_bounds.1.le y)
  calc dist (S.clockInverseReal x) (S.clockInverseReal y)
      ≤ 1 * dist
          (Set.projIcc 0 S.duration S.duration_bounds.1.le x)
          (Set.projIcc 0 S.duration S.duration_bounds.1.le y) :=
        hinv
    _ ≤ 1 * (1 * dist x y) :=
        mul_le_mul_of_nonneg_left hproj zero_le_one
    _ = 1 * dist x y := by rw [one_mul]

theorem continuous_clockInverseReal : Continuous S.clockInverseReal :=
  S.lipschitz_clockInverseReal.continuous

theorem clock_clockInverseReal {s : ℝ} (hs : s ∈ Set.Icc 0 S.duration) :
    S.clock (S.clockInverseReal s) = s := by
  rw [S.clockInverseReal_of_mem hs, S.clock_clockInverse]

theorem clockInverseReal_clock {t : ℝ} (ht : t ∈ Set.Icc S.a S.b) :
    S.clockInverseReal (S.clock t) = t := by
  have hmem : S.clock t ∈ Set.Icc 0 S.duration := by
    have h : S.clock t ∈ S.clock '' Set.Icc S.a S.b := ⟨t, ht, rfl⟩
    rwa [S.clock_image_interval] at h
  have hsub : (⟨S.clock t, hmem⟩ : Set.Icc (0 : ℝ) S.duration) =
      S.clockOrderIso ⟨t, ht⟩ :=
    Subtype.ext (S.coe_clockOrderIso_apply ⟨t, ht⟩)
  rw [S.clockInverseReal_of_mem hmem, clockInverse, hsub]
  exact congrArg Subtype.val (S.clockOrderIso.symm_apply_apply ⟨t, ht⟩)

theorem clockInverseReal_zero : S.clockInverseReal 0 = S.a := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 S.duration :=
    Set.left_mem_Icc.mpr S.duration_bounds.1.le
  have hval : S.clock (S.clockInverseReal 0) = S.clock S.a := by
    rw [S.clock_clockInverseReal hmem0, S.clock_at_start]
  exact S.strictMonoOn_clock.injOn (S.clockInverseReal_mem 0)
    ⟨le_rfl, S.a_lt_b.le⟩ hval

theorem clockInverseReal_terminal : S.clockInverseReal S.duration = S.b := by
  have hmemD : S.duration ∈ Set.Icc 0 S.duration :=
    Set.right_mem_Icc.mpr S.duration_bounds.1.le
  have hval : S.clock (S.clockInverseReal S.duration) = S.clock S.b := by
    rw [S.clock_clockInverseReal hmemD]
    rfl
  exact S.strictMonoOn_clock.injOn (S.clockInverseReal_mem S.duration)
    ⟨S.a_lt_b.le, le_rfl⟩ hval

/-- a.e. transfer through the forward clock: the image of the exceptional
set is null because `σ` is differentiable everywhere on `[a,b]` — no
measurability hypothesis on `P`. -/
theorem clockInverseReal_ae_transfer {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂(volume.restrict (Set.Icc S.a S.b)), P t) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 S.duration)),
      P (S.clockInverseReal s) := by
  classical
  let N : Set ℝ := {t | t ∈ Set.Icc S.a S.b ∧ ¬P t}
  have hN : volume N = 0 := by
    simpa only [N, Classical.not_imp] using
      (ae_iff.mp ((ae_restrict_iff' measurableSet_Icc).mp hP))
  have hdiff : DifferentiableOn ℝ S.clock N :=
    fun t ht =>
      (S.hasDerivAt_clock ht.1).differentiableAt.differentiableWithinAt
  have hImage : volume (S.clock '' N) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume hdiff hN
  have hsub : {s | s ∈ Set.Icc 0 S.duration ∧ ¬P (S.clockInverseReal s)} ⊆
      S.clock '' N := by
    intro s hs
    exact ⟨S.clockInverseReal s, ⟨S.clockInverseReal_mem s, hs.2⟩,
      S.clock_clockInverseReal hs.1⟩
  have hBad := measure_mono_null hsub hImage
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  apply ae_iff.mpr
  simpa only [Classical.not_imp] using hBad

end PositiveExposureSegment

end CZExposure
