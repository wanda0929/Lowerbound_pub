module
public import RequestProject.AppendixE.ExcursionAssembly
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Cutoff limit `α = β⁵`

The pulse exposure overhead for the cutoff choice `α = β⁵` is exactly
`c_H(T) β^(3/8)`, with
`c_H(T) = H.K³ (3T·32^(3/4) + (8T)^(3/4))/12`.  As `β → 0⁺` the
endpoint displacement, the phase-error bound, and the overhead all
tend to `0`, so a cutoff exists for every prescribed error budget.
Every admissible exposure trajectory therefore yields an exact-CZ
`Pulse` of exposure at most `T + ε`, conditional on `H : LocalSteering`.
No uniform duration bound as `ε → 0` is claimed.
-/

@[expose] public section

noncomputable section

namespace CZExposure.LocalSteering

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable (H : LocalSteering)

/-- The exposure overhead of `exists_pulse_of_exposure_trajectory`. -/
def cutoffOverhead (T α β : ℝ) : ℝ :=
  (3 * T / costThreeHalves β) * H.exposureBound (32 * Real.sqrt α) +
    H.exposureBound (8 * T * Real.sqrt β)

/-- The coefficient of `β^(3/8)` in `cutoffOverhead T (β^5) β`. -/
def cutoffCoefficient (T : ℝ) : ℝ :=
  H.K^3 / 12 * (3 * T * Real.rpow 32 (3/4 : ℝ) +
    Real.rpow (8 * T) (3/4 : ℝ))

theorem cutoffCoefficient_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ H.cutoffCoefficient T := by
  refine mul_nonneg (div_nonneg (pow_nonneg H.K_pos.le 3) (by norm_num))
    (add_nonneg ?_ ?_)
  · exact mul_nonneg (mul_nonneg (by norm_num) hT)
      (Real.rpow_nonneg (by norm_num) _)
  · exact Real.rpow_nonneg (mul_nonneg (by norm_num) hT) _

/-- `β^5 ≤ β/2` whenever `0 ≤ β ≤ 1/12`; no `H` needed. -/
theorem fifth_power_le_half {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1/12) :
    β^5 ≤ β/2 := by
  have h4 : β^4 ≤ (1/2 : ℝ)^4 := pow_le_pow_left₀ hβ0 (by linarith) 4
  have h4' : β^4 ≤ 1/2 := le_trans h4 (by norm_num)
  calc β^5 = β^4 * β := by ring
    _ ≤ (1/2 : ℝ) * β := mul_le_mul_of_nonneg_right h4' hβ0
    _ = β/2 := by ring

/-- The exact `β^(3/8)` law for the overhead at `α = β^5`. -/
theorem cutoffOverhead_eq {T β : ℝ} (hT : 0 ≤ T) (hβ : 0 < β) :
    H.cutoffOverhead T (β^5) β =
      H.cutoffCoefficient T * Real.rpow β (3/8 : ℝ) := by
  have h15 : Real.rpow (β^5) (3/8 : ℝ) = Real.rpow β (15/8 : ℝ) := by
    show (β^5 : ℝ)^(3/8 : ℝ) = β^(15/8 : ℝ)
    rw [← Real.rpow_natCast β 5, ← Real.rpow_mul hβ.le]
    congr 1
    norm_num
  have hc3 : costThreeHalves β = Real.rpow β (3/2 : ℝ) := by
    show β * Real.sqrt β = _
    rw [Real.sqrt_eq_rpow]
    nth_rewrite 1 [← Real.rpow_one β]
    rw [← Real.rpow_add hβ]
    congr 1
    norm_num
  have hend : H.exposureBound (32 * Real.sqrt (β^5)) =
      (H.K^3 * Real.rpow 32 (3/4 : ℝ) / 12) * Real.rpow β (15/8 : ℝ) := by
    have h := H.projection_pair_exposureBound_eq (pow_nonneg hβ.le 5)
    rw [h15] at h
    linarith
  have hph : H.exposureBound (8 * T * Real.sqrt β) =
      (H.K^3/12) * (Real.rpow (8*T) (3/4 : ℝ) * Real.rpow β (3/8 : ℝ)) := by
    rw [H.exposureBound_eq (mul_nonneg (mul_nonneg (by norm_num) hT)
      (Real.sqrt_nonneg β))]
    show H.K^3/12 * ((8*T) * Real.sqrt β)^(3/4 : ℝ) = _
    rw [Real.mul_rpow (mul_nonneg (by norm_num) hT) (Real.sqrt_nonneg β)]
    show _ = H.K^3/12 * ((8*T)^(3/4 : ℝ) * β^(3/8 : ℝ))
    congr 1
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hβ.le]
    congr 1
    norm_num
  have hmul : Real.rpow β (15/8 : ℝ) =
      Real.rpow β (3/2 : ℝ) * Real.rpow β (3/8 : ℝ) := by
    show β^(15/8 : ℝ) = β^(3/2 : ℝ) * β^(3/8 : ℝ)
    rw [← Real.rpow_add hβ]
    congr 1
    norm_num
  have hpos : Real.rpow β (3/2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hβ (3/2 : ℝ)).ne'
  simp only [cutoffOverhead, cutoffCoefficient]
  rw [hend, hph, hc3, hmul]
  field_simp [hpos]

/-- The overhead tends to `0` as `β → 0⁺`. -/
theorem tendsto_cutoffOverhead {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun β : ℝ => H.cutoffOverhead T (β^5) β) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Tendsto (fun β : ℝ =>
      H.cutoffCoefficient T * Real.rpow β (3/8 : ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h0 := (Real.continuous_rpow_const (q := 3/8) (by norm_num)).tendsto 0
    have h0' : Tendsto (fun x : ℝ => x^(3/8 : ℝ)) (𝓝[>] (0:ℝ))
        (𝓝 ((0:ℝ)^(3/8 : ℝ))) :=
      h0.mono_left nhdsWithin_le_nhds
    have hm := h0'.const_mul (H.cutoffCoefficient T)
    simpa [Real.zero_rpow (by norm_num : (3/8 : ℝ) ≠ 0)] using hm
  refine Tendsto.congr' ?_ hc
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (H.cutoffOverhead_eq hT hβ).symm

/-- For every error budget there is an admissible cutoff. -/
theorem exists_cutoff_for_error {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1/12 ∧ β^5 ≤ β/2 ∧
      32 * Real.sqrt (β^5) ≤ H.radius ∧
      8 * T * Real.sqrt β ≤ H.radius ∧
      H.cutoffOverhead T (β^5) β < ε := by
  have hsmall : ∀ᶠ β : ℝ in 𝓝[>] (0:ℝ), β ≤ 1/12 := by
    have hten : Tendsto (id : ℝ → ℝ) (𝓝 (0:ℝ)) (𝓝 0) := tendsto_id
    exact (hten.mono_left nhdsWithin_le_nhds).eventually_le_const
      (by norm_num : (0:ℝ) < 1/12)
  have hEndC : ContinuousAt (fun β : ℝ => 32 * Real.sqrt (β^5)) (0:ℝ) := by
    fun_prop
  have hPhC : ContinuousAt (fun β : ℝ => 8 * T * Real.sqrt β) (0:ℝ) := by
    fun_prop
  have hEnd : ∀ᶠ β : ℝ in 𝓝[>] (0:ℝ), 32 * Real.sqrt (β^5) ≤ H.radius :=
    (by simpa using hEndC.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun β : ℝ => 32 * Real.sqrt (β^5)) (𝓝[>] (0:ℝ)) (𝓝 0)
      ).eventually_le_const H.radius_pos
  have hPhase : ∀ᶠ β : ℝ in 𝓝[>] (0:ℝ), 8 * T * Real.sqrt β ≤ H.radius :=
    (by simpa using hPhC.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun β : ℝ => 8 * T * Real.sqrt β) (𝓝[>] (0:ℝ)) (𝓝 0)
      ).eventually_le_const H.radius_pos
  have hOver : ∀ᶠ β : ℝ in 𝓝[>] (0:ℝ),
      H.cutoffOverhead T (β^5) β < ε :=
    (H.tendsto_cutoffOverhead hT).eventually_lt_const hε
  have hall2 : ∀ᶠ β : ℝ in 𝓝[>] (0:ℝ),
      (0:ℝ) < β ∧ β ≤ 1/12 ∧ 32 * Real.sqrt (β^5) ≤ H.radius ∧
        8 * T * Real.sqrt β ≤ H.radius ∧
        H.cutoffOverhead T (β^5) β < ε := by
    filter_upwards [self_mem_nhdsWithin, hsmall, hEnd, hPhase, hOver]
      with β hpos hs hE hP hO
    exact ⟨hpos, hs, hE, hP, hO⟩
  obtain ⟨β, hβpos, hβs, hE, hP, hO⟩ := hall2.exists
  exact ⟨β, hβpos, hβs, fifth_power_le_half hβpos.le hβs, hE, hP, hO⟩

/-- No cutoffs or radius conditions remain as input. -/
theorem exists_pulse_approx_exposure_trajectory
    (H : LocalSteering)
    {T : ℝ} {y : ℝ → ExposureEuclidean} {u : ℝ → ℂ} {K : NNReal}
    (hT : 0 ≤ T) (hy : LipschitzWith K y)
    (hu : Measurable u) (hub : ∀ t, ‖u t‖ ≤ 1)
    (hdom : ∀ t ∈ Set.Icc 0 T, y t ∈ euclideanExposureDomain)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      HasDerivAt y (euclideanBfield (y t) (u t)) t)
    (hstart : y 0 = exposureEuclideanEquiv y0)
    (hend : y T = exposureEuclideanEquiv yPi)
    {ε : ℝ} (hε : 0 < ε) :
  ∃ γ : Pulse, γ.exposure ≤ T + ε := by
  obtain ⟨β, hβ, hβsmall, hhalf, hEnd, hPhase, hOver⟩ :=
    exists_cutoff_for_error (H := H) hT hε
  have hα : (0:ℝ) < β^5 := pow_pos hβ 5
  obtain ⟨γ, -, hγe⟩ :=
    H.exists_pulse_of_exposure_trajectory (α := β^5) (β := β) hT hα hβ
      hhalf hy hu hub hdom hode hstart hend hβsmall hEnd hPhase
  refine ⟨γ, ?_⟩
  have hOver' : (3 * T / costThreeHalves β) * H.exposureBound (32 * Real.sqrt (β^5)) +
      H.exposureBound (8 * T * Real.sqrt β) < ε := hOver
  linarith

end CZExposure.LocalSteering
