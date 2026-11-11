/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.AppendixE.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Appendix E — patching exponent arithmetic and error limit

Exact real-power facts behind the threshold coupling `a = b⁵` at the end of
the patching subsection of Appendix E (`main.tex` lines 2038–2053):

* `b^(−3/2) · (b⁵)^(3/8) = b^(3/8)` — the exponent bookkeeping showing the
  coupled choice removes the singular factor;
* `K (T + T^(3/4)) b^(3/8) → 0` as `b → 0⁺` — the assembled error bound;
* `b⁵ < b/2` eventually — the threshold `a = b⁵` is admissible for small `b`;
* a combination lemma turning a *hypothetical* patched family bound
  `C_{b⁵,b} ≤ T + K(T + T^{3/4}) b^{3/8}` into `physicalInfimum ≤ T`.

All powers are `Real.rpow`; no floating-point approximations. The final
theorem explicitly assumes the existence of the patched pulse family — the
ball-box controllability and phase-repair estimates are not proved here.
-/

noncomputable section

namespace LowerBoundCZ.AppendixE

open Filter

/-- Exact exponent arithmetic for the coupling `a = b⁵`:
`b^(−3/2) (b⁵)^(3/8) = b^(3/8)`. -/
theorem coupled_threshold_power {b : ℝ} (hb : 0 < b) :
    b ^ (-(3 / 2 : ℝ)) * (b ^ 5) ^ (3 / 8 : ℝ) = b ^ (3 / 8 : ℝ) := by
  rw [← Real.rpow_natCast b 5, ← Real.rpow_mul hb.le, ← Real.rpow_add hb]
  congr 1
  norm_num

/-- The assembled patching error tends to zero along `b ↓ 0`. -/
theorem patching_error_tendsto_zero (K T : ℝ) :
    Tendsto (fun b : ℝ => K * (T + T ^ (3 / 4 : ℝ)) * b ^ (3 / 8 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hid : Tendsto (fun b : ℝ => b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc : ContinuousAt (fun b : ℝ => b ^ (3 / 8 : ℝ)) 0 :=
    continuousAt_id.rpow_const (Or.inr (by norm_num))
  have hpow : Tendsto (fun b : ℝ => b ^ (3 / 8 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hc.tendsto.comp hid
  simpa using hpow.const_mul (K * (T + T ^ (3 / 4 : ℝ)))

/-- For sufficiently small positive `b`, the coupled threshold `a = b⁵` is
positive and below `b/2`, as required by the patching scale separation. -/
theorem threshold_eventually_valid :
    ∀ᶠ (b : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 < b ^ 5 ∧ b ^ 5 < b / 2 := by
  have h4 : Tendsto (fun b : ℝ => b ^ 4) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (continuous_pow 4).tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have h4lt := h4.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hboth : ∀ᶠ (b : ℝ) in nhdsWithin 0 (Set.Ioi 0), b ^ 4 < 1 / 2 ∧ 0 < b :=
    h4lt.and eventually_mem_nhdsWithin
  refine hboth.mono fun b hb4hb => ?_
  obtain ⟨hb4, hb⟩ := hb4hb
  refine ⟨pow_pos hb 5, ?_⟩
  have hneg : b * (b ^ 4 - 1 / 2) < 0 := mul_neg_of_pos_of_neg hb (by linarith)
  have e : b * (b ^ 4 - 1 / 2) = b ^ 5 - b / 2 := by ring
  linarith

/-- CONDITIONAL combination of the family bound with the error limit:
if for all sufficiently small `b > 0` there is a physical CZ trajectory of
exposure at most `T + K (T + T^{3/4}) b^{3/8}` — the patched pulse family of
the paper, here an explicit hypothesis — then `physicalInfimum ≤ T`. No
controllability or patching estimate is proved in this file. -/
theorem physicalInfimum_le_of_threshold_family
    (hne : physicalCosts.Nonempty) (K T b0 : ℝ) (hb0 : 0 < b0)
    (hfamily : ∀ b : ℝ, 0 < b → b < b0 →
      ∃ C ∈ physicalCosts, C ≤ T + K * (T + T ^ (3 / 4 : ℝ)) * b ^ (3 / 8 : ℝ)) :
    physicalInfimum ≤ T := by
  apply physicalInfimum_le_of_patching hne
  intro ε hε
  have hlim := (patching_error_tendsto_zero K T).eventually (Iio_mem_nhds hε)
  have hsmall : ∀ᶠ (b : ℝ) in nhdsWithin 0 (Set.Ioi 0), (0 : ℝ) < b ∧ b < b0 :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (Iio_mem_nhds hb0))
  obtain ⟨b, hbε, hb⟩ := (hlim.and hsmall).exists
  obtain ⟨C, hC, hCT⟩ := hfamily b hb.1 hb.2
  exact ⟨C, hC, by linarith⟩

end LowerBoundCZ.AppendixE
