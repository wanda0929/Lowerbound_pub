import LowerBoundCZ.UpperAnalytic
import LowerBoundCZ.UpperSegments

/-! From a certified root of the finite recurrence to a successful integral-model pulse. -/
noncomputable section
namespace LowerBoundCZ.Certification.Upper
open CZExposure Complex Set

private theorem negative_cross_closure (a b : ℂ) (ha : normSq a = 1) (hb : normSq b = 1)
    (hi : (b * star (a*a)).im = 0) (hr : (b * star (a*a)).re < 0) : b = -a^2 := by
  have hn : normSq (b * star (a*a)) = 1 := by
    simp [normSq_mul, ha, hb]
  have hre : (b * star (a*a)).re = -1 := by
    rw [normSq_apply, hi] at hn
    nlinarith
  have hc : b * star (a*a) = -1 := by
    apply Complex.ext
    · exact hre
    · simpa only [Complex.neg_im, Complex.one_im, neg_zero] using hi
  have hu : star (a*a) * (a*a) = 1 := by
    rw [Complex.star_def, ← normSq_eq_conj_mul_self]
    simp [normSq_mul, ha]
  have he := congrArg (fun z : ℂ => z * (a*a)) hc
  simpa only [mul_assoc, hu, mul_one, neg_one_mul, pow_two] using he

private theorem records_terminal (a b : SectorRecord)
    (ha : normSq a.ground + normSq a.rydberg = 1)
    (hb : normSq b.ground + normSq b.rydberg = 1)
    (hz : ![a.rydberg.re, a.rydberg.im, b.rydberg.re, b.rydberg.im,
      (b.ground * star (a.ground*a.ground)).im] = 0)
    (hbranch : (b.ground * star (a.ground*a.ground)).re < 0) :
    stateOf a b ∈ XCZ := by
  have hr1 : a.rydberg = 0 := by
    apply Complex.ext
    · exact congrFun hz 0
    · exact congrFun hz 1
  have hr2 : b.rydberg = 0 := by
    apply Complex.ext
    · exact congrFun hz 2
    · exact congrFun hz 3
  have hi : (b.ground * star (a.ground*a.ground)).im = 0 := congrFun hz 4
  have hna : normSq a.ground = 1 := by
    change normSq a.ground + normSq a.rydberg = 1 at ha
    simpa only [hr1, normSq_zero, add_zero] using ha
  have hnb : normSq b.ground = 1 := by
    change normSq b.ground + normSq b.rydberg = 1 at hb
    simpa only [hr2, normSq_zero, add_zero] using hb
  have hg := negative_cross_closure a.ground b.ground hna hnb hi hbranch
  exact ⟨stateOf_mem _ _ ha hb, by simpa [stateOf] using hr1,
    by simpa [stateOf] using hr2, by simpa [stateOf] using hg⟩

theorem residual_zero_terminal (fixed : Fin 12672 → ℝ) (p : Parameters)
    (hz : residual fixed p = 0) (hbranch : branch fixed p < 0) :
    stateOf (propagate fixed p 1) (propagate fixed p 2) ∈ XCZ :=
  records_terminal _ _ (propagate_normalization fixed p 1)
    (propagate_normalization fixed p 2) hz hbranch

theorem pulse_of_root (fixed : Fin 12672 → ℝ) (p : Parameters) (hd : 0 ≤ p 0)
    (hz : residual fixed p = 0) (hb : branch fixed p < 0) :
    ∃ γ : ActivePulse, γ.S = p 0 ∧ γ.exposure = exposure fixed p := by
  obtain ⟨P, hPu, hPd, hPi, hPe, hPc⟩ := exists_assembly (phase fixed p)
    (p 0 / 12672) (by positivity) (List.finRange 12672)
    ⟨1, 0, 0⟩ ⟨1, 0, 0⟩ (by norm_num) (by norm_num)
  have hs : P.path 0 = x0 := hPi
  have he : P.path P.duration ∈ XCZ := by
    rw [hPe]
    exact residual_zero_terminal fixed p hz hb
  refine ⟨P.toPulse hPu hs he, ?_, ?_⟩
  · change P.duration = p 0
    simpa only [List.length_finRange, Nat.cast_ofNat, mul_div_cancel₀ _ (by norm_num : (12672 : ℝ) ≠ 0)] using hPd
  · change P.exposure = exposure fixed p
    change P.exposure = exposure fixed p - populationCost ⟨1, 0, 0⟩ ⟨1, 0, 0⟩ at hPc
    simpa only [populationCost, mul_zero, add_zero, zero_div, sub_zero] using hPc

theorem Checks.exists_pulse {a : Payload} (h : Checks a) :
    ∃ γ : ActivePulse, γ.exposure < LowerBoundCZ.upperEndpoint := by
  obtain ⟨p, hp, hz⟩ := h.exists_root
  obtain ⟨γ, _, he⟩ := pulse_of_root a.fixed p (h.duration_pos p hp).le hz (h.cz_branch p hp)
  exact ⟨γ, he ▸ h.exposure_bound p hp⟩

theorem Checks.active_upper {a : Payload} (h : Checks a) :
    activeCstar < (LowerBoundCZ.upperEndpoint : EReal) := by
  obtain ⟨γ, hγ⟩ := h.exists_pulse
  exact (iInf_le (fun γ : ActivePulse => (γ.exposure : EReal)) γ).trans_lt
    (EReal.coe_lt_coe_iff.mpr hγ)

theorem Checks.lab_upper {a : Payload} (h : Checks a) :
    labCstar < (LowerBoundCZ.upperEndpoint : EReal) := by
  rw [labCstar_eq_activeCstar]
  exact h.active_upper

end LowerBoundCZ.Certification.Upper
