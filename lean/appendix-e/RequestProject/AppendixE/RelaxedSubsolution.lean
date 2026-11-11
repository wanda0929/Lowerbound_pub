module
public import RequestProject.AppendixE.ExposureSeparation

/-!
# Smooth subsolutions below the relaxed value (Appendix E)

The separation theorem of `ExposureSeparation` produces a smooth compactly supported
test whose balance integral is separated from every mass-bounded measure. Normalizing
it with the control-negation symmetry `B(y, -u) = -B(y, u)` yields a unit derivative
bound along the B-field. Pulling back through `Jmap` via the everywhere-valid
identity `c(x) B(Jx, u) = DJ(x) f_u(x)` gives the analogue of Lemma 3 at every real
threshold `a < pRelaxed`, including the zero-cost face, without any completeness gaps.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set Topology Filter BigOperators
open scoped ENNReal NNReal

/-- The vector field is odd in the control. -/
theorem vf_neg_control (x : State) (u : ℂ) : vf x (-u) = -vf x u := by
  funext i
  fin_cases i <;> simp [vf, fC, map_neg]

/-- The B-field is odd in the control on the whole ambient space. -/
theorem Bfield_neg_control (y : Fin 11 → ℝ) (u : ℂ) :
    Bfield y (-u) = -Bfield y u := by
  unfold Bfield
  split_ifs with h
  · simp only [vf_neg_control, map_neg, smul_neg]
  · simp

/-- Below `pRelaxed`, there is a smooth compactly supported subsolution of the
normalized balance equation, by the separation theorem and control negation. -/
theorem exists_unit_balance_subsolution (a : ℝ) (ha : (a : EReal) < pRelaxed) :
    ∃ φ : (Fin 11 → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ y ∈ Yset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        |fderiv ℝ φ y (Bfield y u)| ≤ 1) ∧
      a < φ y0 - φ yPi := by
  rcases lt_or_ge a 0 with hneg | hpos
  · refine ⟨0, contDiff_const, HasCompactSupport.zero, fun y hy u hu => by simp, ?_⟩
    simpa using hneg
  · obtain ⟨b, hab, hbp⟩ := EReal.exists_between_coe_real ha
    have hab' : a < b := by exact_mod_cast hab
    have hb : 0 < b := hpos.trans_lt hab'
    let M : ℝ≥0 := ⟨b, hb.le⟩
    have hM : ((M : ℝ) : EReal) < pRelaxed := hbp
    obtain ⟨ψ, hψ, hψc, r, hr, hbound, hrt⟩ := exists_smooth_balance_separator M hM
    have hdirac : ∀ p : ExposurePoint,
        b * fderiv ℝ ψ p.1.1 (Bfield p.1.1 p.1.2) < r := by
      intro p
      let μp : FiniteMeasure ExposurePoint := ⟨Measure.dirac p, inferInstance⟩
      have hm : (M • μp).mass = M := by
        rw [mass_smul']
        show M * ((Measure.dirac p : Measure ExposurePoint) Set.univ).toNNReal = M
        simp
      have hb2 := hbound _ hm.le
      rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_mk,
        integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def] at hb2
      exact hb2
    have habs : ∀ y ∈ Yset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        |b * fderiv ℝ ψ y (Bfield y u)| < r := by
      intro y hy u hu
      have hmem : (y, u) ∈ exposureDomain :=
        Set.mk_mem_prod hy (by simpa [Metric.mem_closedBall, dist_eq_norm] using hu)
      have hmem' : (y, -u) ∈ exposureDomain :=
        Set.mk_mem_prod hy (by
          simpa [Metric.mem_closedBall, dist_eq_norm] using norm_neg u ▸ hu)
      have h1 := hdirac ⟨(y, u), hmem⟩
      have h2 := hdirac ⟨(y, -u), hmem'⟩
      rw [Bfield_neg_control, map_neg, mul_neg] at h2
      exact abs_lt.mpr ⟨neg_lt.mp h2, h1⟩
    let c : ℝ := -(b / r)
    refine ⟨fun y => c * ψ y, contDiff_const.mul hψ,
      HasCompactSupport.mul_left (f := fun _ => c) hψc, ?_, ?_⟩
    · intro y hy u hu
      have hd : fderiv ℝ (fun y => c * ψ y) y = c • fderiv ℝ ψ y :=
        fderiv_const_mul ((hψ.differentiable (by norm_cast)) y) c
      rw [hd, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul]
      have hcabs : |c| = b / r := by
        show |-(b / r)| = b / r
        rw [abs_neg, abs_of_pos (div_pos hb hr)]
      rw [hcabs]
      have hbL : b * |fderiv ℝ ψ y (Bfield y u)| < r := by
        have := habs y hy u hu
        rwa [abs_mul, abs_of_pos hb] at this
      calc (b / r) * |fderiv ℝ ψ y (Bfield y u)|
          = (b * |fderiv ℝ ψ y (Bfield y u)|) / r := by ring
        _ ≤ 1 := (div_le_one hr).mpr hbL.le
    · show a < c * ψ y0 - c * ψ yPi
      have hΔ : c * ψ y0 - c * ψ yPi = (b / r) * (ψ yPi - ψ y0) := by
        show -(b / r) * ψ y0 - -(b / r) * ψ yPi = (b / r) * (ψ yPi - ψ y0)
        ring
      rw [hΔ]
      have hmul := mul_lt_mul_of_pos_left hrt (div_pos hb hr)
      rw [div_mul_cancel₀ b hr.ne'] at hmul
      exact hab'.trans hmul

/-- The relaxed analogue of Lemma 3: for every `a < pRelaxed`, a smooth compactly
supported subsolution with the B-field derivative bound on `X` and the CZ endpoint
conditions. Includes the zero-cost face via `cost_smul_Bfield`. -/
theorem smooth_subsolution_relaxed (a : ℝ) (ha : (a : EReal) < pRelaxed) :
    ∃ φ : (Fin 11 → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        |fderiv ℝ (fun x' => φ (Jmap x') - φ yPi) x (vf x u)| ≤ cost x) ∧
      (∀ x ∈ XCZ, φ (Jmap x) - φ yPi = 0) ∧
      a < φ (Jmap x0) - φ yPi := by
  obtain ⟨φ, hφ, hφc, hbound, hend⟩ := exists_unit_balance_subsolution a ha
  refine ⟨φ, hφ, hφc, fun x hx u hu => ?_, fun x hx => ?_, ?_⟩
  · have hJ : DifferentiableAt ℝ Jmap x := contDiff_Jmap.differentiable (by simp) x
    have hφd : DifferentiableAt ℝ φ (Jmap x) :=
      hφ.differentiable (by norm_cast) (Jmap x)
    have hderiv : fderiv ℝ (fun x' => φ (Jmap x') - φ yPi) x
        = (fderiv ℝ φ (Jmap x)).comp (fderiv ℝ Jmap x) := by
      rw [fderiv_sub_const]
      exact (hφd.hasFDerivAt.comp x hJ.hasFDerivAt).fderiv
    rw [hderiv, ContinuousLinearMap.comp_apply, ← cost_smul_Bfield, map_smul,
      smul_eq_mul, abs_mul, abs_of_nonneg (cost_nonneg x)]
    calc cost x * |fderiv ℝ φ (Jmap x) (Bfield (Jmap x) u)|
        ≤ cost x * 1 :=
          mul_le_mul_of_nonneg_left (hbound (Jmap x) ⟨x, hx, rfl⟩ u hu)
            (cost_nonneg x)
      _ = cost x := mul_one _
  · rw [Jmap_of_mem_XCZ hx, sub_self]
  · rw [Jmap_x0]
    exact hend

/-- The physical-threshold version follows once exposure-record realization is proved. -/
theorem smooth_subsolution_of_realization (hrealization : Cstar ≤ pRelaxed)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ φ : (Fin 11 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        |fderiv ℝ (fun x' => φ (Jmap x') - φ yPi) x (vf x u)| ≤ cost x) ∧
      (∀ x ∈ XCZ, φ (Jmap x) - φ yPi = 0) ∧
      a < φ (Jmap x0) - φ yPi :=
  smooth_subsolution_relaxed a (ha.trans_le hrealization)

end CZExposure
