module
public import RequestProject.AppendixE.ExposureCoords

/-!
# Exposure records of physical pulses (Appendix E 2, Step 2)

Every successful pulse `γ` induces the exposure record
`ν_γ = ∫₀^S c(x(s)) δ_{(J(x(s)), u(s))} ds`, a finite measure on `Y × U` of mass `C[u]` that
satisfies the net balance identity. Hence the relaxed infimum satisfies `p ≤ C*`.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set


theorem continuous_fderiv_Jmap_vf :
    Continuous (fun q : State × ℂ => fderiv ℝ Jmap q.1 (vf q.1 q.2)) :=
  ((contDiff_Jmap.continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_vf

theorem measurable_Bfield : Measurable (fun p : (Fin 11 → ℝ) × ℂ => Bfield p.1 p.2) := by
  have hxr : Measurable (fun p : (Fin 11 → ℝ) × ℂ => (fun i : Fin 8 => p.1 i.succ.succ.succ / p.1 2)) :=
    measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply _).comp measurable_fst).div ((measurable_pi_apply _).comp measurable_fst)
  have hc : Continuous cost := contDiff_cost.continuous
  refine Measurable.ite (measurableSet_lt measurable_const
    ((measurable_pi_apply 2).comp measurable_fst)) ?_ measurable_const
  exact ((hc.measurable.comp hxr).inv).smul
    (continuous_fderiv_Jmap_vf.measurable.comp (hxr.prodMk measurable_snd))

theorem measurable_balance_integrand {ψ : (Fin 11 → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Measurable (fun p : (Fin 11 → ℝ) × ℂ => fderiv ℝ ψ p.1 (Bfield p.1 p.2)) := by
  have hΘ : Continuous fun q : (Fin 11 → ℝ) × (Fin 11 → ℝ) => fderiv ℝ ψ q.1 q.2 :=
    ((hψ.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd
  exact hΘ.measurable.comp (measurable_fst.prodMk measurable_Bfield)

theorem Pulse.continuousOn_trajVec (γ : Pulse) : ContinuousOn γ.traj (Icc 0 γ.S) :=
  continuousOn_pi.2 γ.continuousOn_traj

theorem exists_vf_bound : ∃ M, ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ‖vf x u‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Xset.prod (isCompact_closedBall (0 : ℂ) 1)).exists_bound_of_continuousOn
    continuous_vf.continuousOn
  exact ⟨M, fun x hx u hu => hM (x, u) ⟨hx, by simpa using hu⟩⟩

theorem Pulse.lipschitzOn_traj (γ : Pulse) : ∃ K, LipschitzOnWith K γ.traj (Icc 0 γ.S) := by
  obtain ⟨M, hM⟩ := exists_vf_bound
  refine ⟨Real.toNNReal M, LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_⟩
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hsub : γ.traj s i - γ.traj s' i = ∫ t in s'..s, vf (γ.x t) (γ.u t) i := by
    simp only [Pulse.traj]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left]
    · exact (γ.integrable i).mono_set (by
        rw [uIcc_of_le γ.S_nonneg]; exact uIcc_subset_Icc ⟨le_rfl, γ.S_nonneg⟩ hs)
    · exact (γ.integrable i).mono_set (by
        rw [uIcc_of_le γ.S_nonneg]; exact uIcc_subset_Icc ⟨le_rfl, γ.S_nonneg⟩ hs')
  rw [Real.dist_eq, hsub, ← Real.norm_eq_abs]
  have hb : ∀ t ∈ uIoc s' s, ‖vf (γ.x t) (γ.u t) i‖ ≤ M := by
    intro t ht
    have htS : t ∈ Icc 0 γ.S := uIcc_subset_Icc hs' hs (uIoc_subset_uIcc ht)
    exact (norm_le_pi_norm (vf (γ.x t) (γ.u t)) i).trans
      (hM _ (γ.x_mem t htS) _ (γ.u_unit t htS).le)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  rw [Real.dist_eq, abs_sub_comm]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (γ.x_mem s hs) _ (γ.u_unit s hs).le)
  rw [Real.coe_toNNReal _ hM0]

theorem Pulse.integral_fderiv_traj (γ : Pulse) {Φ : State → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    ∫ s in (0 : ℝ)..γ.S, fderiv ℝ Φ (γ.traj s) (vf (γ.x s) (γ.u s)) = Φ (γ.x γ.S) - Φ x0 := by
  have hS := γ.S_nonneg
  obtain ⟨K, hK⟩ := γ.lipschitzOn_traj
  obtain ⟨L, hL⟩ := (hΦ.contDiffOn (s := Metric.closedBall (0 : State) 1)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hmaps : MapsTo γ.traj (Icc 0 γ.S) (Metric.closedBall 0 1) := fun s hs => by
    rw [γ.traj_eq hs]; exact Xset_subset_closedBall (γ.x_mem s hs)
  have hF : LipschitzOnWith (L * K) (fun s => Φ (γ.traj s)) (Icc 0 γ.S) := hL.comp hK hmaps
  have hAC : AbsolutelyContinuousOnInterval (fun s => Φ (γ.traj s)) 0 γ.S := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval; rwa [uIcc_of_le hS]
  have hFTC := hAC.integral_deriv_eq_sub
  rw [γ.traj_eq ⟨hS, le_rfl⟩, γ.traj_zero] at hFTC
  rw [← hFTC]
  refine intervalIntegral.integral_congr_ae ?_
  have hderiv : ∀ i, ∀ᵐ t, t ∈ uIcc 0 γ.S → ∀ c ∈ uIcc 0 γ.S,
      HasDerivAt (fun x => ∫ s in c..x, vf (γ.x s) (γ.u s) i) (vf (γ.x t) (γ.u t) i) t :=
    fun i => (γ.integrable i).ae_hasDerivAt_integral
  rw [← ae_all_iff] at hderiv
  filter_upwards [hderiv] with t ht htI
  have htc : t ∈ uIcc 0 γ.S := uIoc_subset_uIcc htI
  have htr : HasDerivAt γ.traj (vf (γ.x t) (γ.u t)) t := by
    rw [hasDerivAt_pi]; intro i
    exact (ht i htc 0 (by rw [uIcc_of_le hS]; exact ⟨le_rfl, hS⟩)).const_add (x0 i)
  have := ((hΦ.differentiable one_ne_zero) (γ.traj t)).hasFDerivAt.comp_hasDerivAt t htr
  exact this.deriv.symm

/-- The exposure record `ν_γ = ∫₀^S c(x(s)) δ_{(J(x(s)), u(s))} ds` of a successful pulse. -/
def Pulse.record (γ : Pulse) : Measure ((Fin 11 → ℝ) × ℂ) :=
  Measure.map (fun s => (Jmap (γ.traj s), γ.u s))
    ((volume.restrict (Icc 0 γ.S)).withDensity (fun s => ENNReal.ofReal (cost (γ.traj s))))

theorem Pulse.aemeasurable_density (γ : Pulse) :
    AEMeasurable (fun s => ENNReal.ofReal (cost (γ.traj s))) (volume.restrict (Icc 0 γ.S)) :=
  (γ.continuousOn_cost_traj.aemeasurable measurableSet_Icc).ennreal_ofReal

theorem Pulse.aemeasurable_recordMap (γ : Pulse) :
    AEMeasurable (fun s => (Jmap (γ.traj s), γ.u s))
      ((volume.restrict (Icc 0 γ.S)).withDensity (fun s => ENNReal.ofReal (cost (γ.traj s)))) := by
  refine AEMeasurable.mono_ac ?_ (withDensity_absolutelyContinuous _ _)
  exact ((contDiff_Jmap.continuous.comp_continuousOn γ.continuousOn_trajVec).aemeasurable
    measurableSet_Icc).prodMk γ.u_measurable.aemeasurable

theorem Pulse.record_univ (γ : Pulse) : γ.record univ = ENNReal.ofReal γ.exposure := by
  rw [Pulse.record, Measure.map_apply_of_aemeasurable γ.aemeasurable_recordMap MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    γ.exposure_eq, intervalIntegral.integral_of_le γ.S_nonneg, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal]
  · exact γ.continuousOn_cost_traj.integrableOn_Icc
  · exact Filter.Eventually.of_forall fun _ => cost_nonneg _

theorem Pulse.record_compl (γ : Pulse) :
    γ.record (Yset ×ˢ Metric.closedBall (0 : ℂ) 1)ᶜ = 0 := by
  have hmeas : MeasurableSet (Yset ×ˢ Metric.closedBall (0 : ℂ) 1)ᶜ :=
    (isCompact_Yset.isClosed.measurableSet.prod measurableSet_closedBall).compl
  rw [Pulse.record, Measure.map_apply_of_aemeasurable γ.aemeasurable_recordMap hmeas]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Icc]
  convert measure_empty (μ := volume)
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_prod, mem_empty_iff_false,
    iff_false, not_and]
  intro h hs
  refine h ⟨γ.x s, γ.x_mem s hs, by rw [γ.traj_eq hs]⟩ ?_
  simp [γ.u_unit s hs]

theorem Pulse.record_balance (γ : Pulse) {ψ : (Fin 11 → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    ∫ p, fderiv ℝ ψ p.1 (Bfield p.1 p.2) ∂γ.record = ψ yPi - ψ y0 := by
  have hS := γ.S_nonneg
  rw [Pulse.record, integral_map γ.aemeasurable_recordMap
    (measurable_balance_integrand hψ).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ γ.aemeasurable_density
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ s ∈ Icc 0 γ.S, (ENNReal.ofReal (cost (γ.traj s))).toReal •
      fderiv ℝ ψ (Jmap (γ.traj s)) (Bfield (Jmap (γ.traj s)) (γ.u s)) =
      fderiv ℝ (ψ ∘ Jmap) (γ.traj s) (vf (γ.x s) (γ.u s)) := by
    intro s hs
    rw [ENNReal.toReal_ofReal (cost_nonneg _), ← map_smul, cost_smul_Bfield,
      fderiv_comp _ ((hψ.differentiable one_ne_zero) _)
        ((contDiff_Jmap.differentiable (by simp)) _), γ.traj_eq hs]
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc hpt, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hS,
    γ.integral_fderiv_traj (hψ.comp (contDiff_Jmap.of_le le_top)),
    Function.comp_apply, Function.comp_apply, Jmap_of_mem_XCZ γ.terminal, Jmap_x0]

/-- Each successful pulse induces a feasible exposure record whose mass is its exposure. -/
theorem Pulse.isExposureRecord (γ : Pulse) : IsExposureRecord γ.record :=
  ⟨⟨by rw [γ.record_univ]; exact ENNReal.ofReal_lt_top⟩, γ.record_compl,
    fun _ hψ _ => γ.record_balance (hψ.of_le (by norm_cast))⟩

/-- Step 2 of Appendix E 2: the relaxed infimum satisfies `p ≤ C*`. -/
theorem pRelaxed_le_Cstar : pRelaxed ≤ Cstar := by
  refine le_iInf fun γ => ?_
  refine (iInf₂_le γ.record γ.isExposureRecord).trans ?_
  rw [γ.record_univ, EReal.coe_ennreal_ofReal, max_eq_left γ.exposure_nonneg]

end CZExposure
