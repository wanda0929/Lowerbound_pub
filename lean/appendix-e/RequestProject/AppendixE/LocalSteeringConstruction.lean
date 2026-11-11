module
public import RequestProject.AppendixE.EndpointMap
public import RequestProject.AppendixE.QuantitativeSteering

/-! Finite physical realization and uniform quantitative local steering. -/
@[expose] public section
noncomputable section
namespace CZExposure.LocalSteeringConstruction
open ControlLie PulseWords PulseExpansion SignedRootPulse EndpointMap RootRegularity
open scoped Topology

/-- The tail runs first, exactly as in `EndpointMap.state`. -/
def trajectory (is : List (Fin 6)) (p : Params) :
    {P : PhysicalSegment // P.path 0 = x0 ∧ P.path P.duration = state is p} :=
  match is with
  | [] => ⟨PhysicalSegment.unitZero x0 origin_mem, rfl, rfl⟩
  | i :: js =>
    let P := trajectory js p
    let Q := physical (six i) (orders i) (p i) (state js p) (state_mem js p)
    let hm := P.property.2.trans Q.property.symm
    ⟨P.val.concat Q.val hm, by
      constructor
      · exact (PhysicalSegment.concat_initial _ _ _).trans P.property.1
      · exact (PhysicalSegment.concat_terminal _ _ _).trans (physical_terminal _ _ _ _ _)⟩

theorem trajectory_duration (is : List (Fin 6)) (p : Params) :
    (trajectory is p).val.duration =
      (is.map fun i => (six i).length * root (orders i : ℝ)⁻¹ (p i)).sum := by
  induction is with
  | nil => rfl
  | cons i js ih => simp [trajectory, physical_duration, ih, add_comm]

theorem trajectory_unit (is : List (Fin 6)) (p : Params) :
    (trajectory is p).val.UnitControl := by
  induction is with
  | nil => exact PhysicalSegment.unitZero_unit _ _
  | cons i js ih =>
    exact PhysicalSegment.concat_unit _ _
      ((trajectory js p).property.2.trans
        (physical (six i) (orders i) (p i) (state js p) (state_mem js p)).property.symm)
      ih (physical_unit _ _ _ _ _)

theorem root_le_quarter (i : Fin 6) (p : Params) (h : ‖p‖ ≤ 1) :
    root (orders i : ℝ)⁻¹ (p i) ≤ ‖p‖ ^ (1/4 : ℝ) := by
  have he : (1/4 : ℝ) ≤ (orders i : ℝ)⁻¹ := by
    fin_cases i <;> norm_num [orders]
  calc
    root (orders i : ℝ)⁻¹ (p i) ≤ ‖p‖ ^ (orders i : ℝ)⁻¹ :=
      Real.rpow_le_rpow (abs_nonneg _) (by simpa using norm_le_pi_norm p i)
        (le_trans (by norm_num) he)
    _ ≤ ‖p‖ ^ (1/4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge_of_imp (norm_nonneg _) h he
        (by simp [orders_ne_zero])

theorem trajectory_bound (p : Params) (h : ‖p‖ ≤ 1) :
    (trajectory indices p).val.duration ≤ 48 * ‖p‖ ^ (1/4 : ℝ) := by
  rw [trajectory_duration]
  have hb (i : Fin 6) := mul_le_mul_of_nonneg_left (root_le_quarter i p h)
    (show (0 : ℝ) ≤ (six i).length by positivity)
  have hsum := List.sum_le_sum (l := indices)
    (f := fun i => (six i).length * root (orders i : ℝ)⁻¹ (p i))
    (g := fun i => (six i).length * ‖p‖ ^ (1/4 : ℝ)) (fun i _ => hb i)
  convert hsum using 1
  simp [indices, congrFun six_lengths]
  ring

theorem origin_steering : ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
    ∀ y ∈ Xset, ‖y - x0‖ ≤ r → ∃ P : PhysicalSegment,
      P.path 0 = x0 ∧ P.path P.duration = y ∧
      P.duration ≤ K * ‖y - x0‖ ^ (1/4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := parameters_bound
  let M := C * (‖chart‖ + 1)
  have hM : 0 < M := mul_pos hC (by positivity)
  have hc : ContinuousAt chart x0 := chart.continuous.continuousAt
  have hp : ContinuousAt (fun y => parameters (chart y)) x0 :=
    parameters_deriv.continuousAt.comp_of_eq hc chart_origin
  have hb : ∀ᶠ y in 𝓝 x0, ‖parameters (chart y)‖ ≤ C * ‖chart y‖ :=
    hc (by simpa only [chart_origin] using hbound)
  have hs : ∀ᶠ y in 𝓝 x0, ‖parameters (chart y)‖ < 1 := by
    have hh := hp.norm.eventually (gt_mem_nhds (show ‖parameters (chart x0)‖ < 1 by
      simp [chart_origin, parameters_zero]))
    exact hh
  have hall : ∀ᶠ y in 𝓝 x0, y ∈ Xset → ∃ P : PhysicalSegment,
      P.path 0 = x0 ∧ P.path P.duration = y ∧
      P.duration ≤ (48 * M ^ (1/4 : ℝ)) * ‖y - x0‖ ^ (1/4 : ℝ) := by
    filter_upwards [hb, hs, exact_endpoint] with y hb hs he
    intro hy
    refine ⟨(trajectory indices (parameters (chart y))).val,
      (trajectory _ _).property.1, (trajectory _ _).property.2.trans (he hy), ?_⟩
    have hchart : ‖chart y‖ ≤ (‖chart‖ + 1) * ‖y - x0‖ := by
      have hh := chart.le_opNorm (y - x0)
      rw [map_sub, chart_origin, sub_zero] at hh
      nlinarith [norm_nonneg (y - x0)]
    have hb' : ‖parameters (chart y)‖ ≤ M * ‖y - x0‖ :=
      hb.trans (by simpa [M, mul_assoc] using mul_le_mul_of_nonneg_left hchart hC.le)
    calc
      _ ≤ 48 * ‖parameters (chart y)‖ ^ (1/4 : ℝ) := trajectory_bound _ hs.le
      _ ≤ 48 * (M * ‖y - x0‖) ^ (1/4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hb' (by norm_num))
          (by norm_num)
      _ = _ := by rw [Real.mul_rpow hM.le (norm_nonneg _)]; ring
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r/2, 48 * M ^ (1/4 : ℝ), by positivity, by positivity, ?_⟩
  intro y hy hd
  apply hball (show y ∈ Metric.ball x0 r from ?_) hy
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

/-- A uniform radius and duration constant, with no ball-box or steering input. -/
theorem uniform_steering : ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
    ∀ x ∈ Xset, ∀ y ∈ Xset, ‖y - x‖ ≤ r → ∃ P : PhysicalSegment,
      P.path 0 = x ∧ P.path P.duration = y ∧
      P.duration ≤ K * ‖y - x‖ ^ (1/4 : ℝ) := by
  obtain ⟨r, K, hr, hK, hconnect⟩ := origin_steering
  refine ⟨r/4, K * (4 : ℝ) ^ (1/4 : ℝ), by positivity, by positivity, ?_⟩
  intro x hx y hy hd
  let z := ControlTranslation.translate (ControlTranslation.inverse x) y
  have hz : z ∈ Xset := ControlTranslation.translate_mem (ControlTranslation.inverse_mem hx) hy
  have hdist : ‖z - x0‖ ≤ 4 * ‖y - x‖ := ControlTranslation.relative_target_distance hx y
  obtain ⟨P, hstart, hend, htime⟩ := hconnect z hz (by linarith)
  refine ⟨ControlTranslation.segment x hx P, ?_, ?_, ?_⟩
  · exact (ControlTranslation.transport_endpoints hx P hstart hend).1
  · exact (ControlTranslation.transport_endpoints hx P hstart hend).2
  · calc
      _ = P.duration := rfl
      _ ≤ K * ‖z - x0‖ ^ (1/4 : ℝ) := htime
      _ ≤ K * (4 * ‖y - x‖) ^ (1/4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist (by norm_num)) hK.le
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _)]; ring

/-- The system-specific quantitative controllability package, now constructed. -/
def physicalLocalSteering : LocalSteering :=
  let r := uniform_steering.choose
  let K := uniform_steering.choose_spec.choose
  let h := uniform_steering.choose_spec.choose_spec
  { radius := r
    radius_pos := h.1
    K := K
    K_pos := h.2.1
    connect := h.2.2 }

end CZExposure.LocalSteeringConstruction
