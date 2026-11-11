module
public import RequestProject.AppendixE.Evaluation
public import RequestProject.AppendixE.Calculus

/-!
# Weak duality for the stationary and partitioned programs

Integrating the drift inequality along any successful pulse shows that every feasible
certificate bounds the exposure from below.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial MeasureTheory Set

/-- The trajectory extended to all times by its integral formula. -/
def Pulse.traj (γ : Pulse) (s : ℝ) : State :=
  fun i => x0 i + ∫ t in (0 : ℝ)..s, vf (γ.x t) (γ.u t) i

theorem Pulse.traj_eq (γ : Pulse) {s : ℝ} (hs : s ∈ Icc 0 γ.S) : γ.traj s = γ.x s :=
  funext fun i => (γ.ode s hs i).symm

theorem Pulse.traj_zero (γ : Pulse) : γ.traj 0 = x0 := by
  funext i; simp [Pulse.traj]

theorem Pulse.continuousOn_traj (γ : Pulse) (i : Fin 8) :
    ContinuousOn (fun s => γ.traj s i) (Icc 0 γ.S) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (γ.integrable i)
    (a := 0) left_mem_uIcc
  rw [uIcc_of_le γ.S_nonneg] at h
  exact continuousOn_const.add h

theorem cost_eq (x : State) : cost x = (2 * (x 2 ^ 2 + x 3 ^ 2) + (x 6 ^ 2 + x 7 ^ 2)) / 4 := by
  simp [cost, r1, r2, Complex.sq_norm, Complex.normSq_apply]; ring

theorem Pulse.continuousOn_cost_traj (γ : Pulse) :
    ContinuousOn (fun s => cost (γ.traj s)) (Icc 0 γ.S) := by
  simp only [cost_eq]
  have h := γ.continuousOn_traj
  exact ((((h 2).pow 2).add ((h 3).pow 2)).const_smul (2 : ℝ) |>.add
    (((h 6).pow 2).add ((h 7).pow 2))).div_const 4 |>.congr fun s _ => by simp [smul_eq_mul]

theorem Pulse.exposure_eq (γ : Pulse) :
    γ.exposure = ∫ s in (0 : ℝ)..γ.S, cost (γ.traj s) := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le γ.S_nonneg] at hs
  simp only [γ.traj_eq hs]

/-- Weak duality for the stationary program: a feasible certificate bounds the exposure of
every successful pulse from below. -/
theorem stationary_weak_duality {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W)
    (γ : Pulse) : eval x0 W ≤ γ.exposure := by
  obtain ⟨-, -, hterm, σ, hσ, hdrift⟩ := hW
  have hS := γ.S_nonneg
  have key := integral_le_eval_sub W (y := γ.traj) (c := x0)
    (g := fun i t => vf (γ.x t) (γ.u t) i) (a₀ := 0) (A := 0) (B := γ.S) (a := 0) (b := γ.S)
    (h := fun t => -cost (γ.traj t)) (fun s k => rfl) γ.integrable ⟨le_rfl, hS⟩ hS subset_rfl
    (γ.continuousOn_cost_traj.neg.intervalIntegrable_of_Icc hS) ?_
  · rw [intervalIntegral.integral_neg, ← γ.exposure_eq, γ.traj_zero,
      γ.traj_eq ⟨hS, le_rfl⟩] at key
    have := hterm _ γ.terminal
    linarith
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have h0 := eval_nonneg_of_sos_mod (ξ := 0) (γ.x_mem t ht) (γ.u_unit t ht) hσ hdrift
    rw [map_add, eval_pt_cpoly, eval_pt_lieDeriv] at h0
    beta_reduce
    rw [γ.traj_eq ht]
    linarith

theorem cost_nonneg (x : State) : 0 ≤ cost x := by
  rw [cost_eq]; positivity

theorem Pulse.exposure_nonneg (γ : Pulse) : 0 ≤ γ.exposure :=
  intervalIntegral.integral_nonneg γ.S_nonneg fun _ _ => cost_nonneg _

/-! ### The partitioned program -/

/-- The cumulative exposure `∫₀^s c(x(t)) dt`. -/
def Pulse.cumI (γ : Pulse) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, cost (γ.traj t)

/-- The local cell coordinate `ξ_j(s) = (X(s) - a_j)/w_j`, with `X(s) = (1/U) ∫₀^s c`. -/
def cellXi (P : ExposurePartition) (U : ℝ) (γ : Pulse) (j : ℕ) (s : ℝ) : ℝ :=
  (γ.cumI s / U - P.a j) / P.width j

theorem ExposurePartition.width_pos (P : ExposurePartition) {j : ℕ} (hj : j < P.J) :
    0 < P.width j := by
  unfold ExposurePartition.width; linarith [P.a_lt j hj]

theorem ExposurePartition.a_mono (P : ExposurePartition) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ P.J) :
    P.a i ≤ P.a k := by
  induction k, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (P.a_lt k (by omega)).le

theorem Pulse.intervalIntegrable_cost (γ : Pulse) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ γ.S) : IntervalIntegrable (fun t => cost (γ.traj t)) volume a b :=
  (γ.continuousOn_cost_traj.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

theorem Pulse.cumI_sub (γ : Pulse) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S) :
    γ.cumI b - γ.cumI a = ∫ t in a..b, cost (γ.traj t) := by
  unfold Pulse.cumI
  rw [sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals
    (γ.intervalIntegrable_cost le_rfl ha (hab.trans hb))
    (γ.intervalIntegrable_cost ha hab hb)]

theorem Pulse.cumI_mono (γ : Pulse) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S) :
    γ.cumI a ≤ γ.cumI b := by
  have := γ.cumI_sub ha hab hb
  have h2 : 0 ≤ ∫ t in a..b, cost (γ.traj t) :=
    intervalIntegral.integral_nonneg hab fun _ _ => cost_nonneg _
  linarith

theorem Pulse.continuousOn_cumI (γ : Pulse) : ContinuousOn γ.cumI (Icc 0 γ.S) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (γ.intervalIntegrable_cost le_rfl γ.S_nonneg le_rfl) (a := 0) left_mem_uIcc
  rwa [uIcc_of_le γ.S_nonneg] at h

theorem Pulse.cumI_zero (γ : Pulse) : γ.cumI 0 = 0 := by simp [Pulse.cumI]

theorem Pulse.cumI_S (γ : Pulse) : γ.cumI γ.S = γ.exposure := γ.exposure_eq.symm

theorem cellXi_eq (P : ExposurePartition) {U : ℝ} (hU : 0 < U) (γ : Pulse) {j : ℕ}
    (hj : j < P.J) (s : ℝ) :
    cellXi P U γ j s = -P.a j / P.width j + ∫ t in (0 : ℝ)..s, cost (γ.traj t) / (U * P.width j) := by
  have hw := P.width_pos hj
  rw [intervalIntegral.integral_div, cellXi, Pulse.cumI]
  field_simp
  ring

/-- Integration across one cell needs only the pointwise drift inequality. -/
theorem cell_step_of_nonneg {P : ExposurePartition} {U : ℝ} {W : ℕ → CellPoly}
    (hdrift : ∀ j < P.J, ∀ ξ ∈ Icc (0 : ℝ) 1, ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ = 1 →
      0 ≤ eval (pt ξ x u) (cpoly + cellOp (1 / (U * P.width j)) (W j)))
    (γ : Pulse) (hU : 0 < U) {j : ℕ} (hj : j < P.J) {s₁ s₂ : ℝ}
    (h0 : 0 ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ γ.S)
    (hξ : ∀ t ∈ Icc s₁ s₂, cellXi P U γ j t ∈ Icc (0 : ℝ) 1) :
    evalCell (cellXi P U γ j s₁) (γ.traj s₁) (W j) - ∫ t in s₁..s₂, cost (γ.traj t) ≤
      evalCell (cellXi P U γ j s₂) (γ.traj s₂) (W j) := by
  have hS := γ.S_nonneg
  have hw := P.width_pos hj
  set κ := 1 / (U * P.width j) with hκ
  have key := integral_le_eval_sub (W j)
    (y := fun s o => Option.elim o (cellXi P U γ j s) (γ.traj s))
    (c := fun o => Option.elim o (-P.a j / P.width j) x0)
    (g := fun o t => Option.elim o (cost (γ.traj t) / (U * P.width j))
      (fun i => vf (γ.x t) (γ.u t) i))
    (a₀ := 0) (A := 0) (B := γ.S) (a := s₁) (b := s₂)
    (h := fun t => -cost (γ.traj t)) ?_ ?_ ⟨le_rfl, hS⟩ h12 (Icc_subset_Icc h0 h2)
    (γ.intervalIntegrable_cost h0 h12 h2).neg ?_
  · rw [intervalIntegral.integral_neg] at key
    unfold evalCell
    linarith
  · intro s k
    cases k with
    | none => exact cellXi_eq P hU γ hj s
    | some i => rfl
  · intro k
    cases k with
    | none => exact (γ.intervalIntegrable_cost le_rfl hS le_rfl).div_const _
    | some i => exact γ.integrable i
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have htS : t ∈ Icc 0 γ.S := ⟨h0.trans ht.1, ht.2.trans h2⟩
    have h0' := hdrift j hj _ (hξ t ht) _ (γ.x_mem t htS) _ (γ.u_unit t htS)
    rw [map_add, eval_pt_cpoly, eval_pt_cellOp] at h0'
    simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]
    rw [γ.traj_eq htS]
    unfold evalCell at h0'
    have hκ' : κ * cost (γ.x t) * eval (fun o => Option.elim o (cellXi P U γ j t) (γ.x t))
        (pderiv none (W j)) = eval (fun o => Option.elim o (cellXi P U γ j t) (γ.x t))
        (pderiv none (W j)) * (cost (γ.x t) / (U * P.width j)) := by
      rw [hκ]; ring
    linarith

/-- Pointwise drift, interface, and terminal inequalities imply weak duality,
independently of the chosen algebraic certificate representation. -/
theorem split_weak_duality_of_nonneg {P : ExposurePartition} {U : ℝ} {W : ℕ → CellPoly}
    (hdrift : ∀ j < P.J, ∀ ξ ∈ Icc (0 : ℝ) 1, ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ = 1 →
      0 ≤ eval (pt ξ x u) (cpoly + cellOp (1 / (U * P.width j)) (W j)))
    (hinter : ∀ j, j + 1 < P.J → ∀ x ∈ Xset,
      evalCell 1 x (W j) ≤ evalCell 0 x (W (j + 1)))
    (hterm : ∀ j < P.J, ∀ ξ ∈ Icc (0 : ℝ) 1, ∀ x ∈ XCZ, evalCell ξ x (W j) ≤ 0)
    (γ : Pulse) (hγ : γ.exposure < U) :
    evalCell 0 x0 (W 0) ≤ γ.exposure := by
  have hE0 := γ.exposure_nonneg
  have hU : 0 < U := by linarith
  have hS := γ.S_nonneg
  have hXS1 : γ.exposure / U < 1 := (div_lt_one hU).2 hγ
  have hXS0 : 0 ≤ γ.exposure / U := div_nonneg hE0 hU.le
  have hxi_mem : ∀ j < P.J, ∀ t, P.a j ≤ γ.cumI t / U → γ.cumI t / U ≤ P.a (j + 1) →
      cellXi P U γ j t ∈ Icc (0 : ℝ) 1 := by
    intro j hj t h1 h2
    have hw := P.width_pos hj
    constructor
    · exact div_nonneg (by linarith) hw.le
    · rw [cellXi, div_le_one hw]; unfold ExposurePartition.width; linarith
  have claim : ∀ j, j < P.J → P.a j ≤ γ.exposure / U → ∃ s ∈ Icc 0 γ.S, γ.cumI s / U = P.a j ∧
      evalCell 0 x0 (W 0) ≤ γ.cumI s + evalCell 0 (γ.traj s) (W j) := by
    intro j
    induction j with
    | zero =>
      intro _ _
      exact ⟨0, ⟨le_rfl, hS⟩, by simp [γ.cumI_zero, P.a_zero], by simp [γ.cumI_zero, γ.traj_zero]⟩
    | succ j ih =>
      intro hj hjX
      have hajj := P.a_lt j (by omega)
      obtain ⟨s, hs, hsa, hbound⟩ := ih (by omega) (hajj.le.trans hjX)
      have hcont : ContinuousOn (fun t => γ.cumI t / U) (Icc s γ.S) :=
        (γ.continuousOn_cumI.mono (Icc_subset_Icc hs.1 le_rfl)).div_const U
      have hmemI : P.a (j + 1) ∈ Icc (γ.cumI s / U) (γ.cumI γ.S / U) := by
        rw [hsa, γ.cumI_S]; exact ⟨hajj.le, hjX⟩
      obtain ⟨s', hs', hs'a⟩ := intermediate_value_Icc hs.2 hcont hmemI
      simp only at hs'a
      have hs'S : s' ∈ Icc 0 γ.S := ⟨hs.1.trans hs'.1, hs'.2⟩
      have hξmem : ∀ t ∈ Icc s s', cellXi P U γ j t ∈ Icc (0 : ℝ) 1 := by
        intro t ht
        have h1 := div_le_div_of_nonneg_right (γ.cumI_mono hs.1 ht.1 (ht.2.trans hs'.2)) hU.le
        have h2 := div_le_div_of_nonneg_right (γ.cumI_mono (hs.1.trans ht.1) ht.2 hs'.2) hU.le
        rw [hsa] at h1; rw [hs'a] at h2
        exact hxi_mem j (by omega) t h1 h2
      have hstep := cell_step_of_nonneg hdrift γ hU (j := j) (by omega) hs.1 hs'.1 hs'.2 hξmem
      have hξs : cellXi P U γ j s = 0 := by simp [cellXi, hsa]
      have hξs' : cellXi P U γ j s' = 1 := by
        rw [cellXi, hs'a]
        exact div_self (P.width_pos (by omega)).ne'
      rw [hξs, hξs'] at hstep
      have hint := hinter j hj (γ.traj s') (by rw [γ.traj_eq hs'S]; exact γ.x_mem s' hs'S)
      have hsub := γ.cumI_sub hs.1 hs'.1 hs'.2
      exact ⟨s', hs'S, hs'a, by linarith⟩
  have hjle : Nat.findGreatest (fun j => P.a j ≤ γ.exposure / U) (P.J - 1) ≤ P.J - 1 :=
    Nat.findGreatest_le _
  set jstar := Nat.findGreatest (fun j => P.a j ≤ γ.exposure / U) (P.J - 1) with hjstar
  have hjJ : jstar < P.J := by have := P.J_pos; omega
  have hjX : P.a jstar ≤ γ.exposure / U :=
    Nat.findGreatest_spec (P := fun j => P.a j ≤ γ.exposure / U) (m := 0) (Nat.zero_le _)
      (by show P.a 0 ≤ _; rw [P.a_zero]; exact hXS0)
  have hjX' : γ.exposure / U < P.a (jstar + 1) := by
    by_cases h : jstar + 1 ≤ P.J - 1
    · exact lt_of_not_ge (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h)
    · have : jstar + 1 = P.J := by omega
      rw [this, P.a_last]; exact hXS1
  obtain ⟨s, hs, hsa, hbound⟩ := claim jstar hjJ hjX
  have hξmem : ∀ t ∈ Icc s γ.S, cellXi P U γ jstar t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    have h1 := div_le_div_of_nonneg_right (γ.cumI_mono hs.1 ht.1 ht.2) hU.le
    have h2 := div_le_div_of_nonneg_right (γ.cumI_mono (hs.1.trans ht.1) ht.2 le_rfl) hU.le
    rw [hsa] at h1; rw [γ.cumI_S] at h2
    exact hxi_mem jstar hjJ t h1 (by linarith)
  have hstep := cell_step_of_nonneg hdrift γ hU hjJ hs.1 hs.2 le_rfl hξmem
  have hξs : cellXi P U γ jstar s = 0 := by simp [cellXi, hsa]
  rw [hξs] at hstep
  have hT := hterm jstar hjJ (cellXi P U γ jstar γ.S)
    (hxi_mem jstar hjJ γ.S (by rw [γ.cumI_S]; exact hjX) (by rw [γ.cumI_S]; exact hjX'.le))
    (γ.traj γ.S) (by rw [γ.traj_eq ⟨hS, le_rfl⟩]; exact γ.terminal)
  have hsub := γ.cumI_sub hs.1 hs.2 le_rfl
  rw [γ.cumI_S] at hsub
  linarith

theorem SplitFeasible.drift_nonneg {P : ExposurePartition} {U : ℝ} {d : ℕ}
    {W : ℕ → CellPoly} (hW : SplitFeasible P U d W) (j : ℕ) (hj : j < P.J)
    (ξ : ℝ) (hξ : ξ ∈ Icc (0 : ℝ) 1) (x : State) (hx : x ∈ Xset)
    (u : ℂ) (hu : ‖u‖ = 1) :
    0 ≤ eval (pt ξ x u) (cpoly + cellOp (1 / (U * P.width j)) (W j)) := by
  obtain ⟨σ₀, σ₁, hσ₀, hσ₁, he⟩ := (hW j hj).2.2.1
  have hv := eval_eq_zero_of_mem_normIdeal (ξ := ξ) hx hu he
  rw [map_sub, sub_eq_zero] at hv
  rw [hv]
  simp only [map_add, map_mul, map_sub, map_one, eval_pt_xi]
  exact add_nonneg (hσ₀.eval_nonneg _) (mul_nonneg
    (mul_nonneg hξ.1 (sub_nonneg.mpr hξ.2)) (hσ₁.eval_nonneg _))

/-- Integration of an abstract certificate across one cell. -/
theorem cell_step {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (hW : SplitFeasible P U d W) (γ : Pulse) (hU : 0 < U) {j : ℕ} (hj : j < P.J) {s₁ s₂ : ℝ}
    (h0 : 0 ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ γ.S)
    (hξ : ∀ t ∈ Icc s₁ s₂, cellXi P U γ j t ∈ Icc (0 : ℝ) 1) :
    evalCell (cellXi P U γ j s₁) (γ.traj s₁) (W j) - ∫ t in s₁..s₂, cost (γ.traj t) ≤
      evalCell (cellXi P U γ j s₂) (γ.traj s₂) (W j) :=
  cell_step_of_nonneg hW.drift_nonneg γ hU hj h0 h12 h2 hξ

/-- Weak duality for the abstract partitioned program below its exposure ceiling. -/
theorem split_weak_duality {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (hW : SplitFeasible P U d W) (γ : Pulse) (hγ : γ.exposure < U) :
    evalCell 0 x0 (W 0) ≤ γ.exposure := by
  refine split_weak_duality_of_nonneg hW.drift_nonneg ?_
    (fun j hj => (hW j hj).2.2.2.2) γ hγ
  intro j hj x hx
  obtain ⟨σ, hσ, hmem⟩ := (hW j (by omega)).2.2.2.1 hj
  have h1 := eval_eq_zero_of_mem_stateNormIdeal hx hmem
  rw [map_sub, map_sub, eval_atXi, eval_atXi] at h1
  have h2 := hσ.eval_nonneg x
  linarith

end CZExposure
