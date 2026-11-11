import LowerBoundCZ.CertificateContracts

/-! Exact slack accounting along integral-model trajectories. -/
noncomputable section
namespace LowerBoundCZ.Certification.Slack
open CZExposure MvPolynomial MeasureTheory Set

/-- Equality version of the polynomial chain rule. This is the analytic
identity needed for slack accounting, rather than just weak duality. -/
theorem polynomial_integral {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ)
    {y : ℝ → σ → ℝ} {c : σ → ℝ} {g : σ → ℝ → ℝ} {A B a b : ℝ}
    (hy : ∀ s k, y s k = c k + ∫ t in A..s, g k t)
    (hg : ∀ k, IntervalIntegrable (g k) volume A B)
    (ha : A ≤ a) (hab : a ≤ b) (hb : b ≤ B) :
    (∫ t in a..b, ∑ k, eval (y t) (pderiv k p) * g k t) =
      eval (y b) p - eval (y a) p := by
  have hAB : A ≤ B := ha.trans (hab.trans hb)
  have hyc : ContinuousOn y (Icc A B) := by
    apply continuousOn_pi.mpr
    intro k
    have h := intervalIntegral.continuousOn_primitive_interval' (hg k) (a := A) left_mem_uIcc
    rw [uIcc_of_le hAB] at h
    exact (continuousOn_const.add h).congr (fun s _ => hy s k)
  have hi : IntervalIntegrable
      (fun t => ∑ k, eval (y t) (pderiv k p) * g k t) volume a b := by
    have hk (k : σ) : IntervalIntegrable
        (fun t => eval (y t) (pderiv k p) * g k t) volume a b := by
      have hgk := (hg k).mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le hAB]
        exact Icc_subset_Icc ha hb)
      apply hgk.continuousOn_mul
      rw [uIcc_of_le hab]
      exact ((contDiff_eval (pderiv k p)).continuous.comp_continuousOn hyc).mono
        (Icc_subset_Icc ha hb)
    convert IntervalIntegrable.sum Finset.univ (fun k _ => hk k) using 1
    funext t
    simp only [Finset.sum_apply]
  have hlo := integral_le_eval_sub p hy hg ⟨le_rfl, hAB⟩ hab
    (Icc_subset_Icc ha hb) hi (Filter.Eventually.of_forall fun _ _ => le_rfl)
  have hhi := integral_le_eval_sub (-p) hy hg ⟨le_rfl, hAB⟩ hab
    (Icc_subset_Icc ha hb) hi.neg (Filter.Eventually.of_forall fun t _ => by
      simp only [map_neg, neg_mul, Finset.sum_neg_distrib]
      exact le_rfl)
  simp only [Pi.neg_apply] at hhi
  rw [intervalIntegral.integral_neg, map_neg, map_neg] at hhi
  linarith

/-- The actual polynomial cell slack, before any projections or profiles. -/
def occupationSlack (P : ExposurePartition) (U : ℝ) (V : ℕ → CellPoly)
    (γ : ActivePulse) (j : ℕ) (s : ℝ) : ℝ :=
  cost (γ.traj s) - eval (pt (cellXi P U γ j s) (γ.traj s) (γ.u s))
    (cellOp (1/(U * P.width j)) (V j))

theorem cell_potential_integral (P : ExposurePartition) {U : ℝ} (hU : 0 < U)
    (V : ℕ → CellPoly) (γ : ActivePulse) {j : ℕ} (hj : j < P.J)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S) :
    (∫ t in a..b, eval (pt (cellXi P U γ j t) (γ.traj t) (γ.u t))
      (cellOp (1/(U * P.width j)) (V j))) =
    evalCell (cellXi P U γ j b) (γ.traj b) (V j) -
      evalCell (cellXi P U γ j a) (γ.traj a) (V j) := by
  have h := polynomial_integral (V j)
    (y := fun s o => Option.elim o (cellXi P U γ j s) (γ.traj s))
    (c := fun o => Option.elim o (-P.a j / P.width j) x0)
    (g := fun o t => Option.elim o (cost (γ.traj t) / (U * P.width j))
      (fun i => vf (γ.x t) (γ.u t) i))
    (A := 0) (B := γ.S) (a := a) (b := b) ?_ ?_ ha hab hb
  · change _ = evalCell (cellXi P U γ j b) (γ.traj b) (V j) -
        evalCell (cellXi P U γ j a) (γ.traj a) (V j) at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htS : t ∈ Icc 0 γ.S := ⟨ha.trans ht.1, ht.2.trans hb⟩
    simp only [eval_pt_cellOp, Fintype.sum_option, Option.elim_none, Option.elim_some]
    rw [γ.traj_eq htS]
    unfold evalCell
    ring
  · intro s k
    cases k with
    | none => exact cellXi_eq P hU γ hj s
    | some i => rfl
  · intro k
    cases k with
    | none => exact (γ.intervalIntegrable_cost le_rfl γ.S_nonneg le_rfl).div_const _
    | some i => exact γ.integrable i

theorem cell_potential_intervalIntegrable (P : ExposurePartition) (U : ℝ)
    (V : ℕ → CellPoly) (γ : ActivePulse) (j : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S) :
    IntervalIntegrable (fun t => eval (pt (cellXi P U γ j t) (γ.traj t) (γ.u t))
      (cellOp (1/(U * P.width j)) (V j))) volume a b := by
  let y := fun s o => Option.elim o (cellXi P U γ j s) (γ.traj s)
  let g := fun o t => Option.elim o (cost (γ.traj t) / (U * P.width j))
    (fun i => vf (γ.x t) (γ.u t) i)
  have hy : ContinuousOn y (Icc a b) := by
    apply continuousOn_pi.mpr
    intro o
    cases o with
    | none => exact (((γ.continuousOn_cumI.div_const U).sub continuousOn_const).div_const
        (P.width j)).mono (Icc_subset_Icc ha hb)
    | some i => exact (γ.continuousOn_traj i).mono (Icc_subset_Icc ha hb)
  have hg (o : Option (Fin 8)) : IntervalIntegrable (g o) volume a b := by
    cases o with
    | none => exact (γ.intervalIntegrable_cost ha hab hb).div_const _
    | some i => exact (γ.integrable i).mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le γ.S_nonneg]
        exact Icc_subset_Icc ha hb)
  have hk (o : Option (Fin 8)) : IntervalIntegrable
      (fun t => eval (y t) (pderiv o (V j)) * g o t) volume a b := by
    apply (hg o).continuousOn_mul
    rw [uIcc_of_le hab]
    exact (contDiff_eval (pderiv o (V j))).continuous.comp_continuousOn hy
  have hi := IntervalIntegrable.sum Finset.univ (fun o _ => hk o)
  refine (intervalIntegrable_congr ?_).mp hi
  intro t ht
  rw [uIoc_of_le hab] at ht
  simp only [Finset.sum_apply, eval_pt_cellOp, Fintype.sum_option,
    y, g, Option.elim_none, Option.elim_some]
  rw [γ.traj_eq ⟨ha.trans ht.1.le, ht.2.trans hb⟩]
  unfold evalCell
  ring

/-- Exact occupation-slack identity; the integral is justified even for
measurable controls and intervals containing zero-cost stalls. -/
theorem occupation_integral (P : ExposurePartition) {U : ℝ} (hU : 0 < U)
    (V : ℕ → CellPoly) (γ : ActivePulse) {j : ℕ} (hj : j < P.J)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S) :
    (∫ t in a..b, occupationSlack P U V γ j t) =
      γ.cumI b - γ.cumI a -
        (evalCell (cellXi P U γ j b) (γ.traj b) (V j) -
          evalCell (cellXi P U γ j a) (γ.traj a) (V j)) := by
  unfold occupationSlack
  rw [intervalIntegral.integral_sub
    (γ.intervalIntegrable_cost ha hab hb)
    (cell_potential_intervalIntegrable P U V γ j ha hab hb),
    cell_potential_integral P hU V γ hj ha hab hb, γ.cumI_sub ha hab hb]

/-- Exact telescoping before specializing the crossing coordinates to 0 and
1. Adjacent cells share the same time, so each interface is counted once. -/
theorem slack_telescope (P : ExposurePartition) {U : ℝ} (hU : 0 < U)
    (V : ℕ → CellPoly) (γ : ActivePulse) (s : ℕ → ℝ) (n : ℕ)
    (hN : n < P.J) (hs : ∀ k ≤ n+1, s k ∈ Icc 0 γ.S)
    (ho : ∀ k ≤ n, s k ≤ s (k+1)) :
    let F := fun j t => evalCell (cellXi P U γ j t) (γ.traj t) (V j)
    (∑ j ∈ Finset.range (n+1), ∫ t in s j..s (j+1), occupationSlack P U V γ j t) +
      (∑ j ∈ Finset.range n, (F j (s (j+1)) - F (j+1) (s (j+1)))) +
      F n (s (n+1)) - F 0 (s 0) = γ.cumI (s (n+1)) - γ.cumI (s 0) := by
  dsimp only
  induction n with
  | zero =>
    simp only [Finset.sum_range_one, Finset.sum_range_zero, zero_add, add_zero]
    rw [occupation_integral P hU V γ hN (hs 0 (by omega)).1 (ho 0 (by omega))
      (hs 1 (by omega)).2]
    ring
  | succ n ih =>
    have hp := ih (by omega) (fun k hk => hs k (by omega)) (fun k hk => ho k (by omega))
    simp only [Finset.sum_range_succ] at hp ⊢
    rw [occupation_integral P hU V γ hN (hs (n+1) (by omega)).1
      (ho (n+1) (by omega)) (hs (n+2) (by omega)).2]
    linarith

/-- Exposure-coordinate substitution for a polynomial primitive. No inverse
of cumulative exposure and no strictly positive cost rate are required. -/
theorem profile_integral (γ : ActivePulse) (p : MvPolynomial Unit ℝ)
    {l w a b : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S)
    (hleft : γ.cumI a = l) (hright : γ.cumI b = l+w) :
    (∫ t in a..b, eval (fun _ : Unit => (γ.cumI t-l)/w) (pderiv () p) *
      cost (γ.traj t)) = w * (eval (fun _ => 1) p - eval (fun _ => 0) p) := by
  have h := polynomial_integral p
    (y := fun t (_ : Unit) => (γ.cumI t-l)/w)
    (c := fun _ => -l/w) (g := fun _ t => cost (γ.traj t)/w)
    (A := 0) (B := γ.S) (a := a) (b := b) ?_ ?_ ha hab hb
  · simp only [Fintype.sum_unique] at h
    have he (t : ℝ) :
        eval (fun _ : Unit => (γ.cumI t-l)/w) (pderiv () p) * (cost (γ.traj t)/w) =
        (eval (fun _ : Unit => (γ.cumI t-l)/w) (pderiv () p) * cost (γ.traj t))/w := by ring
    simp_rw [he] at h
    rw [intervalIntegral.integral_div, hleft, hright] at h
    simp only [add_sub_cancel_left, div_self hw.ne', sub_self, zero_div] at h
    exact (div_eq_iff hw.ne').mp h |>.trans (mul_comm _ _)
  · intro t k
    rw [intervalIntegral.integral_div]
    change (γ.cumI t-l)/w = -l/w + γ.cumI t/w
    ring
  · intro k
    exact (γ.intervalIntegrable_cost le_rfl γ.S_nonneg le_rfl).div_const _

/-- A pointwise algebraic profile certificate gives the credited physical
integral. The input is local; accumulated trajectory slack is not assumed. -/
theorem profile_credit (P : ExposurePartition) (U : ℝ) (V : ℕ → CellPoly)
    (γ : ActivePulse) (j : ℕ) (p : MvPolynomial Unit ℝ)
    {l w a b : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.S)
    (hleft : γ.cumI a = l) (hright : γ.cumI b = l+w)
    (hpoint : ∀ t ∈ Icc a b,
      eval (fun _ : Unit => (γ.cumI t-l)/w) (pderiv () p) * cost (γ.traj t) ≤
        occupationSlack P U V γ j t) :
    w * (eval (fun _ => 1) p - eval (fun _ => 0) p) ≤
      ∫ t in a..b, occupationSlack P U V γ j t := by
  rw [← profile_integral γ p hw ha hab hb hleft hright]
  have hy : ContinuousOn (fun t (_ : Unit) => (γ.cumI t-l)/w) (Icc a b) :=
    continuousOn_pi.mpr (fun _ =>
      ((γ.continuousOn_cumI.sub continuousOn_const).div_const w).mono (Icc_subset_Icc ha hb))
  have hd := ((contDiff_eval (pderiv () p)).continuous.comp_continuousOn hy).mul
    (γ.continuousOn_cost_traj.mono (Icc_subset_Icc ha hb))
  exact intervalIntegral.integral_mono_on hab (hd.intervalIntegrable_of_Icc hab)
    ((γ.intervalIntegrable_cost ha hab hb).sub
      (cell_potential_intervalIntegrable P U V γ j ha hab hb)) hpoint

/-- Every interval in the guaranteed exposure prefix is traversed in order,
even if cumulative exposure has constant stretches. -/
theorem exposure_crossings (γ : ActivePulse) {l r : ℝ}
    (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ γ.exposure) :
    ∃ a ∈ Icc 0 γ.S, ∃ b ∈ Icc a γ.S,
      a < b ∧ γ.cumI a = l ∧ γ.cumI b = r ∧
      ∀ t ∈ Icc a b, γ.cumI t ∈ Icc l r := by
  obtain ⟨a, ha, hleft⟩ := intermediate_value_Icc γ.S_nonneg γ.continuousOn_cumI
    (show l ∈ Icc (γ.cumI 0) (γ.cumI γ.S) by
      rw [γ.cumI_zero, γ.cumI_S]; exact ⟨hl, hlr.le.trans hr⟩)
  obtain ⟨b, hb, hright⟩ := intermediate_value_Icc ha.2
    (γ.continuousOn_cumI.mono (Icc_subset_Icc ha.1 le_rfl))
    (show r ∈ Icc (γ.cumI a) (γ.cumI γ.S) by
      rw [hleft, γ.cumI_S]; exact ⟨hlr.le, hr⟩)
  have hab : a < b := lt_of_le_of_ne hb.1 (by
    intro he; subst b; rw [hleft] at hright; exact hlr.ne hright)
  refine ⟨a, ha, b, hb, hab, hleft, hright, ?_⟩
  intro t ht
  constructor
  · rw [← hleft]
    exact γ.cumI_mono ha.1 ht.1 (ht.2.trans hb.2)
  · rw [← hright]
    exact γ.cumI_mono (ha.1.trans ht.1) ht.2 hb.2

end LowerBoundCZ.Certification.Slack
