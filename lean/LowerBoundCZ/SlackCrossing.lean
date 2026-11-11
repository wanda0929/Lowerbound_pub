import LowerBoundCZ.SlackAllocation

/-! Physical crossings and interface credits for the pinned five-cell model.
Only finite algebraic checks, never crossing existence or accumulated slack,
are certificate inputs. -/
noncomputable section
namespace LowerBoundCZ.Certification.Slack
open CZExposure MvPolynomial QuotientNormalForm QuotientCertificate Set

def interfaceSlack (V : ℕ → CellPoly) (j : ℕ) (x : State) : ℝ :=
  evalCell 1 x (V j) - evalCell 0 x (V (j+1))

/-- The sign agrees with V=-W and with `slack_telescope`. -/
def interfacePolynomial (V : ℕ → CellPoly) (j : ℕ) : MixedPoly :=
  embed (ofState (atXi 1 (V j) - atXi 0 (V (j+1))))

theorem eval_interfacePolynomial (V : ℕ → CellPoly) (j : ℕ)
    (ξ : ℝ) (x : State) (u : ℂ) :
    (eval (mixedPoint ξ x u) (interfacePolynomial V j)).re = interfaceSlack V j x := by
  simp only [interfacePolynomial, ResidualSymmetry.eval_embed, Complex.ofReal_re,
    eval_pt_ofState, map_sub, eval_atXi, interfaceSlack]

/-- Finite interface data and checks. For the population checker, encode each
block's combined diagonal allocation as ONE R with weight one; do not assume
separate per-projection budgets. Include unused original blocks as well.
The dummy first tensor coordinate may have degree zero. -/
structure InterfaceCertificate (V : ℕ → CellPoly) (j : ℕ) (κ : ℚ) where
  blockCount : ℕ
  blocks : Fin blockCount → AllocatedBlock
  degree : Fin 3 → ℕ
  coeff : ((i : Fin 3) → Fin (degree i+1)) → ℚ
  coord : Fin 3 → MixedPoly
  matrices : ∀ b, (blocks b).Checks
  source : interfacePolynomial V j - ∑ b, (blocks b).original ∈ relations
  residual : (∑ b, (blocks b).allocated) - C (κ : ℂ) -
    tensorMixed degree coeff coord ∈ relations
  nonneg : ∀ k, 0 ≤ coeff k

/-- Domain hypotheses specify the population box, not a physical slack bound. -/
theorem InterfaceCertificate.credit {V : ℕ → CellPoly} {j : ℕ} {κ : ℚ}
    (c : InterfaceCertificate V j κ)
    {x : State} (hx : x ∈ Xset) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (he : ∀ i, eval (mixedPoint 0 x 1) (c.coord i) = (t i : ℂ)) :
    (κ : ℝ) ≤ interfaceSlack V j x := by
  have h := allocation_local_slack c.blocks c.matrices (interfacePolynomial V j) (C (κ : ℂ))
    c.source c.degree c.coeff c.nonneg c.coord c.residual (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    hx (by simp : ‖(1 : ℂ)‖ = 1) t ht he
  simpa only [eval_C, Complex.ratCast_re, eval_interfacePolynomial] using h

/-- Ordered visits to all four internal knots; the fifth cell stops at the
actual endpoint, not at the upper exposure ceiling. -/
structure Crossings (γ : ActivePulse) where
  time : ℕ → ℝ
  start : time 0 = 0
  finish : time 5 = γ.S
  mem : ∀ k ≤ 5, time k ∈ Icc 0 γ.S
  ordered : ∀ k < 5, time k < time (k+1)
  level : ∀ j < 4, γ.cumI (time (j+1)) =
    Pinned.order7.ceiling * Pinned.partition.a (j+1)

theorem cumI_lt_time_lt (γ : ActivePulse) {a b : ℝ}
    (ha : a ∈ Icc 0 γ.S) (hb : b ∈ Icc 0 γ.S)
    (h : γ.cumI a < γ.cumI b) : a < b := by
  by_contra hn
  exact (not_lt_of_ge (γ.cumI_mono hb.1 (le_of_not_gt hn) ha.2)) h

/-- Even with zero-cost stalls, every pulse above the base bound crosses all
four knots, in order. No inverse of cumulative exposure is used. -/
theorem crossings_exist (γ : ActivePulse) (hL : (5861/2000 : ℝ) ≤ γ.exposure) :
    Nonempty (Crossings γ) := by
  classical
  have hit (j : Fin 4) : ∃ t ∈ Icc 0 γ.S,
      γ.cumI t = Pinned.order7.ceiling * Pinned.partition.a (j.val+1) := by
    apply intermediate_value_Icc γ.S_nonneg γ.continuousOn_cumI
    rw [γ.cumI_zero, γ.cumI_S]
    fin_cases j <;> norm_num [Pinned.order7, Pinned.partition] <;> linarith
  choose t ht he using hit
  let s : ℕ → ℝ := fun k => match k with
    | 0 => 0 | 1 => t 0 | 2 => t 1 | 3 => t 2 | 4 => t 3 | _ => γ.S
  have hm : ∀ k ≤ 5, s k ∈ Icc 0 γ.S := by
    intro k hk
    interval_cases k
    · exact ⟨le_rfl, γ.S_nonneg⟩
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · exact ht 3
    · exact ⟨γ.S_nonneg, le_rfl⟩
  have hl : ∀ j < 4, γ.cumI (s (j+1)) =
      Pinned.order7.ceiling * Pinned.partition.a (j+1) := by
    intro j hj
    interval_cases j
    · exact he 0
    · exact he 1
    · exact he 2
    · exact he 3
  refine ⟨⟨s, rfl, rfl, hm, ?_, hl⟩⟩
  intro k hk
  apply cumI_lt_time_lt γ (hm k (by omega)) (hm (k+1) (by omega))
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  norm_num [Pinned.order7, Pinned.partition] at h0 h1 h2 h3
  interval_cases k <;> simp only [s, γ.cumI_zero, γ.cumI_S] <;> linarith

/-- The pinned base certificate discharges the exposure threshold; there is
no additional trajectory-level lower-bound assumption. -/
theorem crossings_exist_of_grams (A : GramBridge.Archive Pinned.order7)
    (h : GramBridge.MatrixChecks A) (γ : ActivePulse) : Nonempty (Crossings γ) := by
  have hl := (Pinned.order7_checks_of_grams A h).active_lower.trans
    (show activeCstar ≤ (γ.exposure : EReal) from iInf_le _ γ)
  apply crossings_exist γ
  exact EReal.coe_le_coe_iff.mp hl

theorem Crossings.coordinates {γ : ActivePulse} (s : Crossings γ)
    {j : ℕ} (hj : j < 4) :
    cellXi Pinned.partition Pinned.order7.ceiling γ j (s.time (j+1)) = 1 ∧
    cellXi Pinned.partition Pinned.order7.ceiling γ (j+1) (s.time (j+1)) = 0 := by
  have hU : Pinned.order7.ceiling ≠ 0 := by norm_num [Pinned.order7]
  have hw := Pinned.partition.width_pos (j := j) (by change j < 5; omega)
  unfold cellXi
  rw [s.level j hj, mul_div_cancel_left₀ _ hU]
  exact ⟨div_self (ne_of_gt hw), by simp⟩

/-- Each time interval stays in its cell. The last interval needs only the
candidate sublevel C≤U, and may end strictly before the last knot. -/
theorem Crossings.cell_domain {γ : ActivePulse} (s : Crossings γ)
    (hC : γ.exposure ≤ Pinned.order7.ceiling) {j : ℕ} (hj : j < 5)
    {t : ℝ} (ht : t ∈ Icc (s.time j) (s.time (j+1))) :
    cellXi Pinned.partition Pinned.order7.ceiling γ j t ∈ Icc (0 : ℝ) 1 := by
  have hU : 0 < Pinned.order7.ceiling := by norm_num [Pinned.order7]
  have hw := Pinned.partition.width_pos (j := j) (by exact hj)
  have hl : γ.cumI (s.time j) = Pinned.order7.ceiling * Pinned.partition.a j := by
    cases j with
    | zero => simp [s.start, γ.cumI_zero, Pinned.partition]
    | succ k => exact s.level k (by omega)
  have hr : γ.cumI (s.time (j+1)) ≤ Pinned.order7.ceiling * Pinned.partition.a (j+1) := by
    by_cases hk : j < 4
    · exact (s.level j hk).le
    · have h4 : j = 4 := by omega
      subst j
      simpa [s.finish, γ.cumI_S, Pinned.partition] using hC
  have hleft := γ.cumI_mono (s.mem j (by omega)).1 ht.1
    (ht.2.trans (s.mem (j+1) (by omega)).2)
  have hright := (γ.cumI_mono ((s.mem j (by omega)).1.trans ht.1) ht.2
    (s.mem (j+1) (by omega)).2).trans hr
  rw [hl] at hleft
  have hlo : Pinned.partition.a j ≤ γ.cumI t / Pinned.order7.ceiling :=
    (le_div_iff₀ hU).mpr (by nlinarith)
  have hhi : γ.cumI t / Pinned.order7.ceiling ≤ Pinned.partition.a (j+1) :=
    (div_le_iff₀ hU).mpr (by nlinarith)
  exact ⟨div_nonneg (sub_nonneg.mpr hlo) hw.le,
    (div_le_one hw).mpr (sub_le_sub_right hhi _)⟩

theorem Crossings.jump {γ : ActivePulse} (s : Crossings γ)
    (V : ℕ → CellPoly) {j : ℕ} (hj : j < 4) :
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ j (s.time (j+1)))
      (γ.traj (s.time (j+1))) (V j) -
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ (j+1) (s.time (j+1)))
      (γ.traj (s.time (j+1))) (V (j+1)) =
      interfaceSlack V j (γ.traj (s.time (j+1))) := by
  rw [(s.coordinates hj).1, (s.coordinates hj).2]
  rfl

/-- All four physical jumps enter the exact accounting once, with positive
sign. The final potential retains its actual local exposure coordinate. -/
theorem Crossings.telescope {γ : ActivePulse} (s : Crossings γ) (V : ℕ → CellPoly) :
    (∑ j ∈ Finset.range 5, ∫ t in s.time j..s.time (j+1),
      occupationSlack Pinned.partition Pinned.order7.ceiling V γ j t) +
    (∑ j ∈ Finset.range 4, interfaceSlack V j (γ.traj (s.time (j+1)))) +
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S) (V 4) -
    evalCell 0 (γ.traj 0) (V 0) = γ.exposure := by
  have h := slack_telescope Pinned.partition (U := Pinned.order7.ceiling)
    (by norm_num [Pinned.order7]) V γ s.time 4
    (by decide) s.mem (fun k hk => (s.ordered k (by omega)).le)
  dsimp only at h
  have hj : (∑ j ∈ Finset.range 4,
      (evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ j (s.time (j+1)))
        (γ.traj (s.time (j+1))) (V j) -
      evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ (j+1) (s.time (j+1)))
        (γ.traj (s.time (j+1))) (V (j+1)))) =
      ∑ j ∈ Finset.range 4, interfaceSlack V j (γ.traj (s.time (j+1))) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact s.jump V (Finset.mem_range.mp hj)
  rw [hj, s.start, s.finish, γ.cumI_zero, γ.cumI_S] at h
  simpa [cellXi, Pinned.partition, γ.cumI_zero] using h

/-- Specialize the finite certificate at the same state used by both cells.
The unit control 1 is only for evaluating the state-only identity, not an
assumption on the physical control at the crossing. -/
theorem Crossings.credit {γ : ActivePulse} (s : Crossings γ)
    {V : ℕ → CellPoly} {j : ℕ} (hj : j < 4) {κ : ℚ}
    (c : InterfaceCertificate V j κ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (he : ∀ i, eval (mixedPoint 0 (γ.traj (s.time (j+1))) 1) (c.coord i) = (t i : ℂ)) :
    (κ : ℝ) ≤ interfaceSlack V j (γ.traj (s.time (j+1))) := by
  apply c.credit ?_ t ht he
  rw [γ.traj_eq (s.mem (j+1) (by omega))]
  exact γ.x_mem _ (s.mem (j+1) (by omega))

/-- Four algebraic interface credits enter the physical total, without an
external hypothesis asserting their accumulated slack. Population-box
coverage and the fixed numerical instances are separate finite obligations. -/
theorem Crossings.credited_telescope {γ : ActivePulse} (s : Crossings γ)
    (V : ℕ → CellPoly) (κ : Fin 4 → ℚ)
    (cert : ∀ j : Fin 4, InterfaceCertificate V j.val (κ j))
    (t : Fin 4 → Fin 3 → ℝ) (ht : ∀ j i, t j i ∈ Icc (0 : ℝ) 1)
    (he : ∀ j i, eval (mixedPoint 0 (γ.traj (s.time (j.val+1))) 1)
      ((cert j).coord i) = (t j i : ℂ)) :
    (∑ j ∈ Finset.range 5, ∫ z in s.time j..s.time (j+1),
      occupationSlack Pinned.partition Pinned.order7.ceiling V γ j z) +
    (∑ j : Fin 4, (κ j : ℝ)) +
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S) (V 4) -
    evalCell 0 (γ.traj 0) (V 0) ≤ γ.exposure := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    s.credit j.isLt (cert j) (t j) (ht j) (he j))
  rw [Fin.sum_univ_eq_sum_range
    (fun j => interfaceSlack V j (γ.traj (s.time (j+1)))) 4] at hb
  linarith [s.telescope V]

end LowerBoundCZ.Certification.Slack
