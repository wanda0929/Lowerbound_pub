module

public import RequestProject.AppendixE.ResidualSymmetry
public import RequestProject.AppendixE.TerminalCertificate

/-! Concrete finite matrix feasibility for stationary certificates. This is
the stationary specialization, not the full partitioned program: the terminal
restriction is constant and needs no interval-multiplier block. -/

@[expose] public section
noncomputable section
namespace CZExposure.ConcreteStationary
open MvPolynomial QuotientNormalForm QuotientCertificate SymmetryGram
open ConjugateGram TerminalCertificate
open scoped Matrix ComplexOrder

/-- Finite retained charge blocks and the actual terminal monomial matrix.
Neither abstract feasibility nor a pointwise residual inequality is assumed. -/
def Feasible (d : ℕ) (W : StatePoly) : Prop :=
  W.totalDegree ≤ 2 * d - 1 ∧ IsGInvariant (fun x => eval x W) ∧
    ∃ Q : (q : retained d) → Matrix (sector d q.val) (sector d q.val) ℝ,
      ∃ T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
        (∀ q, (Q q).PosSemidef) ∧ T.PosSemidef ∧
        (embed (cpoly + lieDeriv W) -
          (∑ q : retained d, gram ((Q q).map Complex.ofReal) (fun i =>
            C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1))) ∈ relations ∧
        -terminalRestriction (rename some W) =
          ∑ i, ∑ j, monomialColumn d i * C (T i j) * monomialColumn d j

/-- Same W and same order: the objective W(x₀) is unchanged. This proves
inclusion into the concrete feasible set, not the converse inclusion. -/
theorem of_stationary {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    Feasible d W := by
  obtain ⟨Q, hQ, he⟩ := ResidualSymmetry.stationary_compressed_identity hW
  obtain ⟨T, hT, ht⟩ := stationary_terminal_gram hW
  refine ⟨hW.1, hW.2.1, (fun q => Q q.val), T, (fun q => hQ q.val), hT, ?_, ht⟩
  rw [Finset.sum_coe_sort (retained d) (fun q =>
    gram ((Q q).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1))]
  exact he

/-- A real positive matrix remains nonnegative on complex columns: its real
quadratic form is the sum of the forms on real and imaginary components. -/
theorem value_re_nonneg {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (v : ι → ℂ) : 0 ≤ (value (B.map Complex.ofReal) v).re := by
  have he : (value (B.map Complex.ofReal) v).re =
      (fun i => (v i).re) ⬝ᵥ (B *ᵥ (fun i => (v i).re)) +
      (fun i => (v i).im) ⬝ᵥ (B *ᵥ (fun i => (v i).im)) := by
    simp [value, dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im,
      Finset.mul_sum, Finset.sum_add_distrib, sub_eq_add_neg, mul_assoc]
  rw [he]
  exact add_nonneg (hB.dotProduct_mulVec_nonneg _) (hB.dotProduct_mulVec_nonneg _)

theorem Feasible.drift_nonneg {d : ℕ} {W : StatePoly} (hW : Feasible d W)
    (ξ : ℝ) {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ eval (pt ξ x u) (cpoly + lieDeriv W) := by
  obtain ⟨_, _, Q, T, hQ, _, he, _⟩ := hW
  have hv := eval_relations_zero he ξ hx hu
  simp only [map_sub, map_sum, ResidualSymmetry.eval_embed, eval_gram] at hv
  have hr := congrArg Complex.re hv
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.re_sum, Complex.zero_re,
    sub_eq_zero] at hr
  rw [hr]
  exact Finset.sum_nonneg (fun q _ => value_re_nonneg (hQ q) _)

theorem Feasible.terminal_nonpos {d : ℕ} {W : StatePoly} (hW : Feasible d W)
    {x : State} (hx : x ∈ XCZ) : eval x W ≤ 0 := by
  obtain ⟨_, hsym, Q, T, _, hT, _, ht⟩ := hW
  have he := congrArg (eval (fun _ : Unit => (1 : ℝ))) ht
  rw [terminalRestriction_stationary] at he
  simp [monomialColumn] at he
  have hp := hT.dotProduct_mulVec_nonneg (fun _ => 1)
  simp [dotProduct, Matrix.mulVec] at hp
  rw [invariant_value hsym hx]
  linarith

/-- Soundness for every successful pulse, without assuming abstract SOS
feasibility or any external completeness input. -/
theorem Feasible.weak_duality {d : ℕ} {W : StatePoly} (hW : Feasible d W)
    (γ : Pulse) : eval x0 W ≤ γ.exposure := by
  open MeasureTheory Set in
  have key := integral_le_eval_sub W (y := γ.traj) (c := x0)
    (g := fun i t => vf (γ.x t) (γ.u t) i) (a₀ := 0) (A := 0) (B := γ.S) (a := 0) (b := γ.S)
    (h := fun t => -cost (γ.traj t)) (fun s k => rfl) γ.integrable
    ⟨le_rfl, γ.S_nonneg⟩ γ.S_nonneg subset_rfl
    (γ.continuousOn_cost_traj.neg.intervalIntegrable_of_Icc γ.S_nonneg) (by
      refine Filter.Eventually.of_forall fun t ht => ?_
      have h0 := hW.drift_nonneg 0 (γ.x_mem t ht) (γ.u_unit t ht)
      rw [map_add, eval_pt_cpoly, eval_pt_lieDeriv] at h0
      beta_reduce
      rw [γ.traj_eq ht]
      linarith)
  rw [intervalIntegral.integral_neg, ← γ.exposure_eq, γ.traj_zero,
    γ.traj_eq ⟨γ.S_nonneg, le_rfl⟩] at key
  have ht := hW.terminal_nonpos γ.terminal
  linarith

/-- The certificate bounds the infimum over successful pulses; this does
not assert that the infimum is finite or attained. -/
theorem Feasible.le_Cstar {d : ℕ} {W : StatePoly} (hW : Feasible d W) :
    (eval x0 W : EReal) ≤ Cstar :=
  le_iInf fun γ => EReal.coe_le_coe_iff.2 (hW.weak_duality γ)

theorem sector_mono {d e : ℕ} (hde : d ≤ e) (q : Charge) : sector d q ⊆ sector e q := by
  intro a ha
  obtain ⟨ha, hq⟩ := Finset.mem_filter.mp ha
  obtain ⟨hn, hf, hd⟩ := NormalFaceBasis.mem_basis.mp ha
  exact Finset.mem_filter.mpr ⟨NormalFaceBasis.mem_basis.mpr ⟨hn, hf, hd.trans hde⟩, hq⟩

theorem retained_mono {d e : ℕ} (hde : d ≤ e) : retained d ⊆ retained e := by
  intro q hq
  obtain ⟨hq, hk⟩ := Finset.mem_filter.mp hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have hs := sector_mono hde (monomialCharge a)
    (Finset.mem_filter.mpr ⟨ha, rfl⟩)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp hs).1, rfl⟩, hk⟩

/-- Pad old charge blocks within the larger sectors and set newly retained
charges to zero. The terminal constant has the same sign at every order. -/
theorem Feasible.mono {d e : ℕ} {W : StatePoly} (hW : Feasible d W) (hde : d ≤ e) :
    Feasible e W := by
  classical
  have ht := hW.terminal_nonpos representative_mem
  obtain ⟨hd, hsym, Q, T, hQ, _, he, _⟩ := hW
  let R : (q : retained e) → Matrix (sector e q.val) (sector e q.val) ℝ := fun q =>
    if h : q.val ∈ retained d then FaceGram.pad (Q ⟨q.val, h⟩) else 0
  let f (q : Charge) : MixedPoly := if h : q ∈ retained d then
    gram ((Q ⟨q, h⟩).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) else 0
  have hsum : (∑ q : retained e, gram ((R q).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1)) =
      ∑ q : retained d, gram ((Q q).map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) := by
    calc
      _ = ∑ q : retained e, f q.val := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq : q.val ∈ retained d
        · simp only [R, f, dif_pos hq]
          exact ResidualSymmetry.pad_gram (sector_mono hde q.val) _ _
        · simp [R, f, hq, gram]
      _ = ∑ q ∈ retained e, f q := Finset.sum_coe_sort _ _
      _ = ∑ q ∈ retained d, f q :=
        (Finset.sum_subset (retained_mono hde) (by intro q _ hq; simp [f, hq])).symm
      _ = _ := by
        rw [← Finset.sum_coe_sort (retained d) f]
        apply Finset.sum_congr rfl
        intro q _
        simp [f, q.property]
  refine ⟨hd.trans (by omega), hsym, R, constantGram e (-eval representative W), ?_,
    constantGram_psd e (neg_nonneg.mpr ht), ?_, ?_⟩
  · intro q
    dsimp only [R]
    split
    · exact FaceGram.pad_posSemidef (hQ _)
    · exact Matrix.PosSemidef.zero
  · rw [hsum]
    exact he
  · rw [constantGram_identity, terminalRestriction_stationary, map_neg]

/-- Supremum of initial values over the concrete order-d certificates.
Extended real values permit an empty feasible set or an infinite optimum. -/
def optimum (d : ℕ) : EReal :=
  ⨆ (W : StatePoly) (_ : Feasible d W), (eval x0 W : EReal)

theorem Lunsplit_le_optimum (d : ℕ) : Lunsplit d ≤ optimum d :=
  iSup₂_le fun W hW => le_iSup₂_of_le
    (f := fun (W : StatePoly) (_ : Feasible d W) => (eval x0 W : EReal))
    W (of_stationary hW) le_rfl

theorem optimum_le_Cstar (d : ℕ) : optimum d ≤ Cstar :=
  iSup₂_le fun _ hW => hW.le_Cstar

theorem optimum_nonneg {d : ℕ} (hd : 1 ≤ d) : 0 ≤ optimum d :=
  (Lunsplit_nonneg hd).trans (Lunsplit_le_optimum d)

theorem optimum_mono : Monotone optimum := by
  intro d e hde
  exact iSup₂_le fun W hW => le_iSup₂_of_le
    (f := fun (W : StatePoly) (_ : Feasible e W) => (eval x0 W : EReal))
    W (hW.mono hde) le_rfl

/-- Conditional convergence by squeezing between the abstract stationary
optimum and the physical optimum. This argument needs neither reverse
conversion nor the separately proved nesting of concrete feasible sets. -/
theorem stationary_convergence
    (hSuperposition : EuclideanDirectedArcSuperposition) :
    Filter.Tendsto optimum Filter.atTop (nhds Cstar) := by
  have h := (stationary_completeness hSuperposition).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds
    Lunsplit_le_optimum optimum_le_Cstar

/-- Every positive-order concrete optimum is a finite real when a successful
pulse is supplied; no geometric or approximation input is needed. -/
theorem optimum_finite (γ : Pulse) {d : ℕ} (hd : 1 ≤ d) :
    optimum d ≠ ⊤ ∧ optimum d ≠ ⊥ :=
  ⟨ne_top_of_le_ne_top (Cstar_finite γ).1 (optimum_le_Cstar d),
    ne_bot_of_le_ne_bot (by simp) (optimum_nonneg hd)⟩

/-- At every sufficiently large order, the real optimum is within epsilon
of the finite physical infimum, from below. -/
theorem optimum_epsilon
    (hSuperposition : EuclideanDirectedArcSuperposition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D,
      0 ≤ Cstar.toReal - (optimum d).toReal ∧
        Cstar.toReal - (optimum d).toReal < ε := by
  obtain ⟨γ⟩ := nonempty_physical_pulse
  obtain ⟨D, W, hD, hW, hv⟩ :=
    polynomial_certificates_epsilon hSuperposition hε
  refine ⟨D, hD, fun d hDd => ?_⟩
  have hf := optimum_finite γ (hD.trans hDd)
  have hc := EReal.coe_toReal hf.1 hf.2
  have hu := optimum_le_Cstar d
  rw [← hc, ← coe_Cstar_toReal γ, EReal.coe_le_coe_iff] at hu
  have hl := (le_iSup₂ (f := fun (W : StatePoly) (_ : Feasible D W) =>
    (eval x0 W : EReal)) W (of_stationary hW)).trans (optimum_mono hDd)
  rw [← hc, EReal.coe_le_coe_iff] at hl
  constructor <;> linarith

end CZExposure.ConcreteStationary
