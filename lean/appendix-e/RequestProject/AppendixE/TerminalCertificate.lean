module

public import RequestProject.AppendixE.Algebra
public import RequestProject.AppendixE.FaceProjection

/-! The terminal part of the concrete stationary-to-partitioned embedding.
The CZ orbit restriction is a genuine univariate polynomial. For stationary
certificates its negative is a nonnegative constant square, at the same order.
This does not supply the charge-block or face-reduced drift Gram bases. -/

@[expose] public section
noncomputable section

namespace CZExposure.TerminalCertificate

open MvPolynomial Complex

def representative : State := mkState 1 0 (-1) 0

theorem representative_mem : representative ∈ XCZ := by
  norm_num [representative, XCZ, Xset]

theorem orbit_of_mem {x : State} (hx : x ∈ XCZ) :
    ∃ α : ℝ, qubitGauge α representative = x := by
  obtain ⟨hx, hr1, hr2, hg2⟩ := hx
  have hn : ‖g1 x‖ = 1 := by
    have h := hx.1
    rw [hr1] at h
    simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h
    nlinarith [norm_nonneg (g1 x)]
  obtain ⟨α, hα⟩ := Complex.norm_eq_one_iff (g1 x) |>.mp hn
  refine ⟨α, ?_⟩
  have htwo : Complex.exp (2 * (α : ℂ) * I) = (g1 x)^2 := by
    rw [show 2 * (α : ℂ) * I = (α : ℂ) * I + (α : ℂ) * I by ring,
      Complex.exp_add, hα, pow_two]
  apply state_ext <;> simp [qubitGauge, representative, hα, htwo, hr1, hr2, hg2]

theorem invariant_value {w : State → ℝ} (hw : IsGInvariant w)
    {x : State} (hx : x ∈ XCZ) : w x = w representative := by
  obtain ⟨α, rfl⟩ := orbit_of_mem hx
  exact (hw representative 0 α).2.1

abbrev UniPoly := MvPolynomial Unit ℝ

/-- Appendix C's τ: substitute (1,0,-1,0), leaving ξ free. -/
def terminalRestriction : CellPoly →ₐ[ℝ] UniPoly :=
  aeval (fun o => o.elim (X ()) (fun i => C (representative i)))

theorem eval_terminalRestriction (W : CellPoly) (ξ : ℝ) :
    eval (fun _ => ξ) (terminalRestriction W) = evalCell ξ representative W := by
  induction W using MvPolynomial.induction_on with
  | C a => simp [terminalRestriction, evalCell]
  | add p q hp hq => simp_all [evalCell]
  | mul_X p i hp =>
    cases i <;> simp_all [terminalRestriction, evalCell]

theorem terminalRestriction_on_orbit (W : CellPoly)
    (hW : ∀ ξ, IsGInvariant (fun x => evalCell ξ x W))
    (ξ : ℝ) {x : State} (hx : x ∈ XCZ) :
    eval (fun _ => ξ) (terminalRestriction W) = evalCell ξ x W := by
  rw [eval_terminalRestriction]
  exact (invariant_value (hW ξ) hx).symm

theorem terminalRestriction_stationary (W : StatePoly) :
    terminalRestriction (rename some W) = C (eval representative W) := by
  induction W using MvPolynomial.induction_on with
  | C a => simp [terminalRestriction]
  | add p q hp hq => simp_all
  | mul_X p i hp => simp_all [terminalRestriction]

/-- The univariate interval cone H_d([0,1]), over real coefficients. -/
def TerminalSOS (d : ℕ) (p : UniPoly) : Prop :=
  ∃ σ₀ σ₁, IsSOS d σ₀ ∧ IsSOS (d - 1) σ₁ ∧
    p = σ₀ + X () * (1 - X ()) * σ₁

theorem constant_square (d : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    IsSOS d (C a : UniPoly) := by
  refine ⟨1, fun _ => C (Real.sqrt a), ?_, ?_⟩
  · intro i
    simp
  · simp [← map_pow, Real.sq_sqrt ha]

/-- The terminal Gram block is the single nonnegative entry -W(x_CZ).
No degree increase and no univariate positivity theorem are needed. -/
theorem stationary_terminal {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    TerminalSOS d (-terminalRestriction (rename some W)) := by
  rw [terminalRestriction_stationary, ← map_neg]
  exact ⟨C (-eval representative W), 0,
    constant_square d (neg_nonneg.mpr (hW.2.2.1 representative representative_mem)),
    IsSOS.zero _, by simp⟩

/-- The actual monomial column (1, ξ, …, ξ^d) in Appendix C. -/
def monomialColumn (d : ℕ) (i : Fin (d + 1)) : UniPoly := X () ^ (i : ℕ)

/-- Put the terminal constant into the constant-monomial diagonal entry. -/
def constantGram (d : ℕ) (a : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then a else 0)

theorem constantGram_psd (d : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (constantGram d a).PosSemidef := by
  rw [constantGram, Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs <;> positivity

theorem constantGram_identity (d : ℕ) (a : ℝ) :
    (∑ i, ∑ j, monomialColumn d i * C (constantGram d a i j) * monomialColumn d j) =
      C a := by
  simp [constantGram, Matrix.diagonal, monomialColumn, apply_ite, ite_mul]

theorem stationary_terminal_gram {d : ℕ} {W : StatePoly}
    (hW : StationaryFeasible d W) :
    ∃ Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ, Q.PosSemidef ∧
      -terminalRestriction (rename some W) =
        ∑ i, ∑ j, monomialColumn d i * C (Q i j) * monomialColumn d j := by
  refine ⟨constantGram d (-eval representative W),
    constantGram_psd d (neg_nonneg.mpr (hW.2.2.1 representative representative_mem)), ?_⟩
  rw [constantGram_identity, terminalRestriction_stationary, map_neg]

theorem stationary_embedding {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W)
    (P : ExposurePartition) (U : ℝ) :
    SplitFeasible P U d (fun _ => rename some W) ∧
      TerminalSOS d (-terminalRestriction (rename some W)) :=
  ⟨hW.toSplit P U, stationary_terminal hW⟩

end CZExposure.TerminalCertificate
