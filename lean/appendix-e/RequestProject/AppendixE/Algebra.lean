module
public import RequestProject.AppendixE.Hierarchy

/-! Algebraic helper lemmas for the SOS hierarchies. -/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial

theorem IsSOS.mono {σ : Type*} {d e : ℕ} {p : MvPolynomial σ ℝ} (h : IsSOS d p) (hde : d ≤ e) :
    IsSOS e p := by
  obtain ⟨n, f, hf, rfl⟩ := h
  exact ⟨n, f, fun l => (hf l).trans hde, rfl⟩

theorem IsSOS.zero {σ : Type*} (d : ℕ) : IsSOS d (0 : MvPolynomial σ ℝ) :=
  ⟨0, Fin.elim0, fun l => l.elim0, by simp⟩

/-- The exposure rate is itself a sum of four squares of linear forms. -/
theorem cpoly_eq_sos : cpoly = (C (Real.sqrt 2 / 2) * xs 2) ^ 2 + (C (Real.sqrt 2 / 2) * xs 3) ^ 2 +
    (C (1 / 2) * xs 6) ^ 2 + (C (1 / 2) * xs 7) ^ 2 := by
  have h : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [cpoly, mul_pow, ← C_pow, h]
  have h2 : (C (1 / 2 : ℝ) : Poly) = C (1 / 4) * 2 := by
    rw [show (2 : Poly) = C 2 from rfl, ← C_mul]; norm_num
  have h3 : (C ((1 / 2 : ℝ) ^ 2) : Poly) = C (1 / 4) := by norm_num
  rw [h2, h3]; ring

theorem cpoly_isSOS {d : ℕ} (hd : 1 ≤ d) : IsSOS d cpoly := by
  refine ⟨4, ![C (Real.sqrt 2 / 2) * xs 2, C (Real.sqrt 2 / 2) * xs 3, C (1 / 2) * xs 6,
    C (1 / 2) * xs 7], ?_, ?_⟩
  · intro l
    fin_cases l <;> simp only [Fin.isValue] <;>
      exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X, hd])
  · rw [cpoly_eq_sos]; simp [Fin.sum_univ_four]

theorem lieDeriv_zero : lieDeriv 0 = 0 := by simp [lieDeriv, ofState]

theorem pderiv_none_rename_some (W : StatePoly) : pderiv none (rename some W : CellPoly) = 0 := by
  induction W using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, pderiv_X]

theorem ofCell_rename_some (W : StatePoly) : ofCell (rename some W) = ofState W := by
  simp only [ofCell, ofState, rename_rename]; rfl

/-- A cell-independent certificate `W_j(ξ, x) = W(x)` has cell drift equal to the stationary
drift: `L_j W_j = f_u W`. -/
theorem cellOp_rename_some (κ : ℝ) (W : StatePoly) : cellOp κ (rename some W) = lieDeriv W := by
  simp only [cellOp, lieDeriv, pderiv_rename (Option.some_injective _), ofCell_rename_some,
    pderiv_none_rename_some]
  simp [ofCell]

theorem atXi_rename_some (t : ℝ) (W : StatePoly) : atXi t (rename some W) = W := by
  rw [atXi, aeval_rename]
  have : ((fun o : Option (Fin 8) => o.elim (C t) X) ∘ some) = (X : Fin 8 → StatePoly) := rfl
  rw [this, aeval_X_left_apply]

theorem evalCell_rename_some (ξ : ℝ) (x : State) (W : StatePoly) :
    evalCell ξ x (rename some W) = eval x W := by
  simp [evalCell, eval_rename]; rfl

theorem StationaryFeasible.mono {d : ℕ} {W : StatePoly} (h : StationaryFeasible d W) :
    StationaryFeasible (d + 1) W := by
  obtain ⟨h1, h2, h3, σ, hσ, h4⟩ := h
  exact ⟨h1.trans (by omega), h2, h3, σ, hσ.mono (by omega), h4⟩

theorem SplitFeasible.mono {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (h : SplitFeasible P U d W) : SplitFeasible P U (d + 1) W := by
  intro j hj
  obtain ⟨h1, h2, ⟨σ₀, σ₁, hσ₀, hσ₁, h3⟩, h4, h5⟩ := h j hj
  refine ⟨h1.trans (by omega), h2, ⟨σ₀, σ₁, hσ₀.mono (by omega), hσ₁.mono (by omega), h3⟩,
    fun hj' => ?_, h5⟩
  obtain ⟨σ, hσ, h6⟩ := h4 hj'
  exact ⟨σ, hσ.mono (by omega), h6⟩

theorem stationaryFeasible_zero {d : ℕ} (hd : 1 ≤ d) : StationaryFeasible d 0 := by
  refine ⟨by simp, fun x θ α => by simp, fun x _ => by simp, cpoly, cpoly_isSOS hd, ?_⟩
  simp [lieDeriv_zero]

/-- Embedding of the stationary program into the partitioned program (Appendix E 4):
`W_j(ξ, x) = W(x)` in every cell. -/
theorem StationaryFeasible.toSplit {d : ℕ} {W : StatePoly} (h : StationaryFeasible d W)
    (P : ExposurePartition) (U : ℝ) : SplitFeasible P U d (fun _ => rename some W) := by
  obtain ⟨h1, h2, h3, σ, hσ, h4⟩ := h
  intro j _
  refine ⟨(totalDegree_rename_le _ _).trans h1, fun ξ => ?_, ⟨σ, 0, hσ, IsSOS.zero _, ?_⟩,
    fun _ => ⟨0, IsSOS.zero _, ?_⟩, fun ξ _ x hx => ?_⟩
  · simpa only [evalCell_rename_some] using h2
  · simpa [cellOp_rename_some] using h4
  · simp [atXi_rename_some]
  · rw [evalCell_rename_some]; exact h3 x hx

end CZExposure
