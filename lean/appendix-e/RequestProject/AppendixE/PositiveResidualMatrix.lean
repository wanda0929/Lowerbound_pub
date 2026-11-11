module

public import RequestProject.AppendixE.ResidualFactors

/-!
# A positive polynomial matrix for the physical residual

Compactness is used only on normalized states and disk controls. The unused
cell coordinate is specialized to zero; no compactness in that coordinate
is assumed. The final identity remains exact in the ambient polynomial ring.
-/

@[expose] public section
noncomputable section

namespace CZExposure.PositiveResidualMatrix

open MvPolynomial Matrix PolynomialApproximation ResidualFactors MatrixCorrection

/-- Remove the auxiliary cell coordinate without changing state or control. -/
def freeze : Poly →ₐ[ℝ] Poly := aeval (fun v => match v with
  | .xi => 0
  | _ => X v)

theorem eval_freeze (p : Poly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ x u) (freeze p) = eval (pt 0 x u) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [freeze]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
      simp only [map_mul, hp]
      congr 1
      cases v <;> simp [freeze, pt]

theorem freeze_amplitudes (i : Fin 4) : freeze (amplitudes i) = amplitudes i := by
  fin_cases i <;> simp [amplitudes, freeze]

theorem freeze_residual (W : StatePoly) : freeze (cpoly + lieDeriv W) = cpoly + lieDeriv W := by
  apply MvPolynomial.funext
  intro y
  let x : State := fun i => y (.st i)
  let u : ℂ := ⟨y (.ctl 0), y (.ctl 1)⟩
  have hy : pt (y .xi) x u = y := by
    funext v
    cases v with
    | st i => rfl
    | xi => rfl
    | ctl i => fin_cases i <;> rfl
  rw [← hy, eval_freeze]
  simp only [map_add, eval_pt_cpoly, eval_pt_lieDeriv]

theorem freeze_quadratic (A : Matrix (Fin 4) (Fin 4) Poly) :
    freeze (amplitudes ⬝ᵥ (A *ᵥ amplitudes)) =
      amplitudes ⬝ᵥ (A.map freeze *ᵥ amplitudes) := by
  simp [dotProduct, mulVec, map_sum, map_mul, freeze_amplitudes]

def realAmplitudes (x : State) : Fin 4 → ℝ := ![x 2, x 3, x 6, x 7]

theorem eval_amplitudes (ξ : ℝ) (x : State) (u : ℂ) (i : Fin 4) :
    eval (pt ξ x u) (amplitudes i) = realAmplitudes x i := by
  fin_cases i <;> simp [amplitudes, realAmplitudes, pt]

theorem eval_quadratic (A : Matrix (Fin 4) (Fin 4) Poly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ x u) (amplitudes ⬝ᵥ (A *ᵥ amplitudes)) =
      realAmplitudes x ⬝ᵥ (A.map (eval (pt ξ x u)) *ᵥ realAmplitudes x) := by
  simp [dotProduct, mulVec, map_sum, map_mul, eval_amplitudes]

theorem cost_pos_of_amplitudes_ne_zero {x : State} (hx : realAmplitudes x ≠ 0) :
    0 < cost x := by
  by_contra h
  have hc : cost x = 0 := le_antisymm (le_of_not_gt h) (cost_nonneg x)
  obtain ⟨h2, h3, h6, h7⟩ := rcoord_sq_le x
  apply hx
  ext i
  fin_cases i
  · change x 2 = 0
    nlinarith
  · change x 3 = 0
    nlinarith
  · change x 6 = 0
    nlinarith
  · change x 7 = 0
    nlinarith

theorem continuous_pt_zero : Continuous (fun p : State × ℂ => pt 0 p.1 p.2) := by
  apply continuous_pi
  intro v
  cases v with
  | st i => exact (continuous_apply i).comp continuous_fst
  | xi => exact continuous_const
  | ctl i =>
      fin_cases i
      · exact Complex.continuous_re.comp continuous_snd
      · exact Complex.continuous_im.comp continuous_snd

theorem continuous_realAmplitudes : Continuous realAmplitudes := by
  apply continuous_pi
  intro i
  fin_cases i <;> exact continuous_apply _

theorem eval_corrected (A : Matrix (Fin 4) (Fin 4) Poly) (Λ ξ : ℝ) (x : State) (u : ℂ) :
    (corrected A amplitudes (C Λ)).map (eval (pt ξ x u)) =
      corrected (A.map (eval (pt ξ x u))) (realAmplitudes x) Λ := by
  ext i j
  by_cases hij : i = j <;>
    simp [corrected, correction, Matrix.map_apply, vecMulVec,
      dotProduct, map_sum, map_mul, eval_amplitudes, hij]

/-- A strictly cost-weighted residual admits a symmetric polynomial matrix
that is positive definite on every normalized state and every disk control.
The caller supplies no matrix, factorization, or compactness assumption. -/
theorem exists_positive_residual_matrix (P : ExposurePoly) (η α : ℝ) (hα : 0 < α)
    (hmargin : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      α * cost x ≤ eval (pt ξ x u) (cpoly + lieDeriv (strictPolynomial P η α))) :
    ∃ A : Matrix (Fin 4) (Fin 4) Poly, A.IsSymm ∧
      amplitudes ⬝ᵥ (A *ᵥ amplitudes) = cpoly + lieDeriv (strictPolynomial P η α) ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
        (A.map (eval (pt ξ x u))).PosDef) ∧
      (∀ x u ξ, A.map (eval (pt ξ x u)) = A.map (eval (pt 0 x u))) := by
  obtain ⟨A, hsym, hq, hface⟩ := exists_residual_matrix P η α
  let K := Xset ×ˢ Metric.closedBall (0 : ℂ) 1
  let a : State × ℂ → Matrix (Fin 4) (Fin 4) ℝ := fun p => A.map (eval (pt 0 p.1 p.2))
  let r : State × ℂ → Fin 4 → ℝ := fun p => realAmplitudes p.1
  have ha : Continuous a := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (MvPolynomial.continuous_eval (p := A i j)).comp continuous_pt_zero
  have hr : Continuous r := continuous_realAmplitudes.comp continuous_fst
  have hs : ∀ p ∈ K, (a p).IsHermitian := by
    intro p _
    simpa [a, Matrix.IsHermitian, conjTranspose] using hsym.map (eval (pt 0 p.1 p.2))
  have hf : ∀ p ∈ K, r p = 0 → (a p).PosDef := by
    rintro ⟨x, u⟩ _ hz
    have he : a (x, u) = diagonal costWeights := by
      ext i j
      exact hface (pt 0 x u) (fun k => by rw [eval_amplitudes]; exact congrFun hz k) i j
    rw [he]
    exact costDiagonal_posDef
  have hrad : ∀ p ∈ K, r p ≠ 0 → 0 < r p ⬝ᵥ (a p *ᵥ r p) := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩ hz
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    have hm := hmargin x hx u hu' 0
    have hpos := mul_pos hα (cost_pos_of_amplitudes_ne_zero hz)
    have he := congrArg (eval (pt 0 x u)) hq
    rw [eval_quadratic] at he
    exact lt_of_lt_of_le hpos (by simpa [a, r, ← he] using hm)
  obtain ⟨Λ, hΛ, hpos⟩ := exists_corrected_posDef
    (isCompact_Xset.prod (isCompact_closedBall (0 : ℂ) 1)) ha hr hs hf hrad
  let B := corrected A amplitudes (C Λ)
  refine ⟨B.map freeze, ?_, ?_, ?_, ?_⟩
  · exact (hsym.add ((correction_symmetric amplitudes).smul (C Λ))).map freeze
  · rw [← freeze_quadratic, corrected_residual, hq, freeze_residual]
  · intro x hx u hu ξ
    have hb : (B.map freeze).map (eval (pt ξ x u)) =
        corrected (a (x, u)) (r (x, u)) Λ := by
      ext i j
      change eval (pt ξ x u) (freeze (B i j)) = _
      rw [eval_freeze]
      exact congrFun (congrFun (eval_corrected A Λ 0 x u) i) j
    rw [hb]
    exact hpos (x, u) ⟨hx, by simpa using hu⟩
  · intro x u ξ
    ext i j
    exact (eval_freeze (B i j) ξ x u).trans (eval_freeze (B i j) 0 x u).symm

/-- The nearly optimal invariant candidate now carries its positive matrix.
Only the superposition input remains explicit.
This is not yet an SOS representation or finite-order feasibility. -/
theorem exists_positive_matrix_candidate_below_Cstar
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ (W : StatePoly) (A : Matrix (Fin 4) (Fin 4) Poly),
      IsGInvariant (fun x => eval x W) ∧ a < eval x0 W ∧
      (∀ x ∈ XCZ, eval x W = 0) ∧ A.IsSymm ∧
      amplitudes ⬝ᵥ (A *ᵥ amplitudes) = cpoly + lieDeriv W ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
        (A.map (eval (pt ξ x u))).PosDef) ∧
      (∀ x u ξ, A.map (eval (pt ξ x u)) = A.map (eval (pt 0 x u))) := by
  obtain ⟨P, η, α, _, hα, _, hv, hsym, hz, hr⟩ :=
    RotationAverage.exists_G_invariant_candidate_below_Cstar
      hSuperposition a ha
  obtain ⟨A, hA, hq, hp, hξ⟩ := exists_positive_residual_matrix P η α hα hr
  exact ⟨strictPolynomial P η α, A, hsym, hv, hz, hA, hq, hp, hξ⟩

end CZExposure.PositiveResidualMatrix
