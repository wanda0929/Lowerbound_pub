module

public import RequestProject.AppendixE.PositiveResidualMatrix
public import RequestProject.AppendixE.MatrixSOSTheorem

/-! Proved matrix SOS representation and finite stationary feasibility.
The temporary equation ξ=0 makes the ambient ideal Archimedean. Polynomial
specialization removes that equation again before entering `StationaryFeasible`.
-/

@[expose] public section
noncomputable section

namespace CZExposure.SOSRepresentation

open MvPolynomial Matrix PolynomialGeometry PositiveResidualMatrix ResidualFactors

def variableEquiv : Var ≃ (Fin 8 ⊕ Fin 2) ⊕ Unit where
  toFun
    | .st i => .inl (.inl i)
    | .ctl i => .inl (.inr i)
    | .xi => .inr ()
  invFun
    | .inl (.inl i) => .st i
    | .inl (.inr i) => .ctl i
    | .inr _ => .xi
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with (i | i) | ⟨⟩ <;> rfl

local instance : Fintype Var := Fintype.ofEquiv _ variableEquiv.symm

theorem sum_variables (f : Var → Poly) :
    ∑ v, f v = (∑ i : Fin 8, f (.st i)) + (∑ i : Fin 2, f (.ctl i)) + f .xi := by
  rw [← variableEquiv.symm.sum_comp]
  simp [Fintype.sum_sum_type, variableEquiv]

def sliceIdeal : Ideal Poly := normIdeal ⊔ Ideal.span {X Var.xi}

theorem norm_generators :
    xs 0^2 + xs 1^2 + xs 2^2 + xs 3^2 - 1 ∈ normIdeal ∧
    xs 4^2 + xs 5^2 + xs 6^2 + xs 7^2 - 1 ∈ normIdeal ∧
    ua^2 + ub^2 - 1 ∈ normIdeal := by
  exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩

theorem slice_archimedean : IdealArchimedean sliceIdeal := by
  refine ⟨3, 0, 0, IsSOS.zero 0, ?_⟩
  obtain ⟨h1, h2, h3⟩ := norm_generators
  have hn := (le_sup_left : normIdeal ≤ sliceIdeal) (normIdeal.add_mem (normIdeal.add_mem h1 h2) h3)
  have hx : (X Var.xi : Poly)^2 ∈ sliceIdeal := by
    rw [pow_two]
    exact sliceIdeal.mul_mem_left _ ((le_sup_right : Ideal.span {X Var.xi} ≤ sliceIdeal)
      (Ideal.subset_span (by simp)))
  have h := sliceIdeal.neg_mem (sliceIdeal.add_mem hn hx)
  convert h using 1
  rw [sum_variables]
  norm_num [Fin.sum_univ_succ, Fin.succ, xs, show (C (3 : ℝ) : Poly) = 3 from map_ofNat C 3]
  ring!

theorem freeze_norm_generator {p : Poly}
    (hp : p ∈ ({xs 0^2 + xs 1^2 + xs 2^2 + xs 3^2 - 1,
      xs 4^2 + xs 5^2 + xs 6^2 + xs 7^2 - 1, ua^2 + ub^2 - 1} : Set Poly)) :
    freeze p ∈ normIdeal := by
  rcases hp with rfl | rfl | rfl
  all_goals simpa [freeze] using (Ideal.subset_span (by simp) :
    _ ∈ normIdeal)

theorem freeze_slice_mem {p : Poly} (hp : p ∈ sliceIdeal) : freeze p ∈ normIdeal := by
  have hle : sliceIdeal ≤ Ideal.comap freeze.toRingHom normIdeal := by
    apply sup_le
    · apply Ideal.span_le.mpr
      intro p hp
      exact freeze_norm_generator hp
    · apply Ideal.span_le.mpr
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      change freeze (X Var.xi) ∈ normIdeal
      simp [freeze]
  exact hle hp

theorem physical_point_of_zeros (y : Var → ℝ)
    (hy : ∀ p ∈ sliceIdeal, eval y p = 0) :
    ∃ (x : State) (u : ℂ), x ∈ Xset ∧ ‖u‖ ≤ 1 ∧ y = pt (y .xi) x u := by
  let x : State := fun i => y (.st i)
  let u : ℂ := ⟨y (.ctl 0), y (.ctl 1)⟩
  have he : y = pt (y .xi) x u := by
    ext v
    cases v with
    | st i => rfl
    | xi => rfl
    | ctl i => fin_cases i <;> rfl
  obtain ⟨h1, h2, h3⟩ := norm_generators
  have e1 := hy _ ((le_sup_left : normIdeal ≤ sliceIdeal) h1)
  have e2 := hy _ ((le_sup_left : normIdeal ≤ sliceIdeal) h2)
  have e3 := hy _ ((le_sup_left : normIdeal ≤ sliceIdeal) h3)
  simp only [map_sub, map_add, map_pow, eval_X, map_one] at e1 e2 e3
  refine ⟨x, u, ⟨?_, ?_⟩, ?_, he⟩
  · rw [norm_sq_g1_add]
    change y (.st 0)^2 + y (.st 1)^2 + y (.st 2)^2 + y (.st 3)^2 = 1
    linarith
  · rw [norm_sq_g2_add]
    change y (.st 4)^2 + y (.st 5)^2 + y (.st 6)^2 + y (.st 7)^2 = 1
    linarith
  · have hu : ‖u‖^2 = 1 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, u]
      nlinarith
    nlinarith [norm_nonneg u]

theorem gram_contraction {k m : ℕ} (I : Ideal Poly)
    (A : Matrix (Fin k) (Fin k) Poly) (H : Matrix (Fin m) (Fin k) Poly)
    (r : Fin k → Poly) (h : ∀ i j, A i j - ∑ l, H l i * H l j ∈ I) :
    r ⬝ᵥ (A *ᵥ r) - ∑ l, (∑ i, H l i * r i)^2 ∈ I := by
  have he : (∑ l, (∑ i, H l i * r i)^2) =
      ∑ i, ∑ j, r i * (∑ l, H l i * H l j) * r j := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  have hid : r ⬝ᵥ (A *ᵥ r) - ∑ i, ∑ j, r i * (∑ l, H l i * H l j) * r j =
      ∑ i, ∑ j, r i * (A i j - ∑ l, H l i * H l j) * r j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  exact I.sum_mem fun i _ => I.sum_mem fun j _ =>
    I.mul_mem_right _ (I.mul_mem_left _ (h i j))

theorem residual_squares
    (W : StatePoly) (A : Matrix (Fin 4) (Fin 4) Poly) (hA : A.IsSymm)
    (hq : amplitudes ⬝ᵥ (A *ᵥ amplitudes) = cpoly + lieDeriv W)
    (hp : ∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ ξ : ℝ,
      (A.map (eval (pt ξ x u))).PosDef) :
    ∃ (m : ℕ) (f : Fin m → Poly), cpoly + lieDeriv W - ∑ l, (f l)^2 ∈ normIdeal := by
  obtain ⟨m, H, hH⟩ := matrixPositivstellensatz Var 4 (by norm_num) sliceIdeal slice_archimedean A hA (by
    intro y hy
    obtain ⟨x, u, hx, hu, he⟩ := physical_point_of_zeros y hy
    rw [he]
    exact hp x hx u hu (y .xi))
  have hc := gram_contraction sliceIdeal A H amplitudes hH
  rw [hq] at hc
  have hf := freeze_slice_mem hc
  refine ⟨m, fun l => freeze (∑ i, H l i * amplitudes i), ?_⟩
  simpa only [map_sub, map_sum, map_pow, freeze_residual] using hf

/-- A finite family of polynomial squares always fits at some finite order.
No effective order estimate for the Positivstellensatz is asserted. -/
theorem finite_order (W : StatePoly) {m : ℕ} (f : Fin m → Poly) :
    ∃ d : ℕ, W.totalDegree ≤ 2 * d - 1 ∧ IsSOS d (∑ l, (f l)^2) := by
  let d := W.totalDegree + 1 + ∑ l, (f l).totalDegree
  refine ⟨d, ?_, m, f, ?_, rfl⟩
  · dsimp [d]
    omega
  · intro l
    have h := Finset.single_le_sum (fun i _ => Nat.zero_le (f i).totalDegree)
      (Finset.mem_univ l)
    dsimp [d]
    omega

theorem exists_stationary_feasible_below_Cstar
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ (d : ℕ) (W : StatePoly), StationaryFeasible d W ∧ a < eval x0 W := by
  obtain ⟨W, A, hG, hv, hz, hA, hq, hp, _⟩ :=
    exists_positive_matrix_candidate_below_Cstar hSuperposition a ha
  obtain ⟨m, f, hf⟩ := residual_squares W A hA hq hp
  obtain ⟨d, hd, hs⟩ := finite_order W f
  exact ⟨d, W, ⟨hd, hG, fun x hx => (hz x hx).le, _, hs, hf⟩, hv⟩

end CZExposure.SOSRepresentation
