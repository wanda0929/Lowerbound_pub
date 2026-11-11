module

public import RequestProject.AppendixE.SymmetryGram
public import RequestProject.AppendixE.NormalFaceBasis
public import Mathlib.Algebra.MvPolynomial.Funext

/-! Apply symmetry-separated matrix construction to stationary certificates.
This constructs degree-bounded normal columns and a real positive matrix on
the physical domain. Face compression and exact quotient identities remain
separate obligations. -/

@[expose] public section
noncomputable section
namespace CZExposure.StationaryGram
open MvPolynomial ComplexConjugate QuotientNormalForm SymmetryGram
open scoped Matrix ComplexOrder

theorem residual_rotate {W : StatePoly} (hW : IsGInvariant (fun x => eval x W))
    (ξ : ℝ) (x : State) (u : ℂ) (t : FaceRestriction.Parameters) :
    eval (pt ξ (opticalGauge (t.2 0) (qubitGauge (t.2 1) x))
      (FaceRestriction.phase (t.2 0) * u)) (cpoly + lieDeriv W) =
      eval (pt ξ x u) (cpoly + lieDeriv W) := by
  let g : RotationAction.Rotations := (Circle.exp (t.2 0), Circle.exp (t.2 1))
  have hp : RotationAction.rotatePoly g W = W := by
    apply MvPolynomial.funext
    intro y
    rw [RotationAction.eval_rotatePoly, RotationAction.rotate_exp]
    exact (hW _ (t.2 0) 0).1.trans (hW y 0 (t.2 1)).2.1
  have hd := RotationAction.rotatePoly_drift g W ξ x u
  rw [hp] at hd
  simp only [map_add, eval_pt_cpoly]
  rw [PolynomialSymmetry.cost_opticalGauge, PolynomialSymmetry.cost_qubitGauge]
  congr 1
  simpa [g, RotationAction.rotate_exp, Circle.coe_exp, FaceRestriction.phase] using hd.symm

theorem residual_reflection {W : StatePoly} (hW : IsGInvariant (fun x => eval x W))
    (ξ : ℝ) (x : State) (u : ℂ) :
    eval (pt ξ (reflection x) (-conj u)) (cpoly + lieDeriv W) =
      eval (pt ξ x u) (cpoly + lieDeriv W) := by
  have hp : PolynomialSymmetry.reflectPoly W = W := by
    apply MvPolynomial.funext
    intro y
    simpa using (hW y 0 0).2.2
  have hd := PolynomialSymmetry.reflectPoly_drift W ξ x u
  rw [hp] at hd
  simp only [map_add, eval_pt_cpoly, PolynomialSymmetry.cost_reflection, hd]

/-- A common finite column set, constructed from all normalized factors. -/
def columns {N : ℕ} (h : Fin N → Poly) : Finset (Fin 11 →₀ ℕ) :=
  Finset.univ.biUnion (fun l => (factorExpansion (h l)).support)

def coefficients {N : ℕ} (h : Fin N → Poly) : Matrix (Fin N) (columns h) ℂ :=
  fun l i => coeff i.val (factorExpansion (h l))

def columnValues {N : ℕ} (h : Fin N → Poly) (ξ : ℝ) (x : State) (u : ℂ) : columns h → ℂ :=
  fun i => eval (mixedPoint ξ x u) (term i.val 1)

theorem column_properties {N d : ℕ} (h : Fin N → Poly)
    (hd : ∀ l, (h l).totalDegree ≤ d) (i : columns h) :
    Normal i.val ∧ (term i.val 1).totalDegree ≤ d := by
  obtain ⟨l, _, hi⟩ := Finset.mem_biUnion.mp i.property
  refine ⟨factorExpansion_normal _ hi, ?_⟩
  apply (term_degree _ _).trans
  have hb := (le_totalDegree hi).trans ((factorExpansion_degree _).trans (hd l))
  simpa [Finsupp.sum_fintype] using hb

theorem expansion_sum {N : ℕ} (h : Fin N → Poly) (l : Fin N) (z : Fin 11 → ℂ) :
    (∑ i : columns h, coefficients h l i * eval z (term i.val 1)) =
      eval z (factorExpansion (h l)) := by
  classical
  rw [← support_sum_monomial_coeff (factorExpansion (h l))]
  simp only [map_sum, coefficients]
  rw [Finset.sum_coe_sort (columns h)
    (fun a : Fin 11 →₀ ℕ => coeff a (factorExpansion (h l)) * eval z (term a 1))]
  apply (Finset.sum_subset (s₁ := (factorExpansion (h l)).support)
    (s₂ := columns h) (by intro a ha; exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, ha⟩) ?_).symm.trans
  · apply Finset.sum_congr rfl
    intro i hi
    simp [term_eq_monomial, eval_monomial]
  · intro a ha hn
    simp [notMem_support_iff.mp hn]

theorem factor_matrix_represents {W : StatePoly} {N : ℕ} (h : Fin N → Poly)
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal)
    (ξ : ℝ) {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ = 1) :
    value ((coefficients h)ᴴ * coefficients h) (columnValues h ξ x u) =
      (eval (pt ξ x u) (cpoly + lieDeriv W) : ℂ) := by
  rw [factor_gram_value]
  simp only [columnValues, expansion_sum, eval_factorExpansion _ ξ hx hu, Complex.conj_ofReal]
  have he := eval_eq_zero_of_mem_normIdeal (ξ := ξ) hx hu hdrift
  simp only [map_sub, map_sum, map_pow, sub_eq_zero] at he
  rw [he]
  simp [pow_two]

theorem columnValues_rotate {N : ℕ} (h : Fin N → Poly) (ξ : ℝ) (x : State) (u : ℂ)
    (t : FaceRestriction.Parameters) :
    columnValues h ξ (opticalGauge (t.2 0) (qubitGauge (t.2 1) x))
      (FaceRestriction.phase (t.2 0) * u) =
      fun i => SymmetryGram.phase (monomialCharge i.val) t * columnValues h ξ x u i := by
  funext i
  simpa only [columnValues, rotatePoint_physical] using
    monomial_response i.val 1 (mixedPoint ξ x u) t

theorem columnValues_reflection {N : ℕ} (h : Fin N → Poly) (ξ : ℝ) (x : State) (u : ℂ) :
    columnValues h ξ (reflection x) (-conj u) = fun i =>
      (if decide (Odd (i.val 1 + i.val 2)) then -1 else 1) * conj (columnValues h ξ x u i) := by
  funext i
  unfold columnValues
  rw [monomial_reflection]
  rcases Nat.even_or_odd (i.val 1 + i.val 2) with he | ho
  · simp [he.neg_one_pow, show ¬Odd (i.val 1 + i.val 2) from Nat.not_odd_iff_even.mpr he]
  · simp [ho, ho.neg_one_pow]

/-- Every stationary certificate uses a subset of the fixed normal face
column. No nonvanishing monomial survives normalization and restriction. -/
theorem stationary_face_submatrix {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ (s : Finset (Fin 11 →₀ ℕ)) (B : Matrix s s ℝ),
      s ⊆ NormalFaceBasis.basis d ∧ B.PosSemidef ∧
      (∀ i j : s, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
      ∀ (ξ : ℝ) (x : State), x ∈ Xset → ∀ u : ℂ, ‖u‖ = 1 →
        value (fun i j => (B i j : ℂ))
          (fun i => rephaser (decide (Odd (i.val 1 + i.val 2))) *
            eval (mixedPoint ξ x u) (term i.val 1)) =
          (eval (pt ξ x u) (cpoly + lieDeriv W) : ℂ) := by
  classical
  obtain ⟨_, hsym, _, σ, ⟨N, h, hd, heq⟩, hdrift⟩ := hW
  rw [heq] at hdrift
  let Ω := ℝ × {x : State // x ∈ Xset} × {u : ℂ // ‖u‖ = 1}
  let v (z : Ω) := columnValues h z.1 z.2.1.val z.2.2.val
  let p (z : Ω) := eval (pt z.1 z.2.1.val z.2.2.val) (cpoly + lieDeriv W)
  let q (i : columns h) := monomialCharge i.val
  let odd (i : columns h) := decide (Odd (i.val 1 + i.val 2))
  let Q := (coefficients h)ᴴ * coefficients h
  have hr (ξ : ℝ) (x : State) (hx : x ∈ Xset) (u : ℂ) (hu : ‖u‖ = 1)
      (t : FaceRestriction.Parameters) :
      value Q (fun i => SymmetryGram.phase (q i) t * columnValues h ξ x u i) =
        (eval (pt ξ x u) (cpoly + lieDeriv W) : ℂ) := by
    rw [← columnValues_rotate]
    have hx' : opticalGauge (t.2 0) (qubitGauge (t.2 1) x) ∈ Xset := by
      simpa only [RotationAction.rotate_exp] using
        RotationAction.rotate_mem_Xset (Circle.exp (t.2 0), Circle.exp (t.2 1)) hx
    rw [factor_matrix_represents h hdrift ξ hx'
      (by simp [FaceRestriction.phase_norm, hu]), residual_rotate hsym]
  obtain ⟨B, hB, hb, hv⟩ := real_invariant_gram q odd Q
    (Matrix.posSemidef_conjTranspose_mul_self (coefficients h)) v p
    (fun z t => hr z.1 z.2.1.val z.2.1.property z.2.2.val z.2.2.property t)
    (by
      intro z t
      change value Q (fun i => SymmetryGram.phase (q i) t *
        ((if decide (Odd (i.val 1 + i.val 2)) then -1 else 1) *
          conj (columnValues h z.1 z.2.1.val z.2.2.val i))) = _
      have he (i : columns h) := congrFun
        (columnValues_reflection h z.1 z.2.1.val z.2.2.val) i
      simp_rw [← he]
      rw [hr z.1 _ (PolynomialSymmetry.reflection_mem_Xset z.2.1.property) _
        (by simpa using z.2.2.property), residual_reflection hsym])
  refine ⟨columns h, B, ?_, hB, hb, ?_⟩
  · intro a ha
    have hc := column_properties h hd ⟨a, ha⟩
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp ha
    exact NormalFaceBasis.mem_basis.mpr
      ⟨hc.1, NormalFaceBasis.stationary_factor_support hdrift l hl, hc.2⟩
  · intro ξ x hx u hu
    exact hv (ξ, ⟨x, hx⟩, ⟨u, hu⟩)

/-- The earlier degree-bounded matrix API, now obtained from the stronger
face-column inclusion theorem. -/
theorem stationary_matrix {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ (s : Finset (Fin 11 →₀ ℕ)) (B : Matrix s s ℝ),
      (∀ i : s, Normal i.val ∧ (term i.val 1).totalDegree ≤ d) ∧ B.PosSemidef ∧
      (∀ i j : s, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
      ∀ (ξ : ℝ) (x : State), x ∈ Xset → ∀ u : ℂ, ‖u‖ = 1 →
        value (fun i j => (B i j : ℂ))
          (fun i => rephaser (decide (Odd (i.val 1 + i.val 2))) *
            eval (mixedPoint ξ x u) (term i.val 1)) =
          (eval (pt ξ x u) (cpoly + lieDeriv W) : ℂ) := by
  obtain ⟨s, B, hs, hB, hb, hv⟩ := stationary_face_submatrix hW
  refine ⟨s, B, ?_, hB, hb, hv⟩
  intro i
  have h := NormalFaceBasis.mem_basis.mp (hs i.property)
  exact ⟨h.1, h.2.2⟩

end CZExposure.StationaryGram
