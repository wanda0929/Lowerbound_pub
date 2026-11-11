module

public import RequestProject.AppendixE.StationaryGram

/-! Embed stationary matrices into the fixed degree-bounded normal face
column. Both conjugate charge sectors are retained; selecting one orbit
representative and proving the exact quotient identity remain separate. -/

@[expose] public section
noncomputable section
namespace CZExposure.FaceGram
open MvPolynomial QuotientNormalForm SymmetryGram
open scoped Matrix ComplexOrder

def inclusion {s t : Finset (Fin 11 →₀ ℕ)} : Matrix s t ℝ :=
  fun i j => if i.val = j.val then 1 else 0

def pad {s t : Finset (Fin 11 →₀ ℕ)} (B : Matrix s s ℝ) : Matrix t t ℝ :=
  (inclusion (s := s) (t := t))ᴴ * B * inclusion (s := s) (t := t)

theorem pad_posSemidef {s t : Finset (Fin 11 →₀ ℕ)} {B : Matrix s s ℝ}
    (hB : B.PosSemidef) : (pad (t := t) B).PosSemidef :=
  hB.conjTranspose_mul_mul_same inclusion

theorem pad_blocks {s t : Finset (Fin 11 →₀ ℕ)} (B : Matrix s s ℝ)
    (hb : ∀ i j : s, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) :
    ∀ i j : t, monomialCharge i.val ≠ monomialCharge j.val → pad B i j = 0 := by
  intro i j hij
  simp only [pad, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases hli : l.val = i.val
  · by_cases hkj : k.val = j.val
    · simp [inclusion, hli, hkj, hb l k (by simpa [hli, hkj] using hij)]
    · simp [inclusion, hkj]
  · simp [inclusion, hli]

private theorem value_dot {ν : Type*} [Fintype ν] (Q : Matrix ν ν ℂ) (w : ν → ℂ) :
    value Q w = star w ⬝ᵥ (Q *ᵥ w) := by
  simp [value, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem value_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix ι κ ℂ) (B : Matrix ι ι ℂ) (v : κ → ℂ) :
    value (Dᴴ * B * D) v = value B (D *ᵥ v) := by
  rw [value_dot, value_dot]
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem pad_value {s t : Finset (Fin 11 →₀ ℕ)} (hs : s ⊆ t) (B : Matrix s s ℝ)
    (v : t → ℂ) : value (fun i j => (pad B i j : ℂ)) v =
      value (fun i j => (B i j : ℂ)) (fun i => v ⟨i.val, hs i.property⟩) := by
  let D : Matrix s t ℂ := fun i j => if i.val = j.val then 1 else 0
  have hm : (fun i j => (pad B i j : ℂ)) = Dᴴ * (B.map Complex.ofReal) * D := by
    ext i j
    simp [pad, inclusion, D, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, apply_ite]
  have hd : D *ᵥ v = fun i : s => v ⟨i.val, hs i.property⟩ := by
    funext i
    change (∑ j : t, (if i.val = j.val then (1 : ℂ) else 0) * v j) = _
    rw [Finset.sum_eq_single ⟨i.val, hs i.property⟩]
    · simp
    · intro j _ hji
      have hne : i.val ≠ j.val := by
        intro h
        apply hji
        exact Subtype.ext h.symm
      simp [hne]
    · simp
  rw [hm, value_congruence, hd]
  rfl

/-- Fixed face-column matrix for every stationary certificate, at unchanged
degree. Equality is on the physical domain, not yet in the quotient ring. -/
theorem stationary_face_matrix {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ B : Matrix (NormalFaceBasis.basis d) (NormalFaceBasis.basis d) ℝ,
      B.PosSemidef ∧
      (∀ i j, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0) ∧
      ∀ (ξ : ℝ) (x : State), x ∈ Xset → ∀ u : ℂ, ‖u‖ = 1 →
        value (fun i j => (B i j : ℂ))
          (fun i => rephaser (decide (Odd (i.val 1 + i.val 2))) *
            eval (mixedPoint ξ x u) (term i.val 1)) =
          (eval (pt ξ x u) (cpoly + lieDeriv W) : ℂ) := by
  obtain ⟨s, B, hs, hB, hb, hv⟩ := StationaryGram.stationary_face_submatrix hW
  refine ⟨pad B, pad_posSemidef hB, pad_blocks B hb, ?_⟩
  intro ξ x hx u hu
  rw [pad_value hs]
  exact hv ξ x hx u hu

end CZExposure.FaceGram
