module
public import RequestProject.AppendixE.MatrixSOSRemainder

/-! M5: the matrix Positivstellensatz, proved from M2--M4. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry
open MvPolynomial Matrix Set

variable {σ : Type} {k : ℕ}

/-- A continuous positive definite matrix on a compact set admits one
strictly positive scalar shift throughout the set. -/
theorem exists_uniform_matrix_shift {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (A : X → Matrix (Fin k) (Fin k) ℝ)
    (hA : Continuous A) (hp : ∀ x ∈ K, (A x).PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ K, (A x - μ • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef := by
  classical
  let S := K ×ˢ Metric.sphere (0 : Fin k → ℝ) 1
  let f : X × (Fin k → ℝ) → ℝ := fun p => p.2 ⬝ᵥ (A p.1 *ᵥ p.2)
  have hc : Continuous f := by dsimp [f, dotProduct, mulVec]; fun_prop
  have hs : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hf (p : X × (Fin k → ℝ)) (h : p ∈ S) : 0 < f p := by
    have hv : p.2 ≠ 0 := by
      intro he
      have hv := h.2
      simp [he] at hv
    simpa [f] using (hp p.1 h.1).dotProduct_mulVec_pos hv
  obtain ⟨η, hη, hmin⟩ : ∃ η : ℝ, 0 < η ∧ ∀ p ∈ S, η ≤ f p := by
    by_cases hn : S.Nonempty
    · obtain ⟨p, hpS, hmin⟩ := hs.exists_isMinOn hn hc.continuousOn
      exact ⟨f p, hf p hpS, hmin⟩
    · exact ⟨1, zero_lt_one, fun p hpS => False.elim (hn ⟨p,hpS⟩)⟩
  let μ := η / ((k:ℝ)+1)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have he : μ*((k:ℝ)+1) = η := by dsimp [μ]; field_simp
  refine ⟨μ, hμ, fun x hx => ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (hp x hx).isHermitian.sub (by simp [Matrix.IsHermitian])
  · intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : u ∈ Metric.sphere (0 : Fin k → ℝ) 1 := by
      simp [u, norm_smul, ne_of_gt hn]
    have hun : ‖u‖ = 1 := by simpa using hu
    have hsq : u ⬝ᵥ u ≤ (k:ℝ) := by
      calc
        _ ≤ ∑ _i : Fin k, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hi : |u i| ≤ 1 := by simpa [hun] using norm_le_pi_norm u i
          have hi' := abs_le.mp hi
          nlinarith
        _ = _ := by simp
    have hl := hmin (x,u) ⟨hx,hu⟩
    have hq : 0 ≤ u ⬝ᵥ ((A x - μ • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ u) := by
      simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      dsimp [f] at hl
      nlinarith
    have hscale : u ⬝ᵥ ((A x - μ • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ u) =
        ‖v‖⁻¹ ^ 2 * (v ⬝ᵥ ((A x - μ • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ v)) := by
      simp only [u, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [hscale] at hq
    simpa using (nonneg_of_mul_nonneg_right hq (sq_pos_of_pos (inv_pos.mpr hn)))

/-- The original matrix representation proposition, with no additional input. -/
theorem matrixPositivstellensatz : MatrixPositivstellensatz := by
  classical
  intro σ _ k _ I hI A hA hp
  let K := {x : σ → ℝ | ∀ p ∈ I, eval x p = 0}
  have hc : Continuous (fun x : σ → ℝ => A.map (eval x)) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact (A i j).continuous_eval
  obtain ⟨μ, hμ, hshift⟩ := exists_uniform_matrix_shift K (hI.isCompact_realZeroSet I)
    (fun x => A.map (eval x)) hc hp
  let B : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ) :=
    fun i j => A i j - C (if i=j then μ else 0)
  have hB (x : σ → ℝ) : B.map (eval x) = A.map (eval x) - μ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    by_cases hij : i=j <;> simp [B, hij]
  have hε : 0 < μ/(2*((k:ℝ)+1)) := by positivity
  obtain ⟨G, hG⟩ := hI.polynomial_matrix_gram_approximation I B
    (fun x hx => by rw [hB]; exact hshift x hx) hε
  let R : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ) :=
    fun i j => A i j - ∑ l, G l i * G l j
  have hR : R.IsSymm := by
    apply Matrix.ext; intro i j
    simp [R, hA.apply i j, mul_comm]
  obtain ⟨n, H, hH⟩ := hI.near_scalar_gram I R hR hμ (by
    intro x hx i j
    have hg := (hG x hx i j).2
    simpa [B, R, sub_right_comm] using hg)
  refine ⟨k+n, fun l i => Fin.addCases (fun a => G a i) (fun b => H b i) l, fun i j => ?_⟩
  simpa [Fin.sum_univ_add, R, sub_sub] using hH i j

end CZExposure.PolynomialGeometry
