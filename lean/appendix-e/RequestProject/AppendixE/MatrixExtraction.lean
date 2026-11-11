module

public import RequestProject.AppendixE.MatrixCorrection

/-!
# Extracting amplitude factors from a cubic ideal

The cube of the amplitude ideal consists of sums with at least three
amplitude factors. Two factors become the outer quadratic-form vectors;
the remaining factor makes every extracted matrix entry vanish on the face.
-/

@[expose] public section
noncomputable section

namespace CZExposure.MatrixExtraction

open Matrix
open scoped Pointwise

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R] [Algebra ℝ R]

def amplitudeIdeal (r : n → R) : Ideal R := Ideal.span (Set.range r)

omit [Fintype n] [DecidableEq n] [Algebra ℝ R] in
theorem amplitude_mem (r : n → R) (i : n) : r i ∈ amplitudeIdeal r :=
  Ideal.subset_span (Set.mem_range_self i)

omit [Fintype n] [DecidableEq n] [Algebra ℝ R] in
theorem amplitudeIdeal_cube (r : n → R) :
    amplitudeIdeal r ^ 3 = Ideal.span
      (Set.range (fun t : (n × n) × n => r t.1.1 * r t.1.2 * r t.2)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, amplitudeIdeal,
    Ideal.span_mul_span, Ideal.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ⟨b, ⟨i, rfl⟩, c, ⟨j, rfl⟩, rfl⟩, d, ⟨k, rfl⟩, rfl⟩
    exact ⟨((i, j), k), rfl⟩
  · rintro ⟨⟨⟨i, j⟩, k⟩, rfl⟩
    exact ⟨r i * r j, ⟨r i, ⟨i, rfl⟩, r j, ⟨j, rfl⟩, rfl⟩,
      r k, ⟨k, rfl⟩, rfl⟩

omit [DecidableEq n] [Algebra ℝ R] in
/-- Extract two factors, initially without imposing symmetry. -/
theorem exists_matrix_of_mem_cube (r : n → R) {p : R}
    (hp : p ∈ amplitudeIdeal r ^ 3) :
    ∃ B : Matrix n n R, (∀ i j, B i j ∈ amplitudeIdeal r) ∧
      r ⬝ᵥ (B *ᵥ r) = p := by
  rw [amplitudeIdeal_cube, Ideal.mem_span_range_iff_exists_fun] at hp
  obtain ⟨c, hc⟩ := hp
  let B : Matrix n n R := fun i j => ∑ k, c ((i, j), k) * r k
  refine ⟨B, ?_, ?_⟩
  · intro i j
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (amplitude_mem r k)
  · rw [← hc]
    simp only [B, dotProduct, mulVec, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Symmetrization over a real algebra, including real polynomial rings. -/
def symmetrize (B : Matrix n n R) : Matrix n n R :=
  (1 / 2 : ℝ) • (B + B.transpose)

omit [Fintype n] [DecidableEq n] in
theorem symmetrize_symmetric (B : Matrix n n R) : (symmetrize B).IsSymm := by
  ext i j
  simp [symmetrize, add_comm]

omit [DecidableEq n] in
theorem symmetrize_quadratic (B : Matrix n n R) (r : n → R) :
    r ⬝ᵥ (symmetrize B *ᵥ r) = r ⬝ᵥ (B *ᵥ r) := by
  have ht : r ⬝ᵥ (B.transpose *ᵥ r) = r ⬝ᵥ (B *ᵥ r) := by
    simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [symmetrize, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, ht]
  rw [← two_smul ℝ (r ⬝ᵥ (B *ᵥ r)), smul_smul]
  norm_num

omit [Fintype n] [DecidableEq n] in
theorem symmetrize_mem (B : Matrix n n R) (I : Ideal R)
    (hB : ∀ i j, B i j ∈ I) (i j : n) : symmetrize B i j ∈ I := by
  change (1 / 2 : ℝ) • (B i j + B j i) ∈ I
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ (I.add_mem (hB i j) (hB j i))

omit [DecidableEq n] in
/-- The extracted symmetric matrix vanishes entrywise on the amplitude face.
The equality is in the polynomial ring, not merely modulo normalization. -/
theorem exists_symmetric_matrix_of_mem_cube (r : n → R) {p : R}
    (hp : p ∈ amplitudeIdeal r ^ 3) :
    ∃ B : Matrix n n R, B.IsSymm ∧
      (∀ i j, B i j ∈ amplitudeIdeal r) ∧ r ⬝ᵥ (B *ᵥ r) = p := by
  obtain ⟨B, hB, hpB⟩ := exists_matrix_of_mem_cube r hp
  exact ⟨symmetrize B, symmetrize_symmetric B,
    symmetrize_mem B _ hB, (symmetrize_quadratic B r).trans hpB⟩

end CZExposure.MatrixExtraction
