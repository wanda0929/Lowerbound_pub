import RequestProject.AppendixE.ReducedBasis

noncomputable section
namespace CZExposure.ReducedBasis
open MvPolynomial
open scoped Matrix

#print axioms difference_mem_span
#print axioms group_conversion
#print axioms groupColumn_restrict
#print axioms restriction_group_sums
#print axioms grouped_conversion
#print axioms face_span_eq
#print axioms groupColumn_degree
#print axioms reducedColumn_degree
#print axioms gram_conversion
#print axioms face_sos_gram
#check @face_span_eq
#check @face_sos_gram

run_cmd do
  for name in [``difference_mem_span, ``group_conversion, ``groupColumn_restrict,
      ``restriction_group_sums, ``grouped_conversion, ``face_span_eq,
      ``groupColumn_degree, ``reducedColumn_degree, ``gram_conversion, ``face_sos_gram] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Singleton groups contribute no reduced columns, including over ℂ.
example (m : ℕ → ℂ) (a : Fin 1 → ℂ) (ha : ∑ i, a i = 0) :
    ∑ i, a i * m i.val = 0 := by
  obtain ⟨b, hb⟩ := group_conversion m 0 a ha
  simpa using hb

-- The prescribed columns are not replaced by differences against a pivot.
-- Fractional coordinates are necessary: (2,-5,3) = (7/2)h₁ − (3/2)h₂.
example (x : ℝ) :
    2 - 5*x + 3*x^2 =
      (7/2 : ℝ) * groupColumn (K := ℝ) (fun i => x^i) 1 -
      (3/2 : ℝ) * groupColumn (K := ℝ) (fun i => x^i) 2 := by
  norm_num [groupColumn, Finset.sum_range_succ]
  ring

-- The largest-degree member cannot silently be discarded in the bound.
example : (groupColumn (K := ℝ)
    (fun i => (X () : MvPolynomial Unit ℝ)^i) 2).totalDegree ≤ 2 := by
  apply groupColumn_degree
  intro i hi
  simpa using hi

-- Formal restriction at x=1: the three monomials form one group.
private def atOne : MvPolynomial Unit ℝ →ₗ[ℝ] (Unit →₀ ℝ) :=
  (Finsupp.lsingle ()) ∘ₗ (aeval (fun _ : Unit => (1 : ℝ))).toLinearMap

-- End-to-end reduced Gram construction with zero already-vanishing columns.
-- Both factors vanish at x=1; the resulting matrix has exactly two columns.
example :
    ∃ Q : Matrix (Empty ⊕ ((_c : Unit) × Fin 2)) (Empty ⊕ ((_c : Unit) × Fin 2)) ℝ,
      Q.PosSemidef ∧
      (∑ k : Fin 2,
        (![2 - 5 * X () + 3 * X ()^2, 1 - X ()^2] k : MvPolynomial Unit ℝ)^2) =
      ∑ i, ∑ j,
        reducedColumn (K := ℝ) (fun e : Empty => e.elim) (fun _ l => X ()^l)
          (fun _ : Unit => 2) i * C (Q i j) *
        reducedColumn (K := ℝ) (fun e : Empty => e.elim) (fun _ l => X ()^l)
          (fun _ : Unit => 2) j := by
  let z : Empty → MvPolynomial Unit ℝ := fun e => e.elim
  let m : Unit → ℕ → MvPolynomial Unit ℝ := fun _ i => X ()^i
  let f : Fin 2 → MvPolynomial Unit ℝ := ![2 - 5 * X () + 3 * X ()^2, 1 - X ()^2]
  have hm (c : Unit) (i : ℕ) (_ : i ≤ 2) : atOne (m c i) = Finsupp.single c 1 := by
    cases c
    simp [atOne, m]
  have hf (k : Fin 2) : f k ∈ Submodule.span ℝ
      (Set.range (originalColumn z m (fun _ => 2))) := by
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
    let a : Fin 2 → Fin 3 → ℝ := ![![2, -5, 3], ![1, 0, -1]]
    refine ⟨Sum.elim (fun e : Empty => e.elim) (fun j => a k j.2), ?_⟩
    fin_cases k <;>
      simp [originalColumn, Fintype.sum_sum_type, Fintype.sum_sigma,
        Fin.sum_univ_succ, a, m, f, smul_eq_C_mul, map_ofNat] <;> ring
  have hTf (k : Fin 2) : atOne (f k) = 0 := by
    fin_cases k <;> norm_num [atOne, f]
  exact (face_sos_gram atOne z m (fun _ => 2) (fun e => e.elim) hm 2
    (fun e => e.elim) (fun _ i hi => by simpa [m] using hi) f hf hTf).2

-- Matrix orientation and cross terms: asymmetric coefficients give a
-- non-diagonal matrix, so confusing AᵀA with AAᵀ is detectable.
example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, -3; -1, 4]
    Aᴴ * A = !![5, -10; -10, 25] := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

end CZExposure.ReducedBasis
