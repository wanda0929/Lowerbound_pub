import RequestProject.AppendixE.PolynomialExistence
import RequestProject.AppendixE.Completeness

/-!
# Polynomial existence audit

Combined-import check: `PolynomialExistence` and `Completeness`
load together. Axiom audit of every new public declaration added in
this milestone: the two input definitions in
`C1ApproximationInput.lean`, the four generic norm/derivative
helpers, and the four physical existence theorems in
`PolynomialExistence.lean`.

Expected: every audited declaration uses only standard Lean axioms —
no `sorryAx` and no project `External` axioms — with the integrated
conditional `Completeness` module also imported.
`BoxC1PolynomialApproximation` is printed so its full quantifier
structure (dimension at least two, positive radius, `ContDiff` one,
positive tolerance, common polynomial for values and all coordinate
derivative errors) is visible. Its inhabitant is proved by Bernstein
approximation, and the physical approximation theorem needs no such input.
-/

noncomputable section

namespace CZExposure.PolynomialGeometry

/-! ## Generic input definitions -/

#check @coordinateBox
#print axioms coordinateBox

/- The generic approximation input, printed so its quantifier
structure is visible: `∀ n ≥ 2`, `∀ R > 0`, `∀ C¹ φ`, `∀ δ > 0`. -/
#print BoxC1PolynomialApproximation
#check @BoxC1PolynomialApproximation
#print axioms BoxC1PolynomialApproximation

example : BoxC1PolynomialApproximation := boxC1PolynomialApproximation

run_cmd do
  for name in [``boxC1PolynomialApproximation,
      ``CZExposure.PolynomialApproximation.exists_C1ApproxOnY,
      ``CZExposure.PolynomialApproximation.exists_strict_candidate_below_Cstar] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

/-! ## Operator-norm conversion helpers -/

#check @linearForm_apply_eq_sum
#print axioms linearForm_apply_eq_sum

#check @linearForm_norm_le
#print axioms linearForm_norm_le

#check @fderiv_eval_basis
#print axioms fderiv_eval_basis

#check @fderiv_difference_norm_le
#print axioms fderiv_difference_norm_le

/- Boundary check: the generic norm bound also covers the empty
domain (`n = 0`), even though the input requires `n ≥ 2`. -/
example (L : (Fin 0 → ℝ) →L[ℝ] ℝ) : ‖L‖ = 0 := by
  have h := linearForm_norm_le L (δ := 0) le_rfl (fun i => Fin.elim0 i)
  exact le_antisymm (by simp at h ⊢) (norm_nonneg L)

end CZExposure.PolynomialGeometry

namespace CZExposure.PolynomialApproximation

open CZExposure.PolynomialGeometry

/-! ## Conditional existence theorems -/

#check @exists_box_for_Yset
#print axioms exists_box_for_Yset

#check @exists_C1ApproxOnY
#print axioms exists_C1ApproxOnY

#check @exists_strict_candidate
#print axioms exists_strict_candidate

/- The final theorem takes only directed-arc superposition;
local steering and C¹ approximation are now proved. -/
#check @exists_strict_candidate_below_Cstar
#print axioms exists_strict_candidate_below_Cstar

end CZExposure.PolynomialApproximation
