import RequestProject.AppendixE.ControlLieAlgebra
import RequestProject.AppendixE.SteeringExposure
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Audit: step-four Lie-bracket rank condition

Aggregate-import axiom audit of `ControlLieAlgebra.lean`, composed
with `SteeringExposure` and `RelaxedSubsolution` to check namespace
compatibility (as with the earlier `vf_neg_control` collision).
Expected axioms are only `[propext, Classical.choice, Quot.sound]`.
-/

open CZExposure

namespace CZExposure.ControlLie

-- The six-parameter linear action.
#check @Params
#check @act
#print axioms act
#check @actLM
#print axioms actLM
#check @actCLM
#print axioms actCLM
#check @actCLM_apply
#print axioms actCLM_apply
#check @hasFDerivAt_act
#print axioms hasFDerivAt_act
#check @contDiff_act
#print axioms contDiff_act

-- Exact Lie-bracket coefficients and identities.
#check @coeffBracket
#print axioms coeffBracket
#check @lieBracket_act
#print axioms lieBracket_act
#check @vf_eq_act
#print axioms vf_eq_act

-- Drive and nested bracket fields: print the definitions so the
-- bracket nesting and mathlib derivative convention are visible.
#print driveX
#print driveY
#print bracket2
#print bracket3X
#print bracket3Y
#print bracket4
#print axioms driveX
#print axioms driveY
#print axioms bracket2
#print axioms bracket3X
#print axioms bracket3Y
#print axioms bracket4
#check @driveX_eq_act
#print axioms driveX_eq_act
#check @driveY_eq_act
#print axioms driveY_eq_act
#check @bracket2_eq_act
#print axioms bracket2_eq_act
#check @bracket3X_eq_act
#print axioms bracket3X_eq_act
#check @bracket3Y_eq_act
#print axioms bracket3Y_eq_act
#check @bracket4_eq_act
#print axioms bracket4_eq_act
#check @bracketFields
#print axioms bracketFields
#check @contDiff_bracketFields
#print axioms contDiff_bracketFields

-- Constraint differential and coordinate tangent space.
#check @normal
#print axioms normal
#check @normalLM
#print axioms normalLM
#check @normalCLM
#print axioms normalCLM
#check @normalCLM_apply
#print axioms normalCLM_apply
#check @normalization
#print axioms normalization
#check @normalization_eq_norms
#print axioms normalization_eq_norms
#check @mem_Xset_iff_normalization
#print axioms mem_Xset_iff_normalization
#check @hasFDerivAt_normalization
#print axioms hasFDerivAt_normalization
#check @tangentSpace
#print axioms tangentSpace
#check @mem_tangentSpace_iff
#print axioms mem_tangentSpace_iff
#check @mem_tangentSpace_iff_fderiv
#print axioms mem_tangentSpace_iff_fderiv
#check @normal_surjective
#print axioms normal_surjective
#check @act_mem_tangent
#print axioms act_mem_tangent

-- Explicit kernel parametrization and equivalence.
#check @frame
#print axioms frame
#check @frameCoords
#print axioms frameCoords
#check @frameCoords_act
#print axioms frameCoords_act
#check @act_frameCoords
#print axioms act_frameCoords
#check @tangentEquiv
#print axioms tangentEquiv
#check @finrank_tangentSpace
#print axioms finrank_tangentSpace

-- Bracket-field expression and rank statements.
#check @bracketCoordinates
#print axioms bracketCoordinates
#check @act_eq_sum_bracketFields
#print axioms act_eq_sum_bracketFields
#check @bracketFields_mem_tangent
#print axioms bracketFields_mem_tangent
#check @span_bracketFields_eq_tangentSpace
#print axioms span_bracketFields_eq_tangentSpace
#check @linearIndependent_bracketFields
#print axioms linearIndependent_bracketFields
#check @finrank_prefix
#print axioms finrank_prefix

/-! ## Edge examples -/

/-- The initial state lies in `Xset`; the rank statement applies. -/
example : x0 ∈ Xset := by
  rw [mem_Xset_iff_normalization]
  funext i
  fin_cases i <;> simp [normalization, normal, x0]

example : LinearIndependent ℝ (fun i : Fin 6 => bracketFields i x0) :=
  linearIndependent_bracketFields (x := x0) (by
    rw [mem_Xset_iff_normalization]
    funext i
    fin_cases i <;> simp [normalization, normal, x0])

example : Module.finrank ℝ (tangentSpace x0) = 6 :=
  finrank_tangentSpace (x := x0) (by
    rw [mem_Xset_iff_normalization]
    funext i
    fin_cases i <;> simp [normalization, normal, x0])

/-- The fully excited state `mkState 0 1 0 1` is in `Xset`: rank six
holds even with vanishing ground amplitudes (no division used). -/
example : mkState 0 1 0 1 ∈ Xset := by
  rw [mem_Xset_iff_normalization]
  funext i
  fin_cases i <;> simp [normalization, normal, mkState]

example : LinearIndependent ℝ
    (fun i : Fin 6 => bracketFields i (mkState 0 1 0 1)) :=
  linearIndependent_bracketFields (x := mkState 0 1 0 1) (by
    rw [mem_Xset_iff_normalization]
    funext i
    fin_cases i <;> simp [normalization, normal, mkState])

/-- Prefix ranks 2, 3, 5, 6 at an arbitrary admissible state. -/
example {x : State} (hx : x ∈ Xset) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : Fin 2 => bracketFields (Fin.castLE (by norm_num : 2 ≤ 6) i) x)))
      = 2 :=
  finrank_prefix hx 2 (by norm_num)

example {x : State} (hx : x ∈ Xset) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : Fin 3 => bracketFields (Fin.castLE (by norm_num : 3 ≤ 6) i) x)))
      = 3 :=
  finrank_prefix hx 3 (by norm_num)

example {x : State} (hx : x ∈ Xset) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : Fin 5 => bracketFields (Fin.castLE (by norm_num : 5 ≤ 6) i) x)))
      = 5 :=
  finrank_prefix hx 5 (by norm_num)

example {x : State} (hx : x ∈ Xset) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : Fin 6 => bracketFields (Fin.castLE (by norm_num : 6 ≤ 6) i) x)))
      = 6 :=
  finrank_prefix hx 6 (by norm_num)

end CZExposure.ControlLie
