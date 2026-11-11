/-
Copyright (c) 2026 LowerBoundCZ authors.
-/
import LowerBoundCZ.Dynamics
import LowerBoundCZ.Dual
import LowerBoundCZ.Upper

/-!
# Headline two-sided bound

Combines the exact five-cell dual with the interval-certified pulse.
-/

noncomputable section

namespace LowerBoundCZ

/-- Every admissible globally driven CZ exposure is at least `293/100`. -/
theorem exposure_ge_splitBound : (splitBound : ℝ) ≤ Cstar :=
  le_csInf AdmissibleExposures_nonempty split_exact_bound

/-- Certified window `2.930 ≤ C_* < 2.935875225844105`. -/
theorem certified_window :
    (splitBound : ℝ) ≤ Cstar ∧ Cstar < upperEndpoint :=
  ⟨exposure_ge_splitBound, Cstar_lt_upperEndpoint⟩

/-- Relative width of the certified interval is below `0.21%`. -/
theorem certified_gap_lt : upperEndpoint - (splitBound : ℝ) < 0.006 := by
  unfold upperEndpoint splitBound
  norm_num

end LowerBoundCZ
