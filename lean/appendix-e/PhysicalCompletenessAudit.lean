import RequestProject.AppendixE.PhysicalCompleteness
import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.ControlLieAlgebra
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Physical-completeness audit

Axiom audit for the cutoff limit and conditional physical
completeness. The pulse constructions and completeness theorems
explicitly take `H : LocalSteering`; the scalar cutoff inequality
`fifth_power_le_half` is independent of `H`. No inhabitant of
`LocalSteering` is constructed or assumed by an axiom in this
development.  The cutoff-limit and `_of_superposition` declarations
use only standard Lean axioms (`hSuperposition` and `H` are explicit
inputs).  The three default wrappers
(`exists_pulse_of_record`, `Cstar_le_pRelaxed`, `pRelaxed_eq_Cstar`)
additionally depend on exactly the pre-existing
`External.euclideanDirectedArcSuperposition` axiom — not on any new
axiom, `sorryAx`, or the global unconditional theorems.  No `ε`-limit
uniform duration bound is claimed.
-/

noncomputable section

namespace CZExposure

/-! ## Cutoff limit (`α = β⁵`) -/

#check @LocalSteering.cutoffOverhead
#print axioms LocalSteering.cutoffOverhead
#check @LocalSteering.cutoffCoefficient
#print axioms LocalSteering.cutoffCoefficient
#check @LocalSteering.cutoffCoefficient_nonneg
#print axioms LocalSteering.cutoffCoefficient_nonneg
#check @LocalSteering.fifth_power_le_half
#print axioms LocalSteering.fifth_power_le_half
#check @LocalSteering.cutoffOverhead_eq
#print axioms LocalSteering.cutoffOverhead_eq
#check @LocalSteering.tendsto_cutoffOverhead
#print axioms LocalSteering.tendsto_cutoffOverhead
#check @LocalSteering.exists_cutoff_for_error
#print axioms LocalSteering.exists_cutoff_for_error

/-! ## Trajectory approximation: full type shows all trajectory/ODE
hypotheses and the `H` parameter -/

#check @LocalSteering.exists_pulse_approx_exposure_trajectory
#print axioms LocalSteering.exists_pulse_approx_exposure_trajectory

/-! ## Record-to-pulse and the conditional equality -/

#check @LocalSteering.exists_pulse_of_record_of_superposition
#print axioms LocalSteering.exists_pulse_of_record_of_superposition
#check @LocalSteering.Cstar_le_pRelaxed_of_superposition
#print axioms LocalSteering.Cstar_le_pRelaxed_of_superposition
#check @LocalSteering.pRelaxed_eq_Cstar_of_superposition
#print axioms LocalSteering.pRelaxed_eq_Cstar_of_superposition

/-! ## Default wrappers: standard axioms + the existing
`External.euclideanDirectedArcSuperposition` only -/

#check @LocalSteering.exists_pulse_of_record
#print axioms LocalSteering.exists_pulse_of_record
#check @LocalSteering.Cstar_le_pRelaxed
#print axioms LocalSteering.Cstar_le_pRelaxed
#check @LocalSteering.pRelaxed_eq_Cstar
#print axioms LocalSteering.pRelaxed_eq_Cstar

/-! ## Edge examples -/

/-- `β^5 ≤ β/2` at `β = 0` — pure algebra, no physical cutoff needed. -/
example : (0:ℝ)^5 ≤ 0/2 :=
  LocalSteering.fifth_power_le_half (le_refl _) (by norm_num)

/-- The coefficient vanishes at `T = 0` (analytic boundary case). -/
example (H : LocalSteering) : H.cutoffCoefficient 0 = 0 := by
  simp [LocalSteering.cutoffCoefficient,
    Real.zero_rpow (by norm_num : (3/4 : ℝ) ≠ 0)]

/-- For arbitrary `H`, `T = 0`, `ε = 1` there is a positive cutoff —
the existential supplies `β > 0`, not `0`. -/
example (H : LocalSteering) : ∃ β : ℝ, 0 < β :=
  (H.exists_cutoff_for_error (le_refl (0:ℝ)) (by norm_num : (0:ℝ) < 1)).imp
    fun β h => h.1

end CZExposure
