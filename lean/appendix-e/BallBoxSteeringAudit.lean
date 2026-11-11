import RequestProject.AppendixE.BallBoxSteering
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Ball-box steering audit

Axiom audit for the physical application of the generic ball-box
input.  The algebra/geometry/`physicalSystem` declarations and the
quadrature-to-segment conversion take no `H` or `hBB`; only the
conditional constructors `localSteeringOfBound`/`localSteeringOfBallBox`
and the completeness corollaries consume bound data or the explicit
generic input.  No value of `CompactRegularLevelBallBox`,
`BallBoxBound`, or `LocalSteering` is asserted: the generic corollary
remains unproved, and there is no steering axiom and no `sorryAx`.
The default wrapper uses only the pre-existing
`External.euclideanDirectedArcSuperposition` axiom.
-/

noncomputable section

namespace CZExposure

/-! ## Generic input structures (all hypotheses printed) -/

#check @ControlGeometry.stepFourFields
#print axioms ControlGeometry.stepFourFields
#print ControlGeometry.RegularStepFourSystem
#check @ControlGeometry.RegularStepFourSystem
#print axioms ControlGeometry.RegularStepFourSystem
#print ControlGeometry.QuadratureSegment
#check @ControlGeometry.QuadratureSegment
#print axioms ControlGeometry.QuadratureSegment
#print ControlGeometry.BallBoxBound
#check @ControlGeometry.BallBoxBound
#print axioms ControlGeometry.BallBoxBound
#print axioms ControlGeometry.CompactRegularLevelBallBox
#print ControlGeometry.CompactRegularLevelBallBox

/-! ## Ambient-vs-Euclidean length helpers -/

#check @StateGeometry.lipschitz_euclideanEquiv_symm
#print axioms StateGeometry.lipschitz_euclideanEquiv_symm
#check @StateGeometry.GeometricPath.ambient_variation_le_length
#print axioms StateGeometry.GeometricPath.ambient_variation_le_length

/-! ## Physical system (no `H`, no `hBB`) -/

#check @BallBoxSteering.contDiff_normalization
#print axioms BallBoxSteering.contDiff_normalization
#check @BallBoxSteering.normalization_fderiv_surjective
#print axioms BallBoxSteering.normalization_fderiv_surjective
#check @BallBoxSteering.normalization_ker
#print axioms BallBoxSteering.normalization_ker
#check @BallBoxSteering.stepFourFields_physical
#print axioms BallBoxSteering.stepFourFields_physical
#check @BallBoxSteering.physicalSystem
#print axioms BallBoxSteering.physicalSystem

/-! ## Quadrature conversion -/

#check @BallBoxSteering.quadratureControl
#print axioms BallBoxSteering.quadratureControl
#check @BallBoxSteering.norm_quadratureControl_sq
#print axioms BallBoxSteering.norm_quadratureControl_sq
#check @BallBoxSteering.vf_quadrature
#print axioms BallBoxSteering.vf_quadrature
#check @BallBoxSteering.toPhysicalSegment
#print axioms BallBoxSteering.toPhysicalSegment
#check @BallBoxSteering.toPhysicalSegment_duration
#print axioms BallBoxSteering.toPhysicalSegment_duration
#check @BallBoxSteering.toPhysicalSegment_path
#print axioms BallBoxSteering.toPhysicalSegment_path

/-! ## Conditional constructors and completeness -/

#check @BallBoxSteering.localSteeringOfBound
#print axioms BallBoxSteering.localSteeringOfBound
#check @BallBoxSteering.localSteeringOfBound_radius
#print axioms BallBoxSteering.localSteeringOfBound_radius
#check @BallBoxSteering.localSteeringOfBound_K
#print axioms BallBoxSteering.localSteeringOfBound_K
#check @BallBoxSteering.localSteeringOfBallBox
#print axioms BallBoxSteering.localSteeringOfBallBox
#check @BallBoxSteering.Cstar_le_pRelaxed_of_ballBox_of_superposition
#print axioms BallBoxSteering.Cstar_le_pRelaxed_of_ballBox_of_superposition
#check @BallBoxSteering.pRelaxed_eq_Cstar_of_ballBox_of_superposition
#print axioms BallBoxSteering.pRelaxed_eq_Cstar_of_ballBox_of_superposition
#check @BallBoxSteering.pRelaxed_eq_Cstar_of_ballBox
#print axioms BallBoxSteering.pRelaxed_eq_Cstar_of_ballBox

/-! ## Edge examples -/

/-- Coincident endpoints under a bound: `d = 0` gives zero duration,
since `K * 0^(1/4) = 0` and duration is nonnegative. -/
example (B : ControlGeometry.BallBoxBound BallBoxSteering.physicalSystem)
    {x : State} (hx : x ∈ Xset) :
    ∃ P : PhysicalSegment, P.duration = 0 := by
  obtain ⟨P, hP0, hPD, hPdur⟩ :=
    (BallBoxSteering.localSteeringOfBound B).connect x hx x hx (by
      rw [sub_self, norm_zero]
      exact le_min (by norm_num)
        (div_nonneg B.radius_pos.le (by norm_num)))
  refine ⟨P, le_antisymm ?_ P.duration_nonneg⟩
  simpa [sub_self] using hPdur

/-- Quadrature norms at `(0,0)` and `(1,0)` — the disk endpoints. -/
example : ‖BallBoxSteering.quadratureControl 0 0‖ = 0 := by
  show ‖(⟨0, 0⟩ : ℂ)‖ = 0
  rw [show (⟨0, 0⟩ : ℂ) = 0 from rfl]
  exact norm_zero
example : ‖BallBoxSteering.quadratureControl 1 0‖ = 1 := by
  show ‖(⟨1, 0⟩ : ℂ)‖ = 1
  rw [show (⟨1, 0⟩ : ℂ) = 1 from rfl]
  exact norm_one

/-- The constructed steering constants as functions of the supplied
generic bound. -/
example (B : ControlGeometry.BallBoxBound BallBoxSteering.physicalSystem) :
    (BallBoxSteering.localSteeringOfBound B).radius =
      min ((1:ℝ)/4) (B.radius/16) := rfl
example (B : ControlGeometry.BallBoxBound BallBoxSteering.physicalSystem) :
    (BallBoxSteering.localSteeringOfBound B).K =
      B.K * (16:ℝ)^(1/4 : ℝ) := rfl

end CZExposure
