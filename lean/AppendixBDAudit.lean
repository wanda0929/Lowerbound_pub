import LowerBoundCZ.AppendixB
import LowerBoundCZ.AppendixD

/-!
The Appendix D entry below uses the paper's successful-pulse model, not
an everywhere differentiable trajectory or an assumed phase velocity.

Appendix B is checked through the complete physical-pulse bound, the infimum
over successful pulses, integrability of the original fiber density, and
convergence of its finite cutoffs. No area formula, endpoint identity,
integrability claim, or limit is supplied as an extra input.
The numerical quadrature value 2.4801 is not asserted by this audit.
-/

set_option autoImplicit false

open CZExposure MeasureTheory Set Filter
open scoped Topology

example (P : Pulse) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ P.S)
    (h1 : ∀ t ∈ Icc a b, g1 (P.x t) ≠ 0)
    (h2 : ∀ t ∈ Icc a b, g2 (P.x t) ≠ 0) :
    ∃ Φ1 Φ2 : ℝ → ℝ,
      AbsolutelyContinuousOnInterval Φ1 a b ∧
      AbsolutelyContinuousOnInterval Φ2 a b ∧
      (∀ t ∈ Icc a b, phaseFactor (Φ1 t) = complexUnitPhase (g1 (P.x t))) ∧
      (∀ t ∈ Icc a b, phaseFactor (Φ2 t) = complexUnitPhase (g2 (P.x t))) ∧
      (∀ᵐ t ∂(volume.restrict (Icc a b)),
        HasDerivAt (fun s => Φ2 s - 2 * Φ1 s)
          (-(1 / Real.sqrt 2) * (P.u t *
            (r2 (P.x t) / g2 (P.x t) - (Real.sqrt 2 : ℂ) * (r1 (P.x t) / g1 (P.x t)))).re) t ∧
        HasDerivAt
          (fun s => r2 (P.x s) / g2 (P.x s) -
            (Real.sqrt 2 : ℂ) * (r1 (P.x s) / g1 (P.x s)))
          ((Complex.I / (Real.sqrt 2 : ℂ)) * P.u t *
            ((r2 (P.x t) / g2 (P.x t)) ^ 2 - (r1 (P.x t) / g1 (P.x t)) ^ 2)) t) :=
  P.toPhysicalSegment.appendixD ha hab hb h1 h2

example (P : Pulse) :
    zObs (P.x 0) = 1 ∧ zObs (P.x P.S) = -1 := P.overlap_endpoints

example (P : Pulse) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 P.S)),
      HasDerivAt (fun s => (zObs (P.x s)).re)
        (overlapVelocity (P.x t) (P.u t)).re t ∧
      LowerBoundCZ.cFib |(zObs (P.x t)).re| *
        |(overlapVelocity (P.x t) (P.u t)).re| ≤ cost (P.x t) :=
  P.toPhysicalSegment.ae_fiber_product

example (P : Pulse) :
    IntervalIntegrable LowerBoundCZ.cFib volume 0 1 ∧
      2 * (∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ) ≤ P.exposure :=
  P.fiber_integrable_and_bound

example : ((2 * (∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ) : ℝ) : EReal) ≤ Cstar :=
  appendixB_Cstar

example (P : Pulse) :
    Tendsto (fun n : ℕ => 2 * ∫ ξ in (0 : ℝ)..1, min (LowerBoundCZ.cFib ξ) (n : ℝ))
      atTop (𝓝 (2 * ∫ ξ in (0 : ℝ)..1, LowerBoundCZ.cFib ξ)) :=
  P.fiber_truncation_limit

#print axioms PhysicalSegment.appendixD
#print axioms Pulse.toPhysicalSegment
#print axioms Pulse.overlap_endpoints
#print axioms PhysicalSegment.ae_fiber_product
#print axioms Pulse.fiber_smooth_lower_bound
#print axioms fiber_smooth_lower_bound_Cstar
#print axioms overlap_area_measure
#print axioms Pulse.fiber_integrable_and_bound
#print axioms appendixB_Cstar
#print axioms Pulse.fiber_truncation_limit

run_cmd do
  for name in [``PhysicalSegment.appendixD, ``Pulse.toPhysicalSegment,
      ``Pulse.overlap_endpoints, ``PhysicalSegment.ae_fiber_product,
      ``Pulse.fiber_smooth_lower_bound, ``fiber_smooth_lower_bound_Cstar,
      ``overlap_area_measure, ``Pulse.fiber_integrable_and_bound,
      ``appendixB_Cstar, ``Pulse.fiber_truncation_limit] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
