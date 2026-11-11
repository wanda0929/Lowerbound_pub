import LowerBoundCZ.Basic
import RequestProject.AppendixE.ConcretePartitioned
import RequestProject.AppendixE.UnitControlRealization
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Interfaces for certificate integration, NOT instantiated certificates.
The historical `LowerBoundCZ.Cstar` and its axioms are not used here.
See CertificateContracts.md for archive correspondence and open obligations. -/

noncomputable section
namespace LowerBoundCZ.Certification
open CZExposure Complex MeasureTheory Set

/-- Canonical maximum-amplitude, integral-solution problem. -/
abbrev ActivePulse := CZExposure.Pulse
abbrev activeCstar : EReal := CZExposure.Cstar

/-- The amplitude-limited laboratory problem, in dimensionless laboratory time.
The shared complex control includes both amplitude and phase. -/
structure LabPulse where
  S : ℝ
  S_nonneg : 0 ≤ S
  u : ℝ → ℂ
  u_measurable : Measurable u
  x : ℝ → State
  u_bound : ∀ s ∈ Icc 0 S, ‖u s‖ ≤ 1
  x_mem : ∀ s ∈ Icc 0 S, x s ∈ Xset
  integrable : ∀ i, IntervalIntegrable (fun t => vf (x t) (u t) i) volume 0 S
  ode : ∀ s ∈ Icc 0 S, ∀ i, x s i = x0 i + ∫ t in (0 : ℝ)..s, vf (x t) (u t) i
  terminal : x S ∈ XCZ

def LabPulse.exposure (γ : LabPulse) : ℝ := ∫ s in (0 : ℝ)..γ.S, cost (γ.x s)
def labCstar : EReal := ⨅ γ : LabPulse, (γ.exposure : EReal)

/-- The inclusion of full-amplitude pulses needs no time change. -/
def toLab (γ : ActivePulse) : LabPulse where
  S := γ.S
  S_nonneg := γ.S_nonneg
  u := γ.u
  u_measurable := γ.u_measurable
  x := γ.x
  u_bound := fun s hs => (γ.u_unit s hs).le
  x_mem := γ.x_mem
  integrable := γ.integrable
  ode := γ.ode
  terminal := γ.terminal

theorem toLab_exposure (γ : ActivePulse) : (toLab γ).exposure = γ.exposure := rfl

theorem labCstar_le_activeCstar : labCstar ≤ activeCstar := by
  refine le_iInf fun γ => ?_
  exact iInf_le_of_le (toLab γ) (le_refl _)

namespace LabPulse

theorem initial (γ : LabPulse) : γ.x 0 = x0 := by
  funext i
  simpa using γ.ode 0 ⟨le_rfl, γ.S_nonneg⟩ i

/-- Repackage the coordinatewise integral equation as a vector equation.
No regularity, positive-amplitude, or invertible-clock hypothesis is added. -/
def toSegment (γ : LabPulse) : PhysicalSegment := by
  have hv : IntervalIntegrable (fun t => vf (γ.x t) (γ.u t)) volume 0 γ.S := by
    rw [intervalIntegrable_iff]
    exact integrable_pi_iff.mpr fun i => intervalIntegrable_iff.mp (γ.integrable i)
  exact {
    duration := γ.S
    duration_nonneg := γ.S_nonneg
    path := γ.x
    control := γ.u
    control_measurable := γ.u_measurable
    control_bound := γ.u_bound
    path_mem := γ.x_mem
    velocity_integrable := hv
    integralEquation := by
      intro s hs
      have hv' := hv.mono_set (uIcc_subset_uIcc_of_mem
        (Set.left_mem_Icc.mpr γ.S_nonneg) hs)
      funext i
      have hproj := (ContinuousLinearMap.proj i :
        State →L[ℝ] ℝ).intervalIntegral_comp_comm hv'
      change (∫ t in (0 : ℝ)..s, vf (γ.x t) (γ.u t) i) =
        (∫ t in (0 : ℝ)..s, vf (γ.x t) (γ.u t)) i at hproj
      simpa only [Pi.add_apply, γ.initial, ← hproj] using γ.ode s hs i }

/-- Remove idling and normalize the drive using Appendix E's measurable
active-time selector. The result has exactly the same terminal state. -/
def compress (γ : LabPulse) : ActivePulse :=
  γ.toSegment.toUnitPulse γ.initial γ.terminal

theorem compress_duration (γ : LabPulse) :
    γ.compress.S = ∫ t in (0 : ℝ)..γ.S, ‖γ.u t‖ := rfl

theorem compress_duration_le (γ : LabPulse) : γ.compress.S ≤ γ.S :=
  γ.toSegment.toUnitPulse_duration_le γ.initial γ.terminal

theorem compress_terminal (γ : LabPulse) : γ.compress.x γ.compress.S = γ.x γ.S :=
  γ.toSegment.toUnit_terminal

/-- The compressed path preserves every state, indexed by accumulated active time. -/
theorem compress_path (γ : LabPulse) {t : ℝ} (ht : t ∈ Icc 0 γ.S) :
    γ.compress.x (∫ q in (0 : ℝ)..t, ‖γ.u q‖) = γ.x t :=
  γ.toSegment.activePath_activeClock ht

theorem compress_exposure (γ : LabPulse) :
    γ.compress.exposure = ∫ t in (0 : ℝ)..γ.S, cost (γ.x t) * ‖γ.u t‖ :=
  γ.toSegment.activeExposure_eq_weightedExposure

theorem compress_exposure_le (γ : LabPulse) : γ.compress.exposure ≤ γ.exposure :=
  γ.toSegment.toUnitPulse_exposure_le γ.initial γ.terminal

end LabPulse

theorem activeCstar_le_labCstar : activeCstar ≤ labCstar := by
  refine le_iInf fun γ => ?_
  exact iInf_le_of_le γ.compress (EReal.coe_le_coe_iff.mpr γ.compress_exposure_le)

/-- Maximum-amplitude reduction for all measurable integral-solution lab pulses,
including controls with zero-amplitude intervals. No existence assumption is needed. -/
theorem labCstar_eq_activeCstar : labCstar = activeCstar :=
  le_antisymm labCstar_le_activeCstar activeCstar_le_labCstar

namespace Lower

/-- Polynomial payload after exact archive decoding. No validity is assumed. -/
structure Payload where
  partition : ExposurePartition
  ceiling : ℝ
  order : ℕ
  offset : ℝ
  potential : ℕ → CellPoly
  target : ℝ

/-- Algebraic certificate interface. `PotentialFeasible` expands to degree,
symmetry, quotient Gram identities, PSD blocks and terminal interval identities.
Archive decoding/basis correspondence must be established separately. -/
structure Checks (a : Payload) : Prop where
  ceiling_pos : 0 < a.ceiling
  target_le_ceiling : a.target ≤ a.ceiling
  order_pos : 0 < a.order
  feasible : ConcretePartitioned.PotentialFeasible
    a.partition a.ceiling a.order a.offset a.potential
  objective : -a.offset - evalCell 0 x0 (a.potential 0) = a.target

/-- This is the proof obligation discharged by the existing weak-duality API,
not a field of Checks. It does not require completeness or a successful witness. -/
theorem Checks.active_lower {a : Payload} (h : Checks a) :
    (a.target : EReal) ≤ activeCstar := by
  have hf := (ConcretePartitioned.feasible_shifted_iff
    a.partition a.ceiling a.order a.offset a.potential).2 h.feasible
  refine le_iInf fun γ => EReal.coe_le_coe_iff.2 ?_
  by_cases hγ : γ.exposure < a.ceiling
  · have hb := hf.weak_duality γ hγ
    simpa only [ConcretePartitioned.evalCell_shifted, h.objective] using hb
  · exact h.target_le_ceiling.trans (le_of_not_gt hγ)

/-- The same certificate bounds the amplitude-limited laboratory problem. -/
theorem Checks.lab_lower {a : Payload} (h : Checks a) :
    (a.target : EReal) ≤ labCstar := by
  rw [labCstar_eq_activeCstar]
  exact h.active_lower

end Lower

namespace Upper

abbrev Parameters := Fin 5 → ℝ
abbrev LinearMap := Parameters →L[ℝ] Parameters

/-- A sector's endpoint and accumulated Rydberg population integral. -/
structure SectorRecord where
  ground : ℂ
  rydberg : ℂ
  population : ℝ

/-- Exact constant-control segment recurrence used by the pinned Arb checker.
Its agreement with the integral ODE and cost is proved in `UpperSegments`. -/
def segment (k : ℕ) (dt phase : ℝ) (z : SectorRecord) : SectorRecord :=
  let rate := Real.sqrt k / 2
  let angle := dt * rate
  let u : ℂ := ⟨Real.cos phase, Real.sin phase⟩
  let q := -I * star u * z.ground
  { ground := z.ground * (Real.cos angle : ℂ) -
      I * u * z.rydberg * (Real.sin angle : ℂ)
    rydberg := z.rydberg * (Real.cos angle : ℂ) + q * (Real.sin angle : ℂ)
    population := z.population +
      (dt / 2 + Real.sin (2 * angle) / (4 * rate)) * normSq z.rydberg +
      (dt / 2 - Real.sin (2 * angle) / (4 * rate)) * normSq q +
      ((1 - Real.cos (2 * angle)) / (2 * rate)) *
        (z.rydberg.re * q.re + z.rydberg.im * q.im) }

/-- The four phase indices are zero-based, as in the Python source.
These phases parameterize u = exp(+i phase), i.e. minus the paper's laser chi. -/
def phase (fixed : Fin 12672 → ℝ) (p : Parameters) (j : Fin 12672) : ℝ :=
  if j.val = 731 then p 1 else if j.val = 6676 then p 2 else
  if j.val = 8661 then p 3 else if j.val = 11922 then p 4 else fixed j

def propagate (fixed : Fin 12672 → ℝ) (p : Parameters) (k : ℕ) : SectorRecord :=
  (List.finRange 12672).foldl
    (fun z j => segment k (p 0 / 12672) (phase fixed p j) z) ⟨1, 0, 0⟩

def residual (fixed : Fin 12672 → ℝ) (p : Parameters) : Parameters :=
  let a := propagate fixed p 1
  let b := propagate fixed p 2
  ![a.rydberg.re, a.rydberg.im, b.rydberg.re, b.rydberg.im,
    (b.ground * star (a.ground * a.ground)).im]

def branch (fixed : Fin 12672 → ℝ) (p : Parameters) : ℝ :=
  ((propagate fixed p 2).ground *
    star ((propagate fixed p 1).ground * (propagate fixed p 1).ground)).re

def exposure (fixed : Fin 12672 → ℝ) (p : Parameters) : ℝ :=
  (2 * (propagate fixed p 1).population + (propagate fixed p 2).population) / 4

/-- Exact real payload. Decimal strings must be decoded as exact rationals,
not binary floats. The Jacobian set represents the checker's interval matrix. -/
structure Payload where
  fixed : Fin 12672 → ℝ
  center : Parameters
  radius : ℝ
  inverse : LinearMap
  jacobians : Set LinearMap
  contraction : ℝ

/-- Numerical enclosures only: no root, successful pulse, or Cstar bound.
Differentiability and the mean-value/Krawczyk argument are Lean obligations,
not external inputs. The finite Pi norm is the infinity norm. -/
structure NumericalBounds (a : Payload) : Prop where
  radius_pos : 0 < a.radius
  duration_pos : ∀ p ∈ Metric.closedBall a.center a.radius, 0 < p 0
  contraction_nonneg : 0 ≤ a.contraction
  contraction_lt_one : a.contraction < 1
  defect_bound : ∀ A ∈ a.jacobians,
    ‖ContinuousLinearMap.id ℝ Parameters - a.inverse.comp A‖ ≤ a.contraction
  krawczyk_interior : ∀ p ∈ Metric.closedBall a.center a.radius,
    ∀ A ∈ a.jacobians,
      a.center - a.inverse (residual a.fixed a.center) +
        (ContinuousLinearMap.id ℝ Parameters - a.inverse.comp A) (p - a.center)
        ∈ Metric.ball a.center a.radius
  cz_branch : ∀ p ∈ Metric.closedBall a.center a.radius, branch a.fixed p < 0
  exposure_bound : ∀ p ∈ Metric.closedBall a.center a.radius,
    exposure a.fixed p < upperEndpoint

/-- Analytic form of the enclosure, derived from the forward-mode program by
`AD.Enclosures.analyticChecks`. No convexity/closedness of the Jacobian set is
needed: the proof applies the scalar mean-value theorem coordinatewise. -/
structure Checks (a : Payload) : Prop extends NumericalBounds a where
  jacobian_enclosure : ∀ p ∈ Metric.closedBall a.center a.radius,
    fderiv ℝ (residual a.fixed) p ∈ a.jacobians

end Upper
end LowerBoundCZ.Certification
