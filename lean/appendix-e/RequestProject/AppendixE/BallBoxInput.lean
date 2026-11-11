module
public import Mathlib

/-!
# Generic ball-box input

This file specifies `CompactRegularLevelBallBox`, an explicit,
unproved corollary for compact regular level sets in finite
dimensional real space. It requires smooth constraint and control
fields, a surjective constraint differential, tangent control fields,
and six independent actual brackets of lengths up to four spanning
the differential kernel. Its conclusion gives bounded, measurable
real quadratures with integral-form dynamics and duration at most
`C L^(1/4)` when a smooth connecting path has ambient length at most
`L ≤ R`. It does not mention Rydberg exposure, conditional phase, or
CZ endpoints. No axiom asserts this proposition; it is a derived
corollary packaging the regular-level-set manifold interpretation,
uniform compactness bounds, norm-length comparison, and
integral-control realization — not the verbatim statement of any
source theorem.
-/

@[expose] public section

noncomputable section

namespace CZExposure.ControlGeometry

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The six actual bracket fields of lengths up to four. -/
def stepFourFields {n : ℕ}
    (X Y : (Fin n → ℝ) → (Fin n → ℝ)) :
    Fin 6 → ((Fin n → ℝ) → (Fin n → ℝ)) :=
  ![X, Y, VectorField.lieBracket ℝ X Y,
    VectorField.lieBracket ℝ Y (VectorField.lieBracket ℝ X Y),
    VectorField.lieBracket ℝ (VectorField.lieBracket ℝ X Y) X,
    VectorField.lieBracket ℝ X
      (VectorField.lieBracket ℝ (VectorField.lieBracket ℝ X Y) X)]

/-- A regular equiregular step-four system on a compact level set. -/
structure RegularStepFourSystem (n m : ℕ) where
  constraint : (Fin n → ℝ) → (Fin m → ℝ)
  level : Fin m → ℝ
  fieldX : (Fin n → ℝ) → (Fin n → ℝ)
  fieldY : (Fin n → ℝ) → (Fin n → ℝ)
  constraint_smooth : ContDiff ℝ ⊤ constraint
  fieldX_smooth : ContDiff ℝ ⊤ fieldX
  fieldY_smooth : ContDiff ℝ ⊤ fieldY
  compact : IsCompact {x | constraint x = level}
  regular : ∀ x, constraint x = level →
    Function.Surjective (fderiv ℝ constraint x)
  tangentX : ∀ x, constraint x = level →
    fderiv ℝ constraint x (fieldX x) = 0
  tangentY : ∀ x, constraint x = level →
    fderiv ℝ constraint x (fieldY x) = 0
  independent : ∀ x, constraint x = level →
    LinearIndependent ℝ (fun i : Fin 6 => stepFourFields fieldX fieldY i x)
  spanning : ∀ x, constraint x = level →
    Submodule.span ℝ (Set.range (fun i : Fin 6 => stepFourFields fieldX fieldY i x)) =
      (fderiv ℝ constraint x).toLinearMap.ker

/-- Generic integral-form admissible segment; no physical costs or
endpoints appear. -/
structure QuadratureSegment {n m : ℕ} (S : RegularStepFourSystem n m) where
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  path : ℝ → (Fin n → ℝ)
  controlX : ℝ → ℝ
  controlY : ℝ → ℝ
  controlX_measurable : Measurable controlX
  controlY_measurable : Measurable controlY
  control_bound : ∀ t ∈ Set.Icc 0 duration, (controlX t)^2 + (controlY t)^2 ≤ 1
  path_mem : ∀ t ∈ Set.Icc 0 duration, S.constraint (path t) = S.level
  velocity_integrable : IntervalIntegrable
    (fun t => controlX t • S.fieldX (path t) + controlY t • S.fieldY (path t))
    volume 0 duration
  integralEquation : ∀ s ∈ Set.Icc 0 duration,
    path s = path 0 + ∫ t in (0:ℝ)..s,
      controlX t • S.fieldX (path t) + controlY t • S.fieldY (path t)

/-- The conclusion of the generic corollary, not an asserted value. -/
structure BallBoxBound {n m : ℕ} (S : RegularStepFourSystem n m) where
  radius : ℝ
  radius_pos : 0 < radius
  K : ℝ
  K_pos : 0 < K
  connect : ∀ (x y : Fin n → ℝ) (w : ℝ → (Fin n → ℝ)) (L : ℝ),
    0 ≤ L → L ≤ radius → ContDiffOn ℝ ⊤ w (Set.Icc 0 1) →
    (∀ t ∈ Set.Icc 0 1, S.constraint (w t) = S.level) →
    w 0 = x → w 1 = y → eVariationOn w (Set.Icc 0 1) ≤ ENNReal.ofReal L →
    ∃ P : QuadratureSegment S, P.path 0 = x ∧ P.path P.duration = y ∧
      P.duration ≤ K * Real.rpow L (1/4 : ℝ)

/-- The explicit generic theorem input. This is UNPROVED: no axiom
and no inhabitant of this proposition is introduced. -/
def CompactRegularLevelBallBox : Prop :=
  ∀ {n m : ℕ} (S : RegularStepFourSystem n m), Nonempty (BallBoxBound S)

end CZExposure.ControlGeometry
