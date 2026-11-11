module
public import Mathlib

/-!
# The active-time CZ exposure problem (Sec. II–III of the paper, as used in Appendix E)

States `x = (g₁, r₁, g₂, r₂) ∈ ℂ⁴` are stored through their eight real coordinates
`(Re g₁, Im g₁, Re r₁, Im r₁, Re g₂, Im g₂, Re r₂, Im r₂)`, because all polynomials of the
hierarchy are real polynomials in these real coordinates ("complete polynomial spaces with
real coefficients").
-/

@[expose] public section

noncomputable section

namespace CZExposure

open Complex MeasureTheory Set ComplexConjugate

/-- A state, stored by its eight real coordinates
`(Re g₁, Im g₁, Re r₁, Im r₁, Re g₂, Im g₂, Re r₂, Im r₂)`. -/
abbrev State := Fin 8 → ℝ

/-- Ground amplitude of sector 1. -/
def g1 (x : State) : ℂ := ⟨x 0, x 1⟩
/-- Rydberg amplitude of sector 1. -/
def r1 (x : State) : ℂ := ⟨x 2, x 3⟩
/-- Ground amplitude of sector 2. -/
def g2 (x : State) : ℂ := ⟨x 4, x 5⟩
/-- Rydberg amplitude of sector 2. -/
def r2 (x : State) : ℂ := ⟨x 6, x 7⟩

/-- Build a state from its four complex amplitudes `(g₁, r₁, g₂, r₂)`. -/
def mkState (a b c d : ℂ) : State := ![a.re, a.im, b.re, b.im, c.re, c.im, d.re, d.im]

/-- The vector field of Eq. (12), in complex form:
`f(x,u) = -(i/2) (u r₁, ū g₁, √2 u r₂, √2 ū g₂)`. -/
def fC (x : State) (u : ℂ) : Fin 4 → ℂ :=
  ![-(I / 2) * (u * r1 x), -(I / 2) * (conj u * g1 x),
    -(I / 2) * ((Real.sqrt 2 : ℂ) * u * r2 x), -(I / 2) * ((Real.sqrt 2 : ℂ) * conj u * g2 x)]

/-- The vector field `f_u(x)` of Eq. (12) in real coordinates. -/
def vf (x : State) (u : ℂ) : State :=
  ![(fC x u 0).re, (fC x u 0).im, (fC x u 1).re, (fC x u 1).im,
    (fC x u 2).re, (fC x u 2).im, (fC x u 3).re, (fC x u 3).im]

/-- The input-averaged exposure rate `c(x) = (2|r₁|² + |r₂|²)/4`. -/
def cost (x : State) : ℝ := (2 * ‖r1 x‖ ^ 2 + ‖r2 x‖ ^ 2) / 4

/-- The two-sector state manifold `X = {|g₁|²+|r₁|² = 1, |g₂|²+|r₂|² = 1}` of Eq. (13). -/
def Xset : Set State :=
  {x | ‖g1 x‖ ^ 2 + ‖r1 x‖ ^ 2 = 1 ∧ ‖g2 x‖ ^ 2 + ‖r2 x‖ ^ 2 = 1}

/-- The CZ terminal orbit `Z = X_CZ = {x ∈ X : r₁ = r₂ = 0, g₂ = -g₁²}` of Eq. (14). -/
def XCZ : Set State :=
  {x | x ∈ Xset ∧ r1 x = 0 ∧ r2 x = 0 ∧ g2 x = -(g1 x) ^ 2}

/-- The zero-cost face `F = {x ∈ X : r₁ = r₂ = 0}`. -/
def Fface : Set State := {x | x ∈ Xset ∧ r1 x = 0 ∧ r2 x = 0}

/-- The initial state `x₀ = (1, 0, 1, 0)`. -/
def x0 : State := ![1, 0, 0, 0, 1, 0, 0, 0]

/-- A successful pulse of the program (15): a measurable unit-modulus control `u` on a finite
active duration `S`, together with an (absolutely continuous, Carathéodory) solution `x` of
`dx/ds = f(x(s), u(s))` with `x(0) = x₀`, `(x(s), u(s)) ∈ K` and `x(S) ∈ X_CZ`. -/
structure Pulse where
  /-- the active duration -/
  S : ℝ
  S_nonneg : 0 ≤ S
  /-- the drive (phase) control -/
  u : ℝ → ℂ
  u_measurable : Measurable u
  /-- the trajectory -/
  x : ℝ → State
  u_unit : ∀ s ∈ Icc 0 S, ‖u s‖ = 1
  x_mem : ∀ s ∈ Icc 0 S, x s ∈ Xset
  integrable : ∀ i, IntervalIntegrable (fun t => vf (x t) (u t) i) volume 0 S
  ode : ∀ s ∈ Icc 0 S, ∀ i, x s i = x0 i + ∫ t in (0 : ℝ)..s, vf (x t) (u t) i
  terminal : x S ∈ XCZ

/-- The exposure `C[u] = ∫₀^S c(x(s)) ds` of a pulse. -/
def Pulse.exposure (γ : Pulse) : ℝ := ∫ s in (0 : ℝ)..γ.S, cost (γ.x s)

/-- The minimum exposure `C*`: the infimum of `C[u]` over all successful pulses
(valued in `EReal`, so that it is `⊤` if no successful pulse existed). -/
def Cstar : EReal := ⨅ γ : Pulse, (γ.exposure : EReal)

/-! ## The symmetry group `G` (Sec. III B), acting on states -/

/-- Optical gauge: `r_k ↦ e^{-iθ} r_k` (paired with `u ↦ e^{iθ} u`). -/
def opticalGauge (θ : ℝ) (x : State) : State :=
  mkState (g1 x) (exp (-(θ : ℂ) * I) * r1 x) (g2 x) (exp (-(θ : ℂ) * I) * r2 x)

/-- Qubit gauge: `(g₁, r₁) ↦ e^{iα}(g₁, r₁)`, `(g₂, r₂) ↦ e^{2iα}(g₂, r₂)`. -/
def qubitGauge (α : ℝ) (x : State) : State :=
  mkState (exp ((α : ℂ) * I) * g1 x) (exp ((α : ℂ) * I) * r1 x)
    (exp (2 * (α : ℂ) * I) * g2 x) (exp (2 * (α : ℂ) * I) * r2 x)

/-- Reflection: complex conjugation of all amplitudes (paired with `u ↦ -ū`). -/
def reflection (x : State) : State :=
  mkState (conj (g1 x)) (conj (r1 x)) (conj (g2 x)) (conj (r2 x))

/-- A real function of the state is `G`-invariant if it is invariant under the two phase
rotations and the reflection generating `G`. -/
def IsGInvariant (w : State → ℝ) : Prop :=
  ∀ x θ α, w (opticalGauge θ x) = w x ∧ w (qubitGauge α x) = w x ∧ w (reflection x) = w x

/-! ## Exposure coordinates (Appendix E 2, Step 1) -/

/-- The progress observable `z = ḡ₂ g₁² + √2 r̄₂ g₁ r₁` of Eq. (E4). -/
def zObs (x : State) : ℂ :=
  conj (g2 x) * g1 x ^ 2 + (Real.sqrt 2 : ℂ) * conj (r2 x) * g1 x * r1 x

/-- The exposure-coordinate map `J(x) = (Re z, Im z, c², c² x_R) ∈ ℝ¹¹` of Eq. (E5). -/
def Jmap (x : State) : Fin 11 → ℝ :=
  Fin.cons (zObs x).re (Fin.cons (zObs x).im (Fin.cons (cost x ^ 2) (fun i => cost x ^ 2 * x i)))

/-- The image `J(x₀) = (1, 0, …, 0)` of the initial state. -/
def y0 : Fin 11 → ℝ := Fin.cons 1 0

/-- The image `J(Z) = {(-1, 0, …, 0)}` of the CZ target orbit. -/
def yPi : Fin 11 → ℝ := Fin.cons (-1) 0

/-- The transformed state space `Y = J(X)`. -/
def Yset : Set (Fin 11 → ℝ) := Jmap '' Xset

/-- The velocity per unit exposure `B(J(x), u) = DJ(x) f_u(x) / c(x)` on `{c > 0}`, and `B = 0`
on `J(F)`. Off `F`, the state is recovered from `y = J(x)` as `x_R = (y₃,…,y₁₀)/y₂`. -/
def Bfield (y : Fin 11 → ℝ) (u : ℂ) : Fin 11 → ℝ :=
  if 0 < y 2 then
    let x : State := fun i => y (i.succ.succ.succ) / y 2
    (cost x)⁻¹ • (fderiv ℝ Jmap x (vf x u))
  else 0

/-- Feasible exposure records of the relaxed program (E6): finite nonnegative measures on
`Y × U` (with `U` the closed unit disk) satisfying the net balance identity
`∫ B · ∇ψ dν = ψ(y_π) - ψ(y₀)` for every compactly supported smooth `ψ`. -/
def IsExposureRecord (ν : Measure ((Fin 11 → ℝ) × ℂ)) : Prop :=
  IsFiniteMeasure ν ∧ ν (Yset ×ˢ Metric.closedBall (0 : ℂ) 1)ᶜ = 0 ∧
    ∀ ψ : (Fin 11 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ p, fderiv ℝ ψ p.1 (Bfield p.1 p.2) ∂ν = ψ yPi - ψ y0

/-- The optimal value `p` of the relaxed program (E6). -/
def pRelaxed : EReal :=
  ⨅ (ν : Measure ((Fin 11 → ℝ) × ℂ)) (_ : IsExposureRecord ν), ((ν Set.univ : ENNReal) : EReal)

end CZExposure
