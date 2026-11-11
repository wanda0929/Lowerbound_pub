module
public import RequestProject.AppendixE.Model

/-!
# The real-coefficient SOS hierarchies (Eq. (E2) and the partitioned program)

All certificates are real polynomials in the real coordinates of the state, the control
`u = u_x + i u_y`, and (for the partitioned program) the local cell coordinate `ξ`.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial

/-- Variables of the polynomial ring: the eight real state coordinates, the two real control
coordinates `(Re u, Im u)`, and the local cell coordinate `ξ`. -/
inductive Var
  | st (i : Fin 8)
  | ctl (i : Fin 2)
  | xi
  deriving DecidableEq

/-- Polynomials in state, control and cell coordinate. -/
abbrev Poly := MvPolynomial Var ℝ

/-- Polynomials in the state coordinates only (used for stationary certificates `W(x)`). -/
abbrev StatePoly := MvPolynomial (Fin 8) ℝ

/-- Polynomials in the cell coordinate `ξ` (the variable `none`) and the state coordinates
(used for cell certificates `W_j(ξ, x)`). -/
abbrev CellPoly := MvPolynomial (Option (Fin 8)) ℝ

/-- Evaluation point for a value `ξ` of the cell coordinate, a state `x` and a control `u`. -/
def pt (ξ : ℝ) (x : State) (u : ℂ) : Var → ℝ
  | .st i => x i
  | .ctl i => ![u.re, u.im] i
  | .xi => ξ

/-- Embedding of state polynomials. -/
def ofState (W : StatePoly) : Poly := rename Var.st W

/-- Embedding of cell polynomials (`none ↦ ξ`). -/
def ofCell (W : CellPoly) : Poly := rename (fun o => Option.elim o Var.xi Var.st) W

/-- Evaluation of a cell polynomial at `(ξ, x)`. -/
def evalCell (ξ : ℝ) (x : State) (W : CellPoly) : ℝ := eval (fun o => Option.elim o ξ x) W

/-- Substitution of a constant `t` for the cell coordinate. -/
def atXi (t : ℝ) (W : CellPoly) : StatePoly :=
  aeval (fun o : Option (Fin 8) => Option.elim o (C t) X) W

/-- The state coordinate variable `x_i`. -/
abbrev xs (i : Fin 8) : Poly := X (Var.st i)
/-- The control variable `Re u`. -/
abbrev ua : Poly := X (Var.ctl 0)
/-- The control variable `Im u`. -/
abbrev ub : Poly := X (Var.ctl 1)

/-- The vector field of Eq. (12) as a polynomial map (real coordinates). -/
def fpoly : Fin 8 → Poly :=
  ![C (1 / 2) * (ua * xs 3 + ub * xs 2), -C (1 / 2) * (ua * xs 2 - ub * xs 3),
    C (1 / 2) * (ua * xs 1 - ub * xs 0), -C (1 / 2) * (ua * xs 0 + ub * xs 1),
    C (Real.sqrt 2 / 2) * (ua * xs 7 + ub * xs 6), -C (Real.sqrt 2 / 2) * (ua * xs 6 - ub * xs 7),
    C (Real.sqrt 2 / 2) * (ua * xs 5 - ub * xs 4), -C (Real.sqrt 2 / 2) * (ua * xs 4 + ub * xs 5)]

/-- The exposure rate `c = (2|r₁|² + |r₂|²)/4` as a polynomial. -/
def cpoly : Poly := C (1 / 4) * (2 * (xs 2 ^ 2 + xs 3 ^ 2) + (xs 6 ^ 2 + xs 7 ^ 2))

/-- The Lie derivative `f_u W = ∇W · f_u` of a stationary certificate. -/
def lieDeriv (W : StatePoly) : Poly := ∑ i : Fin 8, ofState (pderiv i W) * fpoly i

/-- The cell operator `L_j = f · ∇_x + κ c ∂_ξ` of Eq. (23), with `κ = 1/(U w_j)`. -/
def cellOp (κ : ℝ) (W : CellPoly) : Poly :=
  (∑ i : Fin 8, ofCell (pderiv (some i) W) * fpoly i) + C κ * cpoly * ofCell (pderiv none W)

/-- The normalization ideal `I = ⟨|g₁|²+|r₁|²-1, |g₂|²+|r₂|²-1, |u|²-1⟩` of Eq. (E1). -/
def normIdeal : Ideal Poly :=
  Ideal.span {xs 0 ^ 2 + xs 1 ^ 2 + xs 2 ^ 2 + xs 3 ^ 2 - 1,
    xs 4 ^ 2 + xs 5 ^ 2 + xs 6 ^ 2 + xs 7 ^ 2 - 1, ua ^ 2 + ub ^ 2 - 1}

/-- The state normalization ideal (state variables only), used for interface certificates. -/
def stateNormIdeal : Ideal StatePoly :=
  Ideal.span {X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 1, X 4 ^ 2 + X 5 ^ 2 + X 6 ^ 2 + X 7 ^ 2 - 1}

/-- `p` is a sum of squares of polynomials of total degree at most `d`. -/
def IsSOS {σ : Type*} (d : ℕ) (p : MvPolynomial σ ℝ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → MvPolynomial σ ℝ), (∀ l, (h l).totalDegree ≤ d) ∧ p = ∑ l, h l ^ 2

/-- Feasibility in the stationary order-`d` program (E2): `W` is a real `G`-invariant
polynomial with `deg W ≤ 2d - 1`, `W|_Z ≤ 0`, and `c + f_u W ≡ ∑ h_ℓ²  (mod I)` with
`deg h_ℓ ≤ d`. -/
def StationaryFeasible (d : ℕ) (W : StatePoly) : Prop :=
  W.totalDegree ≤ 2 * d - 1 ∧ IsGInvariant (fun x => eval x W) ∧ (∀ x ∈ XCZ, eval x W ≤ 0) ∧
    ∃ σ : Poly, IsSOS d σ ∧ cpoly + lieDeriv W - σ ∈ normIdeal

/-- The optimal value `L_d^unsplit` of the stationary order-`d` program (E2). -/
def Lunsplit (d : ℕ) : EReal :=
  ⨆ (W : StatePoly) (_ : StationaryFeasible d W), ((eval x0 W : ℝ) : EReal)

/-- A finite partition `0 = a₀ < a₁ < ⋯ < a_J = 1` of the normalized cumulative-exposure range
(Eq. (22)), cells being indexed by `j = 0, …, J-1`. -/
structure ExposurePartition where
  J : ℕ
  J_pos : 0 < J
  a : ℕ → ℝ
  a_zero : a 0 = 0
  a_last : a J = 1
  a_lt : ∀ j < J, a j < a (j + 1)

/-- The width `w_j = a_{j+1} - a_j` of cell `j`. -/
def ExposurePartition.width (P : ExposurePartition) (j : ℕ) : ℝ := P.a (j + 1) - P.a j

/-- Feasibility in the order-`d` partitioned program (Sec. III C, Eq. (24), with SOS
representations as in Appendix C 2 but over complete real polynomial spaces), for a partition
`P` and exposure ceiling `U`: each cell certificate `W_j(ξ, x)` is a real polynomial, `G`-invariant
in `x`, with `deg W_j ≤ 2d - 1`, such that
* (drift) `c + L_j W_j ≡ σ₀ + ξ(1-ξ) σ₁ (mod I)` with SOS `σ₀`, `σ₁` of degrees `d`, `d-1`;
* (interface) `W_{j+1}(0, x) - W_j(1, x) ≡ ∑ h²` modulo the state normalizations, `deg h ≤ d`;
* (terminal) `W_j ≤ 0` on `[0,1] × X_CZ`. -/
def SplitFeasible (P : ExposurePartition) (U : ℝ) (d : ℕ) (W : ℕ → CellPoly) : Prop :=
  ∀ j < P.J,
    (W j).totalDegree ≤ 2 * d - 1 ∧
    (∀ ξ, IsGInvariant (fun x => evalCell ξ x (W j))) ∧
    (∃ σ₀ σ₁ : Poly, IsSOS d σ₀ ∧ IsSOS (d - 1) σ₁ ∧
      cpoly + cellOp (1 / (U * P.width j)) (W j) -
        (σ₀ + X Var.xi * (1 - X Var.xi) * σ₁) ∈ normIdeal) ∧
    (j + 1 < P.J → ∃ σ : StatePoly, IsSOS d σ ∧
      atXi 0 (W (j + 1)) - atXi 1 (W j) - σ ∈ stateNormIdeal) ∧
    (∀ ξ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ XCZ, evalCell ξ x (W j) ≤ 0)

/-- The optimal value `L_d^split` of the order-`d` partitioned program, i.e. the supremum of
`W₁(0, x₀)` over feasible cell certificates. -/
def Lsplit (P : ExposurePartition) (U : ℝ) (d : ℕ) : EReal :=
  ⨆ (W : ℕ → CellPoly) (_ : SplitFeasible P U d W), ((evalCell 0 x0 (W 0) : ℝ) : EReal)

end CZExposure
