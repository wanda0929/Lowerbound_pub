module
public import RequestProject.AppendixE.BFieldRegularity
public import Mathlib.Analysis.Calculus.VectorField

/-!
# Control Lie algebra: the step-four bracket rank condition

The actual real vector fields `X = vf(·,1)` and `Y = vf(·,i)` and their
iterated Lie brackets (in mathlib's derivative convention
`[V,W] = DW V − DV W`) span, at every `x ∈ Xset`, the kernel of the
differential of the two normalization constraints.  The span is
realized by an explicit six-coordinate parametrization `Params` of the
kernel — no division by an amplitude is needed, so all states are
covered, including `gₖ = 0` or `rₖ = 0`.

Scope: exact `VectorField.lieBracket` identities, the
constraint-differential kernel, and the rank statements.  No manifold
or metric structure is formalized and no steering-existence or
ball-box theorem is claimed.  The `State` norm stays the ambient sup
norm; `frameCoords` uses a coordinate bilinear form only.
-/

@[expose] public section

noncomputable section

namespace CZExposure.ControlLie

open MeasureTheory Set

/-- Six real coefficients: `A₁,B₁,C₁,A₂,B₂,C₂`. -/
abbrev Params := Fin 6 → ℝ

/-- The su(2) action on each unit spinor sector. -/
def act (p : Params) (x : State) : State :=
  ![p 0 * x 3 + p 1 * x 2 - p 2 * x 1,
    -p 0 * x 2 + p 1 * x 3 + p 2 * x 0,
    p 0 * x 1 - p 1 * x 0 + p 2 * x 3,
    -p 0 * x 0 - p 1 * x 1 - p 2 * x 2,
    p 3 * x 7 + p 4 * x 6 - p 5 * x 5,
    -p 3 * x 6 + p 4 * x 7 + p 5 * x 4,
    p 3 * x 5 - p 4 * x 4 + p 5 * x 7,
    -p 3 * x 4 - p 4 * x 5 - p 5 * x 6]

def actLM (p : Params) : State →ₗ[ℝ] State where
  toFun := act p
  map_add' := fun x y => by
    funext i
    fin_cases i <;> simp [act, Pi.add_apply] <;> ring
  map_smul' := fun r x => by
    funext i
    fin_cases i <;> simp [act, Pi.smul_apply, smul_eq_mul] <;> ring

def actCLM (p : Params) : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap (actLM p)

@[simp] theorem actCLM_apply (p : Params) (x : State) :
    actCLM p x = act p x := rfl

theorem hasFDerivAt_act (p : Params) (x : State) :
    HasFDerivAt (act p) (actCLM p) x :=
  (actCLM p).hasFDerivAt

theorem contDiff_act (p : Params) : ContDiff ℝ ⊤ (act p) :=
  (actCLM p).contDiff

/-- Coefficients of the Lie bracket of two `act` fields; `[A,B]=-2C`,
`[A,C]=2B`, `[B,C]=-2A` in each sector. -/
def coeffBracket (p q : Params) : Params :=
  ![2 * (p 2 * q 1 - p 1 * q 2),
    2 * (p 0 * q 2 - p 2 * q 0),
    2 * (p 1 * q 0 - p 0 * q 1),
    2 * (p 5 * q 4 - p 4 * q 5),
    2 * (p 3 * q 5 - p 5 * q 3),
    2 * (p 4 * q 3 - p 3 * q 4)]

theorem lieBracket_act (p q : Params) :
    VectorField.lieBracket ℝ (act p) (act q) = act (coeffBracket p q) := by
  rw [VectorField.lieBracket_eq]
  funext x
  rw [(hasFDerivAt_act q x).fderiv, (hasFDerivAt_act p x).fderiv]
  show actCLM q (act p x) - actCLM p (act q x) = act (coeffBracket p q) x
  rw [actCLM_apply, actCLM_apply]
  funext i
  fin_cases i <;> simp [act, coeffBracket] <;> ring

theorem vf_eq_act (x : State) (u : ℂ) :
    vf x u = act ![u.re / 2, u.im / 2, 0,
      Real.sqrt 2 * u.re / 2, Real.sqrt 2 * u.im / 2, 0] x := by
  funext i
  fin_cases i <;>
    simp [vf, fC, act, g1, r1, g2, r2, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/-! ## The bracket fields -/

def driveX : State → State := fun x => vf x 1
def driveY : State → State := fun x => vf x Complex.I
def bracket2 : State → State := VectorField.lieBracket ℝ driveX driveY
def bracket3X : State → State := VectorField.lieBracket ℝ driveY bracket2
def bracket3Y : State → State := VectorField.lieBracket ℝ bracket2 driveX
def bracket4 : State → State := VectorField.lieBracket ℝ driveX bracket3Y

theorem driveX_eq_act :
    driveX = act ![1/2, 0, 0, Real.sqrt 2 / 2, 0, 0] := by
  funext x
  show vf x 1 = _
  rw [vf_eq_act x 1]
  congr 1
  funext i
  fin_cases i <;> (simp; try ring_nf)

theorem driveY_eq_act :
    driveY = act ![0, 1/2, 0, 0, Real.sqrt 2 / 2, 0] := by
  funext x
  show vf x Complex.I = _
  rw [vf_eq_act x Complex.I]
  congr 1
  funext i
  fin_cases i <;> (simp; try ring_nf)

theorem bracket2_eq_act :
    bracket2 = act ![0, 0, -1/2, 0, 0, -1] := by
  unfold bracket2
  rw [driveX_eq_act, driveY_eq_act, lieBracket_act]
  congr 1
  funext i
  fin_cases i <;> simp [coeffBracket] <;>
    (ring_nf; try norm_num [Real.sq_sqrt, Real.mul_self_sqrt])

theorem bracket3X_eq_act :
    bracket3X = act ![1/2, 0, 0, Real.sqrt 2, 0, 0] := by
  unfold bracket3X
  rw [driveY_eq_act, bracket2_eq_act, lieBracket_act]
  congr 1
  funext i
  fin_cases i <;> simp [coeffBracket] <;>
    (ring_nf; try norm_num [Real.sq_sqrt, Real.mul_self_sqrt])

theorem bracket3Y_eq_act :
    bracket3Y = act ![0, 1/2, 0, 0, Real.sqrt 2, 0] := by
  unfold bracket3Y
  rw [bracket2_eq_act, driveX_eq_act, lieBracket_act]
  congr 1
  funext i
  fin_cases i <;> simp [coeffBracket] <;>
    (ring_nf; try norm_num [Real.sq_sqrt, Real.mul_self_sqrt])

theorem bracket4_eq_act :
    bracket4 = act ![0, 0, -1/2, 0, 0, -2] := by
  unfold bracket4
  rw [driveX_eq_act, bracket3Y_eq_act, lieBracket_act]
  congr 1
  funext i
  fin_cases i <;> simp [coeffBracket] <;>
    (ring_nf; try norm_num [Real.sq_sqrt, Real.mul_self_sqrt])

def bracketFields : Fin 6 → (State → State) :=
  ![driveX, driveY, bracket2, bracket3X, bracket3Y, bracket4]

theorem contDiff_bracketFields (i : Fin 6) :
    ContDiff ℝ ⊤ (bracketFields i) := by
  fin_cases i <;>
    simp [bracketFields] <;>
    (first
      | rw [driveX_eq_act]
      | rw [driveY_eq_act]
      | rw [bracket2_eq_act]
      | rw [bracket3X_eq_act]
      | rw [bracket3Y_eq_act]
      | rw [bracket4_eq_act])
    <;> exact contDiff_act _

/-! ## The normalization constraint and its tangent space -/

/-- Coordinate dot product of `x` and `v` on each sector block —
a bilinear form, not an inner product instance on the sup-normed
`State`. -/
def normal (x v : State) : Fin 2 → ℝ :=
  ![x 0*v 0 + x 1*v 1 + x 2*v 2 + x 3*v 3,
    x 4*v 4 + x 5*v 5 + x 6*v 6 + x 7*v 7]

def normalLM (x : State) : State →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := normal x
  map_add' := fun v w => by
    funext i
    fin_cases i <;> simp [normal, Pi.add_apply] <;> ring
  map_smul' := fun r v => by
    funext i
    fin_cases i <;> simp [normal, Pi.smul_apply, smul_eq_mul] <;> ring

def normalCLM (x : State) : State →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (normalLM x)

@[simp] theorem normalCLM_apply (x v : State) :
    normalCLM x v = normal x v := rfl

/-- The two normalization constraints. -/
def normalization (x : State) : Fin 2 → ℝ := normal x x

private theorem norm_sq_mk (a b : ℝ) :
    ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

theorem normalization_eq_norms (x : State) :
    normalization x =
      ![‖g1 x‖ ^ 2 + ‖r1 x‖ ^ 2, ‖g2 x‖ ^ 2 + ‖r2 x‖ ^ 2] := by
  funext i
  fin_cases i <;>
    simp [normalization, normal, g1, r1, g2, r2, norm_sq_mk] <;> ring

theorem mem_Xset_iff_normalization (x : State) :
    x ∈ Xset ↔ normalization x = (fun _ => 1) := by
  rw [normalization_eq_norms]
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [h1, h2]
  · intro h
    constructor
    · have := congrFun h 0
      simpa using this
    · have := congrFun h 1
      simpa using this

private theorem hasFDerivAt_mulCoord (x : State) (j : Fin 8) :
    HasFDerivAt (fun y : State => y j * y j)
      ((2 * x j) • (ContinuousLinearMap.proj j : State →L[ℝ] ℝ)) x := by
  have h : HasFDerivAt (fun y : State =>
      (ContinuousLinearMap.proj j : State →L[ℝ] ℝ) y *
      (ContinuousLinearMap.proj j : State →L[ℝ] ℝ) y)
      ((ContinuousLinearMap.proj j : State →L[ℝ] ℝ) x •
        (ContinuousLinearMap.proj j : State →L[ℝ] ℝ) +
        (ContinuousLinearMap.proj j : State →L[ℝ] ℝ) x •
        (ContinuousLinearMap.proj j : State →L[ℝ] ℝ)) x :=
    ((ContinuousLinearMap.proj j : State →L[ℝ] ℝ).hasFDerivAt).mul
      ((ContinuousLinearMap.proj j : State →L[ℝ] ℝ).hasFDerivAt)
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

theorem hasFDerivAt_normalization (x : State) :
    HasFDerivAt normalization (2 • normalCLM x) x := by
  apply hasFDerivAt_pi''
  intro i
  fin_cases i
  · have h := (((hasFDerivAt_mulCoord x 0).add (hasFDerivAt_mulCoord x 1)).add
      (hasFDerivAt_mulCoord x 2)).add (hasFDerivAt_mulCoord x 3)
    refine h.congr_fderiv ?_
    ext v
    simp [normalCLM_apply, normal]
    ring
  · have h := (((hasFDerivAt_mulCoord x 4).add (hasFDerivAt_mulCoord x 5)).add
      (hasFDerivAt_mulCoord x 6)).add (hasFDerivAt_mulCoord x 7)
    refine h.congr_fderiv ?_
    ext v
    simp [normalCLM_apply, normal]
    ring

/-- The kernel of the constraint differential: the coordinate tangent
space.  No manifold tangent bundle is asserted. -/
def tangentSpace (x : State) : Submodule ℝ State := (normalLM x).ker

theorem mem_tangentSpace_iff (x v : State) :
    v ∈ tangentSpace x ↔ normal x v = 0 :=
  LinearMap.mem_ker

theorem mem_tangentSpace_iff_fderiv (x v : State) :
    v ∈ tangentSpace x ↔ fderiv ℝ normalization x v = 0 := by
  rw [mem_tangentSpace_iff, (hasFDerivAt_normalization x).fderiv,
    ContinuousLinearMap.smul_apply, smul_eq_zero]
  simp [normalCLM_apply]

theorem normal_surjective {x : State} (hx : x ∈ Xset) :
    Function.Surjective (normal x) := by
  intro y
  refine ⟨![y 0 * x 0, y 0 * x 1, y 0 * x 2, y 0 * x 3,
    y 1 * x 4, y 1 * x 5, y 1 * x 6, y 1 * x 7], ?_⟩
  have hnorm : normalization x = fun _ => 1 :=
    (mem_Xset_iff_normalization x).mp hx
  have h0 : x 0*x 0 + x 1*x 1 + x 2*x 2 + x 3*x 3 = 1 := by
    have := congrFun hnorm 0
    simpa [normalization, normal] using this
  have h1 : x 4*x 4 + x 5*x 5 + x 6*x 6 + x 7*x 7 = 1 := by
    have := congrFun hnorm 1
    simpa [normalization, normal] using this
  funext i
  fin_cases i
  · show x 0*(y 0*x 0) + x 1*(y 0*x 1) + x 2*(y 0*x 2) +
      x 3*(y 0*x 3) = y 0
    rw [show x 0*(y 0*x 0) + x 1*(y 0*x 1) + x 2*(y 0*x 2) +
        x 3*(y 0*x 3) = y 0*(x 0*x 0 + x 1*x 1 + x 2*x 2 + x 3*x 3) from
      by ring, h0]
    ring
  · show x 4*(y 1*x 4) + x 5*(y 1*x 5) + x 6*(y 1*x 6) +
      x 7*(y 1*x 7) = y 1
    rw [show x 4*(y 1*x 4) + x 5*(y 1*x 5) + x 6*(y 1*x 6) +
        x 7*(y 1*x 7) = y 1*(x 4*x 4 + x 5*x 5 + x 6*x 6 + x 7*x 7) from
      by ring, h1]
    ring

theorem act_mem_tangent (x : State) (p : Params) :
    act p x ∈ tangentSpace x := by
  rw [mem_tangentSpace_iff]
  funext i
  fin_cases i <;> simp [normal, act] <;> ring

/-! ## The explicit kernel parametrization -/

/-- Unit-generator fields at `x`. -/
def frame (x : State) (i : Fin 6) : State := act (Pi.single i 1) x

/-- Kernel coordinates of `v`: a coordinate bilinear form, not an
inner-product instance. -/
def frameCoords (x v : State) : Params :=
  fun i => ∑ j : Fin 8, frame x i j * v j

private theorem frameCoords_act_aux (x : State) (p : Params) :
    frameCoords x (act p x) =
      ![p 0 * normalization x 0, p 1 * normalization x 0,
        p 2 * normalization x 0, p 3 * normalization x 1,
        p 4 * normalization x 1, p 5 * normalization x 1] := by
  funext i
  fin_cases i <;>
    simp [frameCoords, frame, normalization, normal, act,
      Fin.sum_univ_succ, Pi.single] <;> ring

theorem frameCoords_act {x : State} (hx : x ∈ Xset) (p : Params) :
    frameCoords x (act p x) = p := by
  rw [frameCoords_act_aux]
  have hn : normalization x = fun _ => 1 :=
    (mem_Xset_iff_normalization x).mp hx
  funext i
  fin_cases i <;> simp [hn]

private theorem act_frameCoords_aux (x v : State) (j : Fin 8) :
    act (frameCoords x v) x j =
      (if (j : ℕ) < 4 then
        normalization x 0 * v j - normal x v 0 * x j
      else normalization x 1 * v j - normal x v 1 * x j) := by
  fin_cases j <;>
    simp [act, frameCoords, frame, normalization, normal,
      Fin.sum_univ_succ, Pi.single] <;>
    ring

theorem act_frameCoords {x : State} (hx : x ∈ Xset) {v : State}
    (hv : v ∈ tangentSpace x) : act (frameCoords x v) x = v := by
  have hn : normalization x = fun _ => 1 :=
    (mem_Xset_iff_normalization x).mp hx
  have hv' : normal x v = 0 := (mem_tangentSpace_iff x v).mp hv
  funext j
  rw [act_frameCoords_aux]
  fin_cases j <;> simp [hn, hv']

/-- The linear equivalence `ℝ⁶ ≃ tangentSpace x` at every `x ∈ X`. -/
def tangentEquiv (x : State) (hx : x ∈ Xset) :
    Params ≃ₗ[ℝ] tangentSpace x where
  toFun p := ⟨act p x, act_mem_tangent x p⟩
  invFun v := frameCoords x v
  left_inv := frameCoords_act hx
  right_inv := fun v => Subtype.ext (act_frameCoords hx v.property)
  map_add' := fun p q => Subtype.ext (by
    funext i
    fin_cases i <;> simp [act, Pi.add_apply] <;> ring)
  map_smul' := fun r p => Subtype.ext (by
    funext i
    fin_cases i <;> simp [act, Pi.smul_apply, smul_eq_mul] <;> ring)

theorem finrank_tangentSpace {x : State} (hx : x ∈ Xset) :
    Module.finrank ℝ (tangentSpace x) = 6 := by
  rw [← (tangentEquiv x hx).finrank_eq]
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-! ## Bracket-field coordinates and rank -/

/-- Coefficients expressing `act p` in the displayed bracket fields. -/
def bracketCoordinates (p : Params) : Params :=
  ![4*p 0 - Real.sqrt 2*p 3,
    4*p 1 - Real.sqrt 2*p 4,
    -4*p 2 + p 5,
    -2*p 0 + Real.sqrt 2*p 3,
    -2*p 1 + Real.sqrt 2*p 4,
    2*p 2 - p 5]

theorem act_eq_sum_bracketFields (p : Params) (x : State) :
    act p x = ∑ i : Fin 6, (bracketCoordinates p i) • bracketFields i x := by
  funext j
  fin_cases j <;>
    simp [Fin.sum_univ_succ,
      bracketFields, bracketCoordinates, driveX_eq_act, driveY_eq_act,
      bracket2_eq_act, bracket3X_eq_act, bracket3Y_eq_act,
      bracket4_eq_act, act, smul_eq_mul] <;>
    ring_nf <;>
    try simp [Real.sq_sqrt] <;>
    try ring

theorem bracketFields_mem_tangent (x : State) (i : Fin 6) :
    bracketFields i x ∈ tangentSpace x := by
  fin_cases i <;>
    simp [bracketFields] <;>
    (first
      | rw [driveX_eq_act]
      | rw [driveY_eq_act]
      | rw [bracket2_eq_act]
      | rw [bracket3X_eq_act]
      | rw [bracket3Y_eq_act]
      | rw [bracket4_eq_act])
    <;> exact act_mem_tangent x _

theorem span_bracketFields_eq_tangentSpace {x : State} (hx : x ∈ Xset) :
    Submodule.span ℝ (Set.range (fun i : Fin 6 => bracketFields i x)) =
      tangentSpace x := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact bracketFields_mem_tangent x i
  · intro v hv
    rw [← act_frameCoords hx hv]
    rw [act_eq_sum_bracketFields]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))

theorem linearIndependent_bracketFields {x : State} (hx : x ∈ Xset) :
    LinearIndependent ℝ (fun i : Fin 6 => bracketFields i x) := by
  refine linearIndependent_iff_card_eq_finrank_span.mpr ?_
  show Fintype.card (Fin 6) = Module.finrank ℝ
    (Submodule.span ℝ
      (Set.range (fun i : Fin 6 => bracketFields i x)))
  rw [span_bracketFields_eq_tangentSpace hx, finrank_tangentSpace hx,
    Fintype.card_fin]

theorem finrank_prefix {x : State} (hx : x ∈ Xset) (n : ℕ) (hn : n ≤ 6) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range
        (fun i : Fin n => bracketFields (Fin.castLE hn i) x))) = n := by
  have hlin := (linearIndependent_bracketFields hx).comp
    (Fin.castLE hn) (Fin.strictMono_castLE hn).injective
  have hlin2 : LinearIndependent ℝ
      (fun i : Fin n => bracketFields (Fin.castLE hn i) x) := hlin
  rw [finrank_span_eq_card hlin2, Fintype.card_fin]

end CZExposure.ControlLie
