module

public import RequestProject.AppendixE.Completeness
public import RequestProject.AppendixE.FaceProjection
public import RequestProject.AppendixE.ReducedBasis
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Formal face restriction in the actual physical coordinates. The coefficient
index is (ξ degree, u winding, g₁ winding, g₂ winding). Distinct characters
are proved independent, rather than assumed independent from their labels. -/

@[expose] public section
noncomputable section

namespace CZExposure.FaceRestriction

open MvPolynomial ComplexConjugate

abbrev Index := ℕ × (Fin 3 → ℤ)
abbrev Parameters := ℝ × (Fin 3 → ℝ)
abbrev FaceAlgebra := AddMonoidAlgebra ℂ Index
abbrev ComplexPoly := MvPolynomial Var ℂ

def exponent (k : Index) (t : Parameters) : ℂ :=
  k.1 * (t.1 : ℂ) + ∑ i, (k.2 i : ℂ) * (t.2 i : ℂ) * Complex.I

def character (k : Index) : Multiplicative Parameters →* ℂ where
  toFun t := Complex.exp (exponent k t.toAdd)
  map_one' := by simp [exponent]
  map_mul' s t := by
    change Complex.exp (exponent k (s.toAdd + t.toAdd)) = _
    rw [show exponent k (s.toAdd + t.toAdd) =
      exponent k s.toAdd + exponent k t.toAdd by
        simp [exponent, mul_add, add_mul, Finset.sum_add_distrib]; ring,
      Complex.exp_add]

private theorem exp_linear_injective {a b : ℂ}
    (h : ∀ t : ℝ, Complex.exp ((t : ℂ) * a) = Complex.exp ((t : ℂ) * b)) : a = b := by
  have hd (c : ℂ) : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const c).cexp (x := (0 : ℝ))
  exact (hd a).unique (by simpa only [funext h] using hd b)

theorem character_injective : Function.Injective character := by
  intro a b h
  have hp : (a.1 : ℂ) = b.1 := by
    apply exp_linear_injective
    intro t
    have e := DFunLike.congr_fun h (Multiplicative.ofAdd (t, 0))
    simpa [character, exponent, mul_comm] using e
  have hq (i : Fin 3) : (a.2 i : ℂ) * Complex.I = (b.2 i : ℂ) * Complex.I := by
    apply exp_linear_injective
    intro t
    have e := DFunLike.congr_fun h (Multiplicative.ofAdd (0, Pi.single i t))
    simpa [character, exponent, Pi.single_apply, apply_ite, mul_ite, ite_mul,
      Finset.sum_ite_eq', mul_left_comm, mul_comm] using e
  apply Prod.ext
  · exact_mod_cast hp
  · funext i
    exact_mod_cast (mul_right_cancel₀ Complex.I_ne_zero (hq i))

theorem characters_independent :
    LinearIndependent ℂ (fun k => (character k : Multiplicative Parameters → ℂ)) :=
  (linearIndependent_monoidHom (Multiplicative Parameters) ℂ).comp
    character character_injective

def indexCharacter (t : Parameters) : Multiplicative Index →* ℂ where
  toFun k := character k.toAdd (Multiplicative.ofAdd t)
  map_one' := by simp [character, exponent]
  map_mul' a b := by
    change Complex.exp (exponent (a.toAdd + b.toAdd) t) =
      Complex.exp (exponent a.toAdd t) * Complex.exp (exponent b.toAdd t)
    rw [show exponent (a.toAdd + b.toAdd) t =
      exponent a.toAdd t + exponent b.toAdd t by
        simp [exponent, add_mul, Finset.sum_add_distrib]; ring,
      Complex.exp_add]

def evaluate (t : Parameters) : FaceAlgebra →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ Index (indexCharacter t)

/-- Evaluations at positive ξ and all three independent phases already
determine every formal coefficient. -/
theorem eq_zero_of_evaluate (p : FaceAlgebra) (hp : ∀ t, evaluate t p = 0) : p = 0 := by
  apply (linearIndependent_iff.mp characters_independent) p
  funext t
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, evaluate,
    AddMonoidAlgebra.lift_apply, indexCharacter, Finset.sum_apply] using hp t.toAdd

def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

def faceState (t : Parameters) : State := mkState (phase (t.2 1)) 0 (phase (t.2 2)) 0

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem faceState_mem (t : Parameters) : faceState t ∈ Fface := by
  simp [faceState, Fface, Xset, phase_norm]

/-- The Laurent generator for u (i=0), g₁ (i=1), or g₂ (i=2).
Negative winding encodes the conjugate, not a new independent variable. -/
def mode (i : Fin 3) (q : ℤ) : FaceAlgebra :=
  AddMonoidAlgebra.single (0, Pi.single i q) 1

def realMode (i : Fin 3) : FaceAlgebra := (1/2 : ℂ) • (mode i 1 + mode i (-1))
def imagMode (i : Fin 3) : FaceAlgebra := (1/(2*Complex.I) : ℂ) • (mode i 1 - mode i (-1))

def coordinate : Var → FaceAlgebra
  | .xi => AddMonoidAlgebra.single (1, 0) 1
  | .ctl i => if i = 0 then realMode 0 else imagMode 0
  | .st i => ![realMode 1, imagMode 1, 0, 0, realMode 2, imagMode 2, 0, 0] i

def restriction : ComplexPoly →ₐ[ℂ] FaceAlgebra := aeval coordinate

theorem evaluate_mode (t : Parameters) (i : Fin 3) (q : ℤ) :
    evaluate t (mode i q) = Complex.exp ((q : ℂ) * (t.2 i : ℂ) * Complex.I) := by
  simp [evaluate, mode, indexCharacter, character, exponent,
    Pi.single_apply, ite_mul, Finset.sum_ite_eq']

theorem evaluate_realMode (t : Parameters) (i : Fin 3) :
    evaluate t (realMode i) = ((phase (t.2 i)).re : ℂ) := by
  simp only [realMode, map_smul, map_add, evaluate_mode]
  rw [Complex.re_eq_add_conj]
  simp [phase, ← Complex.exp_conj, mul_comm, div_eq_mul_inv]

theorem evaluate_imagMode (t : Parameters) (i : Fin 3) :
    evaluate t (imagMode i) = ((phase (t.2 i)).im : ℂ) := by
  simp only [imagMode, map_smul, map_sub, evaluate_mode]
  rw [Complex.im_eq_sub_conj]
  simp [phase, ← Complex.exp_conj, mul_comm, div_eq_mul_inv]

theorem evaluate_coordinate (t : Parameters) (v : Var) :
    evaluate t (coordinate v) =
      (pt (Real.exp t.1) (faceState t) (phase (t.2 0)) v : ℂ) := by
  cases v with
  | xi => simp [coordinate, evaluate, indexCharacter, character, exponent, pt, Complex.ofReal_exp]
  | ctl i => fin_cases i <;> simp [coordinate, evaluate_realMode, evaluate_imagMode, pt]
  | st i => fin_cases i <;>
      simp [coordinate, evaluate_realMode, evaluate_imagMode, pt, faceState, mkState]

theorem evaluate_restriction (t : Parameters) (p : ComplexPoly) :
    evaluate t (restriction p) =
      eval (fun v => (pt (Real.exp t.1) (faceState t) (phase (t.2 0)) v : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restriction, evaluate, indexCharacter, character, exponent]
  | add p q hp hq => simp_all
  | mul_X p v hp => simp_all [restriction, evaluate_coordinate]

/-- Physical face vanishing implies zero formal restriction. Only a subset
of the physical face (ξ positive) is needed for the coefficient argument. -/
theorem restriction_zero_of_physical_vanishing (p : ComplexPoly)
    (hp : ∀ ξ x, x ∈ Fface → ∀ u : ℂ, ‖u‖ = 1 →
      eval (fun v => (pt ξ x u v : ℂ)) p = 0) : restriction p = 0 := by
  apply eq_zero_of_evaluate
  intro t
  rw [evaluate_restriction]
  exact hp _ _ (faceState_mem t) _ (phase_norm _)

/-- The existing stationary face-vanishing theorem now yields formal zero
for each actual real SOS factor, after extending its coefficients to ℂ. -/
theorem stationary_factors_restriction_zero {W : StatePoly} {n : ℕ} {h : Fin n → Poly}
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) (l : Fin n) :
    restriction (MvPolynomial.map Complex.ofRealHom (h l)) = 0 := by
  apply restriction_zero_of_physical_vanishing
  intro ξ x hx u hu
  have hz := (sos_factors_vanish_on_face hdrift hx hu ξ).2 l
  exact (MvPolynomial.map_eval Complex.ofRealHom (pt ξ x u) (h l)).symm.trans (by simp [hz])

/-- Normalization-ideal terms do not change the formal face restriction. -/
theorem normIdeal_restriction_zero {p : Poly} (hp : p ∈ normIdeal) :
    restriction (MvPolynomial.map Complex.ofRealHom p) = 0 := by
  apply restriction_zero_of_physical_vanishing
  intro ξ x hx u hu
  have hz := eval_eq_zero_of_mem_normIdeal (ξ := ξ) hx.1 hu hp
  exact (MvPolynomial.map_eval Complex.ofRealHom (pt ξ x u) p).symm.trans (by simp [hz])

/-- Connect the actual Laurent restriction to the finite-column kernel theorem.
The finite character list must be injective: unrelated characters cannot be
merged. The hypotheses on z and m specify their computed restrictions, not an
assumption that physical vanishing implies coefficient vanishing. -/
theorem mem_reduced_span_of_restriction_zero {χ ι : Type*}
    [Fintype χ] [DecidableEq χ] [Fintype ι]
    (keys : χ → Index) (hkeys : Function.Injective keys)
    (z : ι → ComplexPoly) (m : χ → ℕ → ComplexPoly) (n : χ → ℕ)
    (hz : ∀ i, restriction (z i) = 0)
    (hm : ∀ c i, i ≤ n c → restriction (m c i) = AddMonoidAlgebra.single (keys c) 1)
    (p : ComplexPoly)
    (hp : p ∈ Submodule.span ℂ (Set.range (ReducedBasis.originalColumn z m n)))
    (hzero : restriction p = 0) :
    p ∈ Submodule.span ℂ (Set.range (ReducedBasis.reducedColumn (K := ℂ) z m n)) := by
  let T : ComplexPoly →ₗ[ℂ] (χ →₀ ℂ) :=
    (Finsupp.lcomapDomain keys hkeys).comp restriction.toLinearMap
  have hz' (i : ι) : T (z i) = 0 := by
    change (Finsupp.lcomapDomain (R := ℂ) keys hkeys) (restriction (z i)) = 0
    rw [hz, map_zero]
  have hm' (c : χ) (i : ℕ) (hi : i ≤ n c) : T (m c i) = Finsupp.single c 1 := by
    change (Finsupp.lcomapDomain (R := ℂ) keys hkeys) (restriction (m c i)) = _
    rw [hm c i hi]
    exact Finsupp.comapDomain_single keys c 1 hkeys.injOn
  rw [← ReducedBasis.face_span_eq T z m n hz' hm']
  refine ⟨hp, ?_⟩
  change (Finsupp.lcomapDomain (R := ℂ) keys hkeys) (restriction p) = 0
  rw [hzero, map_zero]

/-- A stationary SOS factor belongs to the actual prescribed face-column span
once its monomial expansion and restriction groups are supplied. Column degree
control is provided separately by `ReducedBasis.reducedColumn_degree`.
No general completeness assumptions are needed for this transfer. -/
theorem stationary_factor_mem_reduced_span {χ ι : Type*}
    [Fintype χ] [DecidableEq χ] [Fintype ι]
    (keys : χ → Index) (hkeys : Function.Injective keys)
    (z : ι → ComplexPoly) (m : χ → ℕ → ComplexPoly) (n : χ → ℕ)
    (hz : ∀ i, restriction (z i) = 0)
    (hm : ∀ c i, i ≤ n c → restriction (m c i) = AddMonoidAlgebra.single (keys c) 1)
    {W : StatePoly} {N : ℕ} {h : Fin N → Poly}
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) (l : Fin N)
    (hp : MvPolynomial.map Complex.ofRealHom (h l) ∈
      Submodule.span ℂ (Set.range (ReducedBasis.originalColumn z m n))) :
    MvPolynomial.map Complex.ofRealHom (h l) ∈
      Submodule.span ℂ (Set.range (ReducedBasis.reducedColumn (K := ℂ) z m n)) :=
  mem_reduced_span_of_restriction_zero keys hkeys z m n hz hm _ hp
    (stationary_factors_restriction_zero hdrift l)

end CZExposure.FaceRestriction
