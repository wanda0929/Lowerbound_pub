module
public import RequestProject.AppendixE.BernsteinDerivatives
public import RequestProject.AppendixE.C1ApproximationInput

/-! Affine transport of simultaneous Bernstein C¹ approximation to a closed box. -/
@[expose] public section
noncomputable section
namespace CZExposure.BernsteinC1
open MvPolynomial

def affineSubst {d : ℕ} (a b : ℝ) : MvPolynomial (Fin d) ℝ →+* MvPolynomial (Fin d) ℝ :=
  eval₂Hom C (fun i => C a * X i + C b)

theorem eval_affineSubst {d : ℕ} (a b : ℝ) (P : MvPolynomial (Fin d) ℝ)
    (x : Fin d → ℝ) : eval x (affineSubst a b P) = eval (fun j => a*x j+b) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [affineSubst]
  | add P Q hP hQ => simp_all
  | mul_X P j hP => simp_all [affineSubst]

theorem pderiv_affineSubst {d : ℕ} (a b : ℝ) (P : MvPolynomial (Fin d) ℝ)
    (i : Fin d) : pderiv i (affineSubst a b P) = C a * affineSubst a b (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [affineSubst]
  | add P Q hP hQ => simp [hP, hQ, mul_add]
  | mul_X P j hP =>
    simp only [map_mul, Derivation.leibniz, hP]
    by_cases hj : j = i
    · subst j
      simp [affineSubst, Derivation.leibniz]
      ring
    · simp [affineSubst, Derivation.leibniz, pderiv_X_of_ne hj]
      ring

theorem partial_affine {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (x : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun y => f (fun j => a*y j+b)) x (Pi.single i 1) =
      a * fderiv ℝ f (fun j => a*x j+b) (Pi.single i 1) := by
  have hg : HasFDerivAt (fun y : Fin d → ℝ => a • y + (fun _ => b))
      (a • ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    ((hasFDerivAt_id x).const_smul a).add_const (fun _ => b)
  have hh := (hf.differentiable (by decide) (fun j => a*x j+b)).hasFDerivAt.comp x hg
  have he := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hh.fderiv
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul,
    smul_eq_mul, Pi.smul_apply, Pi.add_apply] using he

end CZExposure.BernsteinC1

namespace CZExposure.PolynomialGeometry
open MvPolynomial BernsteinC1

/-- The former generic input is a theorem: one polynomial approximates both
values and all coordinate derivatives on the whole closed box. -/
theorem boxC1PolynomialApproximation : BoxC1PolynomialApproximation := by
  intro d _ R hR f hf δ hδ
  let g : (Fin d → ℝ) → ℝ := fun y => f (fun j => (2*R)*y j + (-R))
  have hg : ContDiff ℝ 1 g := hf.comp (by fun_prop)
  have hscale : 0 < 2*R := by positivity
  have hε : 0 < min δ (2*R*δ) := lt_min hδ (mul_pos hscale hδ)
  obtain ⟨P, hv, hp⟩ := exists_cube_C1 g hg hε
  let Q := affineSubst (1/(2*R)) (1/2) P
  suffices h : ∀ x ∈ coordinateBox d R,
      |eval x Q - f x| ≤ δ ∧ ∀ i, |eval x (pderiv i Q) - fderiv ℝ f x (Pi.single i 1)| ≤ δ by
    exact ⟨Q, fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  intro x hx
  let y : Cube d := fun j => ⟨x j / (2*R) + 1/2, by
    have hj := abs_le.mp (hx j)
    constructor
    · have := (le_div_iff₀ hscale).mpr (show (-1/2:ℝ)*(2*R) ≤ x j by linarith)
      linarith
    · have := (div_le_iff₀ hscale).mpr (show x j ≤ (1/2:ℝ)*(2*R) by linarith)
      linarith⟩
  have hy : (fun j => (2*R)*realPoint y j + (-R)) = x := by
    funext j
    dsimp [realPoint, y]
    field_simp
    ring
  have he : (fun j => 1/(2*R)*x j+1/2) = realPoint y := by
    funext j; dsimp [realPoint, y]; ring
  dsimp only [Q]
  constructor
  · rw [eval_affineSubst, he]
    have hvy := hv y
    change |eval (realPoint y) P - f (fun j => (2*R)*realPoint y j + (-R))| ≤ _ at hvy
    rw [hy] at hvy
    exact hvy.trans (min_le_left _ _)
  · intro i
    have hc : partialValue g i y = (2*R)*fderiv ℝ f x (Pi.single i 1) := by
      unfold partialValue g
      rw [partial_affine f hf, hy]
    have hpy := (hp y i).trans (min_le_right δ (2*R*δ))
    rw [hc] at hpy
    rw [pderiv_affineSubst, eval_mul, eval_C, eval_affineSubst, he]
    have heq : 1/(2*R)*eval (realPoint y) (pderiv i P) - fderiv ℝ f x (Pi.single i 1) =
        (eval (realPoint y) (pderiv i P) - (2*R)*fderiv ℝ f x (Pi.single i 1))/(2*R) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hscale]
    exact (div_le_iff₀ hscale).mpr (by nlinarith [hpy])

end CZExposure.PolynomialGeometry
