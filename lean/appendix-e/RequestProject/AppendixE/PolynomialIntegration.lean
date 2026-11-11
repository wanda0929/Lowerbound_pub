module

public import RequestProject.AppendixE.PolynomialSymmetry

/-!
# Coefficientwise integration of uniformly degree-bounded polynomials

The integral is a finite polynomial, not an integral in an unspecified topology
on the infinite-dimensional polynomial ring. Every real linear functional
commutes with this integral; in particular evaluation and directional derivatives
do. The degree bound is preserved, including when coefficients cancel.
-/

@[expose] public section
noncomputable section

namespace CZExposure.PolynomialIntegration

open MvPolynomial MeasureTheory

variable {n : ℕ} {A : Type*} [MeasurableSpace A]

/-- A finite set containing every exponent of a polynomial of total degree ≤ d. -/
def exponentBox (n d : ℕ) : Finset (Fin n →₀ ℕ) :=
  Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => d))

theorem support_subset_exponentBox (p : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hp : p.totalDegree ≤ d) : p.support ⊆ exponentBox n d := by
  intro e he
  simp only [exponentBox, Finset.mem_Iic]
  intro i
  change e i ≤ d
  exact ((degreeOf_le_iff.mp (degreeOf_le_totalDegree p i)) e he).trans hp

theorem sum_exponentBox (p : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    (∑ e ∈ exponentBox n d, monomial e (coeff e p)) = p := by
  classical
  calc _ = ∑ e ∈ p.support, monomial e (coeff e p) := by
         symm
         apply Finset.sum_subset (support_subset_exponentBox p hp)
         intro e _ he
         simp [notMem_support_iff.mp he]
       _ = p := support_sum_monomial_coeff p

/-- Integrate each coefficient in a fixed finite exponent box. -/
def polynomialIntegral (d : ℕ) (μ : Measure A) (p : A → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ e ∈ exponentBox n d, monomial e (∫ a, coeff e (p a) ∂μ)

theorem polynomialIntegral_degree (d : ℕ) (μ : Measure A)
    (p : A → MvPolynomial (Fin n) ℝ) (hp : ∀ a, (p a).totalDegree ≤ d) :
    (polynomialIntegral d μ p).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro e _
  by_cases he : e.sum (fun _ k => k) ≤ d
  · exact (totalDegree_monomial_le _ _).trans he
  · have hz : ∀ a, coeff e (p a) = 0 := fun a =>
      coeff_eq_zero_of_totalDegree_lt ((hp a).trans_lt (Nat.lt_of_not_ge he))
    simp [hz]

theorem linearMap_monomial (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (e : Fin n →₀ ℕ) (c : ℝ) : L (monomial e c) = c * L (monomial e 1) := by
  conv_lhs => rw [show monomial e c = c • monomial e (1 : ℝ) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact L.map_smul c _

theorem linearMap_eq_sum (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (p : MvPolynomial (Fin n) ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    L p = ∑ e ∈ exponentBox n d, coeff e p * L (monomial e 1) := by
  conv_lhs => rw [← sum_exponentBox p hp]
  rw [map_sum]
  exact Finset.sum_congr rfl fun e _ => linearMap_monomial L e _

theorem integrable_linearMap (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    {d : ℕ} {μ : Measure A} {p : A → MvPolynomial (Fin n) ℝ}
    (hp : ∀ a, (p a).totalDegree ≤ d)
    (hc : ∀ e, Integrable (fun a => coeff e (p a)) μ) :
    Integrable (fun a => L (p a)) μ := by
  simp_rw [linearMap_eq_sum L _ (hp _)]
  exact integrable_finset_sum _ fun e _ => (hc e).mul_const _

/-- No differentiation-under-the-integral hypothesis is needed: directional
derivatives at a fixed point are linear functionals of the polynomial. -/
theorem linearMap_polynomialIntegral (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    {d : ℕ} {μ : Measure A} {p : A → MvPolynomial (Fin n) ℝ}
    (hp : ∀ a, (p a).totalDegree ≤ d)
    (hc : ∀ e, Integrable (fun a => coeff e (p a)) μ) :
    L (polynomialIntegral d μ p) = ∫ a, L (p a) ∂μ := by
  simp only [polynomialIntegral, map_sum]
  simp_rw [linearMap_eq_sum L _ (hp _)]
  rw [integral_finset_sum _ (fun e _ => (hc e).mul_const _)]
  apply Finset.sum_congr rfl
  intro e _
  rw [linearMap_monomial, integral_mul_const]

section Continuity

variable {B : Type*} [TopologicalSpace B]

theorem continuous_coeff_mul {p q : B → MvPolynomial (Fin n) ℝ}
    (hp : ∀ e, Continuous (fun a => coeff e (p a)))
    (hq : ∀ e, Continuous (fun a => coeff e (q a))) (e : Fin n →₀ ℕ) :
    Continuous (fun a => coeff e (p a * q a)) := by
  classical
  simp only [coeff_mul]
  exact continuous_finset_sum _ fun i _ => (hp i.1).mul (hq i.2)

/-- Continuous coefficients of the substitutions give continuous coefficients
of every substituted polynomial. -/
theorem continuous_coeff_aeval {m : ℕ} (P : MvPolynomial (Fin m) ℝ)
    (s : B → Fin m → MvPolynomial (Fin n) ℝ)
    (hs : ∀ i e, Continuous (fun a => coeff e (s a i))) :
    ∀ e, Continuous (fun a => coeff e (aeval (s a) P)) := by
  induction P using MvPolynomial.induction_on with
  | C c => intro e; simp only [aeval_C]; exact continuous_const
  | add p q hp hq => intro e; simp only [map_add]; exact (hp e).add (hq e)
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    exact continuous_coeff_mul hp (hs i)

end Continuity

end CZExposure.PolynomialIntegration
