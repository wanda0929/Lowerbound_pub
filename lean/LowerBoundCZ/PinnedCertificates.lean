import LowerBoundCZ.CertificateContracts
import LowerBoundCZ.CertificateData
import LowerBoundCZ.GramBridge
import LowerBoundCZ.PotentialBasis
import LowerBoundCZ.UpperAD
import LowerBoundCZ.UpperWitness
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Concrete payloads from the pinned publication archive. Numerical validity
is an explicit hypothesis, never an axiom or an assertion of the final bound.
The external decoder and the remaining proof obligations are documented in
CertificateContracts.md. -/
noncomputable section
namespace LowerBoundCZ.Certification.Pinned
open CZExposure MvPolynomial
set_option maxRecDepth 2000
set_option maxHeartbeats 0

def partition : ExposurePartition where
  J := 5
  J_pos := by norm_num
  a := fun j => match j with
    | 0 => 0 | 1 => 1/36 | 2 => 1/3 | 3 => 2/3 | 4 => 35/36 | _ => 1
  a_zero := rfl
  a_last := rfl
  a_lt := by
    intro j hj
    interval_cases j <;> norm_num

/-- The source identity is c + A^T lambda + n - Gram = 0, hence V=-sum lambda*m. -/
def order7 : Lower.Payload where
  partition := partition
  ceiling := 2935887/1000000
  order := 7
  offset := realScalar CertificateData.offset
  potential := fun j => -∑ i : Fin 776,
    C (realScalar (CertificateData.multipliers[j*776+i.val]?.getD (0, 0))) *
      basisPolynomial (CertificateData.basis[i.val]?.getD (0, #[], #[]))
  target := 5861/2000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem order7_basis_properties : ∀ i : Fin 776,
    let b := CertificateData.basis[i.val]?.getD default
    degreeBound b ≤ 13 ∧ Balanced b := by
  decide

theorem order7_degree (j : ℕ) : (order7.potential j).totalDegree ≤ 13 := by
  exact sumBasis_degree _ _ (fun i => (order7_basis_properties i).1)

theorem order7_invariant (j : ℕ) (ξ : ℝ) :
    IsGInvariant (fun x => evalCell ξ x (order7.potential j)) := by
  exact sumBasis_invariant _ _ (fun i => (order7_basis_properties i).2) ξ

def initialSupport : Finset (Fin 776) := {0, 3, 11, 28, 61}

set_option maxRecDepth 100000 in
theorem order7_initial_support : ∀ i : Fin 776,
    initialWeight (CertificateData.basis[i.val]?.getD default) =
      if i ∈ initialSupport then 1 else 0 := by
  decide

private theorem initialSupport_sum (f : Fin 776 → ℚ) :
    (∑ i ∈ initialSupport, f i) = f 0 + f 3 + f 11 + f 28 + f 61 := by
  simp [initialSupport, Finset.sum_insert, add_assoc]

theorem order7_initial_coefficients :
    (∑ i ∈ initialSupport, (CertificateData.multipliers[i.val]?.getD (0, 0)).1) =
      CertificateData.offset.1 + 5861/2000 ∧
    (∑ i ∈ initialSupport, (CertificateData.multipliers[i.val]?.getD (0, 0)).2) =
      CertificateData.offset.2 := by
  rw [initialSupport_sum, initialSupport_sum]
  unfold CertificateData.multipliers
  simp only [Array.append_assoc]
  repeat' rw [Array.getElem?_append_left]
  -- `change` checks these five entries against the pinned array definition;
  -- `norm_num` proves the rational arithmetic without unfolding Rat's implementation.
  · with_unfolding_all change
      (-141967577028892456493 / 1125899906842624000 +
        401219252457778643 / 4503599627370496 + 62410133906022921 / 4503599627370496 +
        -8825898179830347 / 9007199254740992 + 6391198173464225 / 2251799813685248 : ℚ) =
        CertificateData.offset.1 + 5861/2000 ∧
        (0/1+0/1+0/1+0/1+0/1 : ℚ) = CertificateData.offset.2
    norm_num [CertificateData.offset]
  all_goals decide

theorem order7_objective :
    -order7.offset - evalCell 0 x0 (order7.potential 0) = order7.target := by
  have h := sumBasis_objective
    (fun i : Fin 776 => CertificateData.multipliers[0*776+i.val]?.getD (0, 0))
    (fun i => CertificateData.basis[i.val]?.getD default)
    initialSupport CertificateData.offset (5861/2000)
    order7_initial_support (by
      simpa only [Nat.zero_mul, Nat.zero_add] using order7_initial_coefficients)
  exact h.trans (by norm_num [order7])

private def matrixMap (a : Array ℚ) : Upper.LinearMap :=
  (Matrix.toLin' (fun i j : Fin 5 => (a[i.val*5+j.val]?.getD 0 : ℝ))).toContinuousLinearMap

/-- Exact rational box and all 12,672 phases, not rounded summary numbers. -/
def upper : Upper.Payload where
  fixed := fun i => (CertificateData.phases[i.val]?.getD 0 : ℝ)
  center := fun i => (CertificateData.center[i.val]?.getD 0 : ℝ)
  radius := (CertificateData.radius : ℝ)
  inverse := matrixMap CertificateData.inverse
  jacobians := {A | ∀ i j : Fin 5,
    (CertificateData.jacobianLower[i.val*5+j.val]?.getD 0 : ℝ) ≤ A (Pi.single j 1) i ∧
    A (Pi.single j 1) i ≤ (CertificateData.jacobianUpper[i.val*5+j.val]?.getD 0 : ℝ)}
  contraction := (CertificateData.contraction : ℝ)

/-- First-tier external obligation specialized to the actual order-7 payload.
No proof of this input is asserted by this module. -/
abbrev Order7Checks : Prop := Lower.Checks order7
abbrev UpperChecks : Prop := Upper.AD.Enclosures upper

/-- Numerical enclosures imply the physical upper bound; the root and pulse
are constructed in Lean, not supplied by this hypothesis. -/
theorem upper_lab_bound (h : UpperChecks) :
    labCstar < (LowerBoundCZ.upperEndpoint : EReal) :=
  h.analyticChecks.lab_upper

theorem order7_lab_lower (h : Order7Checks) : (5861/2000 : EReal) ≤ labCstar := by
  simpa [order7] using h.lab_lower

/-- Source Gram PSD and coefficient identities now imply the concrete
feasibility predicate; feasibility itself is no longer an external input. -/
theorem order7_checks_of_grams (A : GramBridge.Archive order7) (h : GramBridge.MatrixChecks A) :
    Order7Checks where
  ceiling_pos := by norm_num [order7]
  target_le_ceiling := by norm_num [order7]
  order_pos := by norm_num [order7]
  feasible := (show GramBridge.Checks A from {
    toMatrixChecks := h
    degree := fun j _ => order7_degree j
    invariant := fun j _ ξ => order7_invariant j ξ }).feasible
  objective := order7_objective

theorem order7_lab_lower_of_grams (A : GramBridge.Archive order7) (h : GramBridge.MatrixChecks A) :
    (5861/2000 : EReal) ≤ labCstar :=
  order7_lab_lower (order7_checks_of_grams A h)

/-- First-tier base window for one and the same laboratory integral model.
The slack-strengthened lower endpoint is a separate result, not claimed here. -/
theorem lab_window (A : GramBridge.Archive order7) (hl : GramBridge.MatrixChecks A)
    (hu : UpperChecks) :
    (5861/2000 : EReal) ≤ labCstar ∧ labCstar < (LowerBoundCZ.upperEndpoint : EReal) :=
  ⟨order7_lab_lower_of_grams A hl, upper_lab_bound hu⟩

end LowerBoundCZ.Certification.Pinned
