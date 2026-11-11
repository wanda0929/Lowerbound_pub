import LowerBoundCZ.GramBridge
import LowerBoundCZ.SlackCalculus
import LowerBoundCZ.PinnedCertificates
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Gram allocations imply local physical slack. All numerical hypotheses
are matrix order, scalar budgets, and polynomial identities/signs. In
particular no pointwise or trajectory inequality is a certificate input. -/
noncomputable section
namespace LowerBoundCZ.Certification.Slack
open CZExposure MvPolynomial QuotientNormalForm QuotientCertificate SymmetryGram
open scoped Matrix

theorem gram_value_mono {ι : Type*} [Fintype ι] {Q R : Matrix ι ι ℝ}
    (h : (Q - R).PosSemidef) (z : ι → ℂ) :
    (value (R.map Complex.ofReal) z).re ≤ (value (Q.map Complex.ofReal) z).re := by
  have hn := ConcreteStationary.value_re_nonneg h z
  have he : value ((Q - R).map Complex.ofReal) z =
      value (Q.map Complex.ofReal) z - value (R.map Complex.ofReal) z := by
    simp [value, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [he, Complex.sub_re] at hn
  linarith

/-- Weights are budgeted per original block, never independently per
projection. An unused fraction is harmless because the original block is PSD. -/
theorem gram_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι ι ℝ) (R : κ → Matrix ι ι ℝ) (w : κ → ℝ)
    (hQ : Q.PosSemidef) (hR : ∀ k, (Q - R k).PosSemidef)
    (hw : ∀ k, 0 ≤ w k) (hbudget : ∑ k, w k ≤ 1) (z : ι → ℂ) :
    (∑ k, w k * (value ((R k).map Complex.ofReal) z).re) ≤
      (value (Q.map Complex.ofReal) z).re := by
  calc
    _ ≤ ∑ k, w k * (value (Q.map Complex.ofReal) z).re :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (gram_value_mono (hR k) z) (hw k))
    _ = (∑ k, w k) * (value (Q.map Complex.ofReal) z).re := (Finset.sum_mul ..).symm
    _ ≤ 1 * (value (Q.map Complex.ofReal) z).re :=
      mul_le_mul_of_nonneg_right hbudget (ConcreteStationary.value_re_nonneg hQ z)
    _ = _ := one_mul _

/-- All four localizers used by the original, unmerged archive. Keeping
them avoids confusing source block IDs with the merged cone representation. -/
inductive Localizer where
  | one | xi | oneMinusXi | xiOneMinusXi
  deriving DecidableEq

def Localizer.poly : Localizer → MixedPoly
  | .one => 1 | .xi => X 0 | .oneMinusXi => 1-X 0
  | .xiOneMinusXi => X 0 * (1-X 0)

theorem Localizer.eval_nonneg (l : Localizer) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (x : State) (u : ℂ) :
    0 ≤ (eval (mixedPoint ξ x u) l.poly).re := by
  cases l <;> simp [Localizer.poly, mixedPoint, Complex.mul_re]
  · exact hξ.1
  · linarith [hξ.2]
  · exact mul_nonneg hξ.1 (sub_nonneg.mpr hξ.2)

theorem Localizer.eval_im (l : Localizer) (ξ : ℝ) (x : State) (u : ℂ) :
    (eval (mixedPoint ξ x u) l.poly).im = 0 := by
  cases l <;> simp [Localizer.poly, mixedPoint, Complex.mul_im]

/-- Source columns already include the archive's phases and facial map.
`R` is the reduced matrix embedded back into the *original* row coordinates;
matrix order is checked there, including exact zero rows. -/
structure AllocatedBlock where
  size : ℕ
  source : Fin size → MixedPoly
  Q : Matrix (Fin size) (Fin size) ℝ
  localizer : Localizer
  count : ℕ
  R : Fin count → Matrix (Fin size) (Fin size) ℝ
  weight : Fin count → ℚ

def AllocatedBlock.original (b : AllocatedBlock) : MixedPoly :=
  b.localizer.poly * gram (b.Q.map Complex.ofReal) b.source

def AllocatedBlock.allocated (b : AllocatedBlock) : MixedPoly :=
  b.localizer.poly * ∑ k, C (b.weight k : ℂ) * gram ((b.R k).map Complex.ofReal) b.source

structure AllocatedBlock.Checks (b : AllocatedBlock) : Prop where
  psd : b.Q.PosSemidef
  domination : ∀ k, (b.Q - b.R k).PosSemidef
  nonneg : ∀ k, 0 ≤ b.weight k
  budget : ∑ k, b.weight k ≤ 1

theorem AllocatedBlock.eval_le (b : AllocatedBlock) (h : b.Checks)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (x : State) (u : ℂ) :
    (eval (mixedPoint ξ x u) b.allocated).re ≤
      (eval (mixedPoint ξ x u) b.original).re := by
  have hb := gram_budget b.Q b.R (fun k => (b.weight k : ℝ)) h.psd h.domination
    (fun k => Rat.cast_nonneg.mpr (h.nonneg k)) (by
      simpa only [Rat.cast_sum, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h.budget)
    (fun i => eval (mixedPoint ξ x u) (b.source i))
  simpa [AllocatedBlock.allocated, AllocatedBlock.original, eval_gram,
    Complex.mul_re, b.localizer.eval_im] using
    mul_le_mul_of_nonneg_left hb (b.localizer.eval_nonneg hξ x u)

/-- Polynomial Bernstein factors, with unrestricted real endpoints.
Only the normalized coordinate is required to lie in [0,1] on evaluation. -/
def bernsteinMixed (n k : ℕ) (y : MixedPoly) : MixedPoly :=
  C (n.choose k : ℂ) * y^k * (1-y)^(n-k)

theorem bernsteinMixed_nonneg (n k : ℕ) (y : MixedPoly) (z : Fin 11 → ℂ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : eval z y = (t : ℂ)) :
    0 ≤ (eval z (bernsteinMixed n k y)).re := by
  simp only [bernsteinMixed, map_mul, map_pow, map_sub, eval_C, map_one, hy]
  norm_cast
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)

/-- Tensor coefficients are checked after subtracting profile times cost.
The coordinates encode the actual exposure/population rectangle. -/
def tensorMixed (degree : Fin 3 → ℕ)
    (coeff : ((i : Fin 3) → Fin (degree i + 1)) → ℚ)
    (coord : Fin 3 → MixedPoly) : MixedPoly :=
  ∑ k, C (coeff k : ℂ) * ∏ i, bernsteinMixed (degree i) (k i) (coord i)

theorem tensorMixed_nonneg (degree : Fin 3 → ℕ)
    (coeff : ((i : Fin 3) → Fin (degree i + 1)) → ℚ)
    (hc : ∀ k, 0 ≤ coeff k) (coord : Fin 3 → MixedPoly)
    (z : Fin 11 → ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ i, eval z (coord i) = (t i : ℂ)) :
    0 ≤ (eval z (tensorMixed degree coeff coord)).re := by
  have hb (i : Fin 3) (k : ℕ) : eval z (bernsteinMixed (degree i) k (coord i)) =
      ((degree i).choose k * t i ^ k * (1-t i)^ (degree i-k) : ℝ) := by
    simp [bernsteinMixed, he]
  simp only [tensorMixed, map_sum, map_mul, eval_C, map_prod, hb]
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_ratCast, ← Complex.ofReal_mul,
    Complex.re_sum, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (Rat.cast_nonneg.mpr (hc k))
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ht i).1 _))
    (pow_nonneg (sub_nonneg.mpr (ht i).2) _)

/-- Two finite polynomial identities connect the original drift and the
allocated residual to the same source blocks. Equality is modulo the proved
normalization ideal, not an assumed physical inequality. -/
theorem allocation_local_slack {n : ℕ} (blocks : Fin n → AllocatedBlock)
    (hb : ∀ i, (blocks i).Checks) (drift profile : MixedPoly)
    (hsource : drift - ∑ i, (blocks i).original ∈ relations)
    (degree : Fin 3 → ℕ)
    (coeff : ((i : Fin 3) → Fin (degree i + 1)) → ℚ)
    (hc : ∀ k, 0 ≤ coeff k) (coord : Fin 3 → MixedPoly)
    (hresidual : (∑ i, (blocks i).allocated) - profile -
      tensorMixed degree coeff coord ∈ relations)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ = 1)
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ i, eval (mixedPoint ξ x u) (coord i) = (t i : ℂ)) :
    (eval (mixedPoint ξ x u) profile).re ≤ (eval (mixedPoint ξ x u) drift).re := by
  have hs := congrArg Complex.re (eval_relations_zero hsource ξ hx hu)
  have hr := congrArg Complex.re (eval_relations_zero hresidual ξ hx hu)
  simp only [map_sub, map_sum, Complex.sub_re, Complex.re_sum, Complex.zero_re] at hs hr
  have htensor := tensorMixed_nonneg degree coeff hc coord _ t ht he
  have halloc := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (blocks i).eval_le (hb i) hξ x u)
  linarith

/-- The source checker uses degree (14,7,7), ordered as exposure,p₁,p₂. -/
def allocationDegree : Fin 3 → ℕ := ![14, 7, 7]

/-- A decoded rectangle of the pinned order-seven allocation certificate.
The decoder supplies data, not a proof. Each region has its own block budget. -/
structure AllocationRegion where
  cell : Fin 5
  lo : Fin 3 → ℚ
  hi : Fin 3 → ℚ
  delta : Fin 15 → ℚ
  blockCount : ℕ
  blocks : Fin blockCount → AllocatedBlock
  residual : ((i : Fin 3) → Fin (allocationDegree i + 1)) → ℚ

def populationCoordinates : Fin 3 → MixedPoly := ![X 0, X 5 * X 6, X 9 * X 10]

def AllocationRegion.coord (r : AllocationRegion) (i : Fin 3) : MixedPoly :=
  C ((r.hi i - r.lo i : ℚ)⁻¹ : ℂ) * (populationCoordinates i - C (r.lo i : ℂ))

def AllocationRegion.profile (r : AllocationRegion) : MixedPoly :=
  ∑ k : Fin 15, C (r.delta k : ℂ) * bernsteinMixed 14 k (r.coord 0)

def AllocationRegion.rate (r : AllocationRegion) (ξ : ℝ) : ℝ :=
  ∑ k : Fin 15, (r.delta k : ℝ) * (Nat.choose 14 k : ℝ) *
    ((ξ-r.lo 0)/(r.hi 0-r.lo 0))^k.val *
      (1-(ξ-r.lo 0)/(r.hi 0-r.lo 0))^(14-k.val)

def AllocationRegion.drift (r : AllocationRegion) : MixedPoly :=
  embed (cpoly - cellOp
    (1/(Pinned.order7.ceiling * Pinned.order7.partition.width r.cell.val))
    (Pinned.order7.potential r.cell.val))

structure AllocationRegion.Checks (r : AllocationRegion) : Prop where
  widths : ∀ i, r.lo i < r.hi i
  blocks : ∀ i, (r.blocks i).Checks
  source : r.drift - ∑ i, (r.blocks i).original ∈ relations
  residual_identity : (∑ i, (r.blocks i).allocated) -
    r.profile * embed cpoly -
      tensorMixed allocationDegree r.residual r.coord ∈ relations
  residual_nonneg : ∀ k, 0 ≤ r.residual k

theorem AllocationRegion.eval_coord (r : AllocationRegion) (ξ : ℝ) (x : State)
    (u : ℂ) (i : Fin 3) :
    eval (mixedPoint ξ x u) (r.coord i) =
      ((![ξ, ‖r1 x‖^2, ‖r2 x‖^2] i - (r.lo i : ℝ)) /
        ((r.hi i : ℝ) - r.lo i) : ℝ) := by
  have hp : eval (mixedPoint ξ x u) (populationCoordinates i) =
      (![ξ, ‖r1 x‖^2, ‖r2 x‖^2] i : ℝ) := by
    fin_cases i <;> simp [populationCoordinates, mixedPoint, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  simp [AllocationRegion.coord, hp, div_eq_mul_inv, mul_comm]

theorem AllocationRegion.eval_profile (r : AllocationRegion) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) r.profile = (r.rate ξ : ℂ) := by
  simp [AllocationRegion.profile, bernsteinMixed, r.eval_coord, AllocationRegion.rate,
    mul_assoc]

/-- The local conclusion is the actual pinned potential's physical drift,
with the paper's asymmetric population cost. Box membership is a domain
condition; the slack inequality itself follows from finite algebraic checks. -/
theorem AllocationRegion.local_slack (r : AllocationRegion) (h : r.Checks)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ = 1)
    (hbox : ∀ i, ![ξ, ‖r1 x‖^2, ‖r2 x‖^2] i ∈
      Set.Icc (r.lo i : ℝ) (r.hi i : ℝ)) :
    r.rate ξ * cost x ≤ cost x - eval (pt ξ x u)
      (cellOp (1/(Pinned.order7.ceiling * Pinned.order7.partition.width r.cell.val))
        (Pinned.order7.potential r.cell.val)) := by
  have ht (i : Fin 3) :
      (![ξ, ‖r1 x‖^2, ‖r2 x‖^2] i - (r.lo i : ℝ)) /
        ((r.hi i : ℝ) - r.lo i) ∈ Set.Icc (0 : ℝ) 1 := by
    have hw : (0 : ℝ) < (r.hi i : ℝ) - r.lo i := by exact_mod_cast sub_pos.mpr (h.widths i)
    exact ⟨div_nonneg (sub_nonneg.mpr (hbox i).1) hw.le,
      (div_le_one hw).mpr (sub_le_sub_right (hbox i).2 _)⟩
  have hl := allocation_local_slack r.blocks h.blocks r.drift
    (r.profile * embed cpoly) h.source allocationDegree r.residual
    h.residual_nonneg r.coord h.residual_identity hξ hx hu _ ht (r.eval_coord ξ x u)
  simpa only [AllocationRegion.drift, map_mul, r.eval_profile, ResidualSymmetry.eval_embed,
    map_sub, eval_pt_cpoly, ← Complex.ofReal_mul, Complex.ofReal_re] using hl

theorem AllocationRegion.trajectory_slack (r : AllocationRegion) (h : r.Checks)
    (γ : ActivePulse) {s : ℝ} (hs : s ∈ Set.Icc 0 γ.S)
    (hξ : cellXi Pinned.order7.partition Pinned.order7.ceiling γ r.cell.val s ∈
      Set.Icc (0 : ℝ) 1)
    (hbox : ∀ i,
      ![cellXi Pinned.order7.partition Pinned.order7.ceiling γ r.cell.val s,
        ‖r1 (γ.traj s)‖^2, ‖r2 (γ.traj s)‖^2] i ∈ Set.Icc (r.lo i : ℝ) (r.hi i : ℝ)) :
    r.rate (cellXi Pinned.order7.partition Pinned.order7.ceiling γ r.cell.val s) *
      cost (γ.traj s) ≤ occupationSlack Pinned.order7.partition Pinned.order7.ceiling
        Pinned.order7.potential γ r.cell.val s := by
  exact r.local_slack h hξ (by rw [γ.traj_eq hs]; exact γ.x_mem s hs) (γ.u_unit s hs) hbox

end LowerBoundCZ.Certification.Slack
