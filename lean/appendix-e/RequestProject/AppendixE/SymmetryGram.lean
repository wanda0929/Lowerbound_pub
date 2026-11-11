module

public import RequestProject.AppendixE.QuotientNormalForm

/-! Charge separation of finite complex Gram representations. The preservation
theorem requires invariance under the two phase rotations, not invariance of
individual square factors. No independent-character assumption is introduced. -/

@[expose] public section
noncomputable section

namespace CZExposure.SymmetryGram
open ComplexConjugate
open scoped Matrix ComplexOrder

abbrev Charge := ℤ × ℤ

/-- Charges in the mixed-coordinate order fixed by QuotientNormalForm. -/
def variableCharge : Fin 11 → Charge :=
  ![(0,0), (1,0), (-1,0), (0,1), (0,-1), (-1,1), (1,-1),
    (0,2), (0,-2), (-1,2), (1,-2)]

def monomialCharge (a : Fin 11 → ℕ) : Charge := ∑ i, a i • variableCharge i

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Delete only entries between different charges. -/
def separate (q : ι → Charge) (Q : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if q i = q j then Q i j else 0

private def selector (q : ι → Charge) (c : Charge) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if q i = c then 1 else 0)

private theorem separate_eq_sum (q : ι → Charge) (Q : Matrix ι ι ℂ) :
    separate q Q = ∑ c ∈ Finset.univ.image q, (selector q c)ᴴ * Q * selector q c := by
  ext i j
  simp only [Matrix.sum_apply, selector, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : q i = q j <;>
    simp [separate, apply_ite, ite_mul, Finset.mem_image, h]

theorem separate_posSemidef (q : ι → Charge) {Q : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) : (separate q Q).PosSemidef := by
  rw [separate_eq_sum]
  exact Matrix.posSemidef_sum _ (fun c _ => hQ.conjTranspose_mul_mul_same (selector q c))

def value (Q : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (v i) * Q i j * v j

end Matrix

/-- Reuse the proved independent characters, with zero ξ and third phase
exponents. No degree coordinate is confused with a rotation charge. -/
def chargeIndex (q : Charge) : FaceRestriction.Index := (0, ![q.1, q.2, 0])

theorem chargeIndex_sub_eq_zero (a b : Charge) :
    chargeIndex (b - a) = 0 ↔ a = b := by
  constructor
  · intro h
    have h0 := congrArg (fun k : FaceRestriction.Index => k.2 0) h
    have h1 := congrArg (fun k : FaceRestriction.Index => k.2 1) h
    apply Prod.ext <;> dsimp [chargeIndex] at * <;> omega
  · rintro rfl
    simp [chargeIndex]

def phase (q : Charge) (t : FaceRestriction.Parameters) : ℂ :=
  Complex.exp (((q.1 : ℂ) * (t.2 0 : ℂ) + (q.2 : ℂ) * (t.2 1 : ℂ)) * Complex.I)

theorem evaluate_charge_single (q : Charge) (t : FaceRestriction.Parameters) (c : ℂ) :
    FaceRestriction.evaluate t (AddMonoidAlgebra.single (chargeIndex q) c) = c * phase q t := by
  simp [FaceRestriction.evaluate, FaceRestriction.indexCharacter,
    FaceRestriction.character, FaceRestriction.exponent, chargeIndex, phase,
    Fin.sum_univ_succ]
  ring_nf
  simp

theorem phase_sub (a b : Charge) (t : FaceRestriction.Parameters) :
    phase (b - a) t = conj (phase a t) * phase b t := by
  simp only [phase, Prod.fst_sub, Prod.snd_sub, Int.cast_sub, ← Complex.exp_conj,
    map_mul, map_add, map_intCast, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  ring

theorem phase_add (a b : Charge) (t : FaceRestriction.Parameters) :
    phase (a + b) t = phase a t * phase b t := by
  simp only [phase, Prod.fst_add, Prod.snd_add, Int.cast_add, ← Complex.exp_add]
  congr 1
  ring

theorem phase_sum {κ : Type*} (s : Finset κ) (q : κ → Charge)
    (t : FaceRestriction.Parameters) : phase (∑ i ∈ s, q i) t = ∏ i ∈ s, phase (q i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | @insert i s hi ih => simp [hi, phase_add, ih]

theorem phase_nsmul (n : ℕ) (q : Charge) (t : FaceRestriction.Parameters) :
    phase (n • q) t = phase q t ^ n := by
  induction n with
  | zero => simp [phase]
  | succ n ih => rw [succ_nsmul, phase_add, ih, pow_succ]

/-- The diagonal rotation action in the actual mixed-coordinate order. -/
def rotatePoint (t : FaceRestriction.Parameters) (x : Fin 11 → ℂ) : Fin 11 → ℂ :=
  fun i => phase (variableCharge i) t * x i

theorem monomial_response (a : QuotientNormalForm.Powers) (c : ℂ)
    (x : Fin 11 → ℂ) (t : FaceRestriction.Parameters) :
    MvPolynomial.eval (rotatePoint t x) (QuotientNormalForm.term a c) =
      phase (monomialCharge a) t * MvPolynomial.eval x (QuotientNormalForm.term a c) := by
  simp only [QuotientNormalForm.term, rotatePoint, monomialCharge, phase_sum, phase_nsmul,
    map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
    mul_pow, Finset.prod_mul_distrib]
  ring

theorem rotatePoint_physical (t : FaceRestriction.Parameters) (ξ : ℝ) (x : State) (u : ℂ) :
    rotatePoint t (QuotientNormalForm.mixedPoint ξ x u) =
      QuotientNormalForm.mixedPoint ξ (opticalGauge (t.2 0) (qubitGauge (t.2 1) x))
        (FaceRestriction.phase (t.2 0) * u) := by
  funext i
  fin_cases i <;>
    simp [rotatePoint, variableCharge, phase, QuotientNormalForm.mixedPoint,
      opticalGauge, qubitGauge, FaceRestriction.phase, map_mul, ← Complex.exp_conj,
      ← mul_assoc, ← Complex.exp_add] <;> ring_nf <;> norm_num [Complex.conj_ofNat]

section Preservation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def spectrum (q : ι → Charge) (Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    FaceRestriction.FaceAlgebra :=
  ∑ i, ∑ j, AddMonoidAlgebra.single (chargeIndex (q j - q i)) (conj (v i) * Q i j * v j)

omit [DecidableEq ι] in
private theorem evaluate_spectrum (q : ι → Charge) (Q : Matrix ι ι ℂ) (v : ι → ℂ)
    (t : FaceRestriction.Parameters) :
    FaceRestriction.evaluate t (spectrum q Q v) = value Q (fun i => phase (q i) t * v i) := by
  simp only [spectrum, map_sum, evaluate_charge_single, phase_sub, value, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
/-- The invariant expression, not each factor, is what must be preserved.
Independent characters force its constant coefficient to be its value. -/
theorem separate_value (q : ι → Charge) (Q : Matrix ι ι ℂ) (v : ι → ℂ) (z : ℂ)
    (hinv : ∀ t, value Q (fun i => phase (q i) t * v i) = z) :
    value (separate q Q) v = z := by
  have heq : spectrum q Q v = AddMonoidAlgebra.single 0 z := by
    apply sub_eq_zero.mp
    apply FaceRestriction.eq_zero_of_evaluate
    intro t
    rw [map_sub, evaluate_spectrum, hinv]
    simp [FaceRestriction.evaluate]
  have hc := congrArg (fun p : FaceRestriction.FaceAlgebra => p 0) heq
  change (∑ i, ∑ j, Finsupp.single (chargeIndex (q j - q i))
    (conj (v i) * Q i j * v j)) 0 = (Finsupp.single 0 z : FaceRestriction.Index →₀ ℂ) 0 at hc
  simpa only [Finsupp.finset_sum_apply, Finsupp.single_apply, chargeIndex_sub_eq_zero,
    if_pos rfl, value, separate, mul_ite, ite_mul, mul_zero, zero_mul] using hc

/-- Positive charge-separated data on the unchanged column set. In particular
any degree bound on those columns is untouched by this construction. -/
theorem invariant_gram (q : ι → Charge) (Q : Matrix ι ι ℂ) (hQ : Q.PosSemidef)
    {Ω : Type*} (v : Ω → ι → ℂ) (p : Ω → ℂ)
    (hinv : ∀ x t, value Q (fun i => phase (q i) t * v x i) = p x) :
    ∃ B : Matrix ι ι ℂ, B.PosSemidef ∧
      (∀ i j, q i ≠ q j → B i j = 0) ∧ ∀ x, value B (v x) = p x := by
  refine ⟨separate q Q, separate_posSemidef q hQ, ?_, ?_⟩
  · intro i j h
    simp [separate, h]
  · intro x
    exact separate_value q Q (v x) (p x) (hinv x)

end Preservation

section FactorMatrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The original complex Gram matrix is constructed from the factor
coefficients; redundant columns and complex coefficients are permitted. -/
theorem factor_gram_value (A : Matrix κ ι ℂ) (v : ι → ℂ) :
    value (Aᴴ * A) v = ∑ k, conj (∑ i, A k i * v i) * (∑ i, A k i * v i) := by
  symm
  simp only [value, Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Construct the charge-separated matrix directly from a supplied finite
monomial expansion. Only invariance of the sum of absolute squares is needed. -/
theorem monomial_gram (a : ι → QuotientNormalForm.Powers) (A : Matrix κ ι ℂ)
    (S : Set (Fin 11 → ℂ)) (p : (Fin 11 → ℂ) → ℂ)
    (hinv : ∀ x ∈ S, ∀ t,
      (∑ k, conj (∑ i, A k i * MvPolynomial.eval (rotatePoint t x)
          (QuotientNormalForm.term (a i) 1)) *
        (∑ i, A k i * MvPolynomial.eval (rotatePoint t x)
          (QuotientNormalForm.term (a i) 1))) = p x) :
    ∃ B : Matrix ι ι ℂ, B.PosSemidef ∧
      (∀ i j, monomialCharge (a i) ≠ monomialCharge (a j) → B i j = 0) ∧
      ∀ x ∈ S, value B (fun i => MvPolynomial.eval x (QuotientNormalForm.term (a i) 1)) = p x := by
  classical
  refine ⟨separate (fun i => monomialCharge (a i)) (Aᴴ * A),
    separate_posSemidef _ (Matrix.posSemidef_conjTranspose_mul_self A), ?_, ?_⟩
  · intro i j h
    simp [separate, h]
  · intro x hx
    apply separate_value
    intro t
    rw [factor_gram_value]
    simpa only [monomial_response] using hinv x hx t

end FactorMatrix

section Rephase
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exactly the manuscript's factor i for odd control degree, 1 otherwise. -/
def rephaser (odd : Bool) : ℂ := if odd then Complex.I else 1

theorem rephaser_unit (odd : Bool) : conj (rephaser odd) * rephaser odd = 1 := by
  cases odd <;> simp [rephaser]

theorem rephaser_reflection (odd : Bool) (z : ℂ) :
    rephaser odd * ((if odd then -1 else 1) * conj z) = conj (rephaser odd * z) := by
  cases odd <;> simp [rephaser, map_mul]

theorem monomial_reflection (a : QuotientNormalForm.Powers) (ξ : ℝ) (x : State) (u : ℂ) :
    MvPolynomial.eval (QuotientNormalForm.mixedPoint ξ (reflection x) (-conj u))
        (QuotientNormalForm.term a 1) =
      (-1 : ℂ) ^ (a 1 + a 2) * conj (MvPolynomial.eval
        (QuotientNormalForm.mixedPoint ξ x u) (QuotientNormalForm.term a 1)) := by
  simp only [QuotientNormalForm.term, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.prod_univ_succ, Fin.prod_univ_zero]
  dsimp [QuotientNormalForm.mixedPoint, reflection]
  simp only [map_neg, map_one, Complex.conj_ofReal, g1_mkState, r1_mkState,
    g2_mkState, r2_mkState, starRingEnd_self_apply, pow_add]
  rw [neg_pow (conj u), neg_pow u]
  ring

/-- The raw reflection sign is absorbed by i exactly for odd control degree. -/
theorem rephased_monomial_reflection (a : QuotientNormalForm.Powers)
    (ξ : ℝ) (x : State) (u : ℂ) :
    rephaser (decide (Odd (a 1 + a 2))) *
      MvPolynomial.eval (QuotientNormalForm.mixedPoint ξ (reflection x) (-conj u))
        (QuotientNormalForm.term a 1) =
      conj (rephaser (decide (Odd (a 1 + a 2))) * MvPolynomial.eval
        (QuotientNormalForm.mixedPoint ξ x u) (QuotientNormalForm.term a 1)) := by
  rw [monomial_reflection]
  have h : (-1 : ℂ) ^ (a 1 + a 2) =
      if decide (Odd (a 1 + a 2)) then -1 else 1 := by
    rcases Nat.even_or_odd (a 1 + a 2) with he | ho
    · simp [he.neg_one_pow, show ¬Odd (a 1 + a 2) from Nat.not_odd_iff_even.mpr he]
    · simp [ho, ho.neg_one_pow]
  rw [h]
  exact rephaser_reflection _ _

theorem rephaser_degree (odd : Bool) (p : QuotientNormalForm.MixedPoly) :
    (MvPolynomial.C (rephaser odd) * p).totalDegree ≤ p.totalDegree := by
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

def rephaseMatrix (odd : ι → Bool) (Q : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => rephaser (odd i)) * Q *
    (Matrix.diagonal (fun i => rephaser (odd i)))ᴴ

theorem rephaseMatrix_apply (odd : ι → Bool) (Q : Matrix ι ι ℂ) (i j : ι) :
    rephaseMatrix odd Q i j = rephaser (odd i) * Q i j * conj (rephaser (odd j)) := by
  simp [rephaseMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem rephaseMatrix_posSemidef (odd : ι → Bool) {Q : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) : (rephaseMatrix odd Q).PosSemidef :=
  hQ.mul_mul_conjTranspose_same _

theorem rephaseMatrix_value (odd : ι → Bool) (Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    value (rephaseMatrix odd Q) (fun i => rephaser (odd i) * v i) = value Q v := by
  unfold value
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [rephaseMatrix_apply, map_mul]
  calc
    _ = (conj (rephaser (odd i)) * rephaser (odd i)) *
        (conj (rephaser (odd j)) * rephaser (odd j)) * (conj (v i) * Q i j * v j) := by ring
    _ = _ := by rw [rephaser_unit, rephaser_unit]; ring

theorem rephaseMatrix_blocks (odd : ι → Bool) (q : ι → Charge) (Q : Matrix ι ι ℂ)
    (h : ∀ i j, q i ≠ q j → Q i j = 0) :
    ∀ i j, q i ≠ q j → rephaseMatrix odd Q i j = 0 := by
  intro i j hij
  simp [rephaseMatrix_apply, h i j hij]

end Rephase

section Reflection
variable {ι : Type*} [Fintype ι]

/-- After rephasing, reflection acts by conjugating the column values.
Entrywise real part then gives the reflection-averaged real matrix. -/
def realMatrix (Q : Matrix ι ι ℂ) : Matrix ι ι ℝ := fun i j => (Q i j).re

theorem realMatrix_posSemidef {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (realMatrix Q).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    have h := congrArg Complex.re (hQ.1.apply i j)
    simpa [realMatrix] using h
  · intro v
    have h := (Complex.nonneg_iff.mp (hQ.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [realMatrix, Matrix.mulVec, dotProduct, Complex.mul_re, Finset.mul_sum] using h

theorem realMatrix_value (Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    value (fun i j => (realMatrix Q i j : ℂ)) v =
      (value Q v + conj (value Q (fun i => conj (v i)))) / 2 := by
  have h (a b c : ℂ) : conj a * (b.re : ℂ) * c =
      (conj a * b * c + conj a * conj b * c) / 2 := by
    rw [Complex.re_eq_add_conj]
    ring
  simp only [value, realMatrix, h, map_sum, map_mul, starRingEnd_self_apply,
    ← Finset.sum_div, Finset.sum_add_distrib]

/-- A real symmetric positive matrix for a real-valued reflection-invariant
expression, retaining every zero between different charges. -/
theorem reflection_gram (q : ι → Charge) (Q : Matrix ι ι ℂ) (hQ : Q.PosSemidef)
    (hblock : ∀ i j, q i ≠ q j → Q i j = 0)
    {Ω : Type*} (v : Ω → ι → ℂ) (p : Ω → ℝ)
    (hrep : ∀ x, value Q (v x) = (p x : ℂ))
    (href : ∀ x, value Q (fun i => conj (v x i)) = (p x : ℂ)) :
    ∃ B : Matrix ι ι ℝ, B.PosSemidef ∧
      (∀ i j, q i ≠ q j → B i j = 0) ∧
      ∀ x, value (fun i j => (B i j : ℂ)) (v x) = (p x : ℂ) := by
  refine ⟨realMatrix Q, realMatrix_posSemidef hQ, ?_, ?_⟩
  · intro i j h
    simp [realMatrix, hblock i j h]
  · intro x
    rw [realMatrix_value, hrep, href, Complex.conj_ofReal]
    ring

end Reflection

/-- Combined charge separation, parity rephasing, and real reflection
averaging. The orbit identities are explicit obligations for the supplied
column representation; they are not new general mathematical inputs. -/
theorem real_invariant_gram {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → Charge) (odd : ι → Bool) (Q : Matrix ι ι ℂ) (hQ : Q.PosSemidef)
    (v : Ω → ι → ℂ) (p : Ω → ℝ)
    (hrot : ∀ x t, value Q (fun i => phase (q i) t * v x i) = (p x : ℂ))
    (href : ∀ x t, value Q (fun i => phase (q i) t *
      ((if odd i then -1 else 1) * conj (v x i))) = (p x : ℂ)) :
    ∃ B : Matrix ι ι ℝ, B.PosSemidef ∧
      (∀ i j, q i ≠ q j → B i j = 0) ∧
      ∀ x, value (fun i j => (B i j : ℂ)) (fun i => rephaser (odd i) * v x i) = (p x : ℂ) := by
  have hblock : ∀ i j, q i ≠ q j → separate q Q i j = 0 := by
    intro i j h
    simp [separate, h]
  apply reflection_gram q (rephaseMatrix odd (separate q Q))
    (rephaseMatrix_posSemidef odd (separate_posSemidef q hQ))
    (rephaseMatrix_blocks odd q _ hblock) (fun x i => rephaser (odd i) * v x i) p
  · intro x
    rw [rephaseMatrix_value]
    exact separate_value q Q (v x) _ (hrot x)
  · intro x
    have heq : (fun i => conj (rephaser (odd i) * v x i)) =
        (fun i => rephaser (odd i) * ((if odd i then -1 else 1) * conj (v x i))) := by
      funext i
      exact (rephaser_reflection _ _).symm
    rw [heq, rephaseMatrix_value]
    exact separate_value q Q _ _ (href x)

end CZExposure.SymmetryGram
