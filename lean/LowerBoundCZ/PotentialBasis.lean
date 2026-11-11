import LowerBoundCZ.CertificateContracts

/-! Properties of the source-order real monomial decoder. These statements
are independent of the numerical certificate and hold off the state manifold. -/
noncomputable section
namespace LowerBoundCZ.Certification.Pinned
open CZExposure MvPolynomial

def realScalar (q : ℚ × ℚ) : ℝ := (q.1 : ℝ) + (q.2 : ℝ) * Real.sqrt 2

def mulPair (a b : CellPoly × CellPoly) : CellPoly × CellPoly :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def powPair (a : CellPoly × CellPoly) : ℕ → CellPoly × CellPoly
  | 0 => (1, 0)
  | n + 1 => mulPair (powPair a n) a

abbrev BasisEntry := Nat × Array Nat × Array Nat

/-- Real part of xi^d * product(conj(z_k)^anti_k * z_k^holo_k),
z=(g1,r1,g2,r2). Representatives are used once, not doubled. -/
def basisPolynomial (b : BasisEntry) : CellPoly :=
  X none ^ b.1 * ((List.finRange 4).foldl (fun p k =>
    let re : CellPoly := X (some ⟨2*k.val, by omega⟩)
    let im : CellPoly := X (some ⟨2*k.val+1, by omega⟩)
    mulPair p (mulPair (powPair (re, -im) (b.2.1[k.val]?.getD 0))
      (powPair (re, im) (b.2.2[k.val]?.getD 0)))) (1, 0)).1

def anti (b : BasisEntry) (k : Fin 4) : ℕ := b.2.1[k.val]?.getD 0
def holo (b : BasisEntry) (k : Fin 4) : ℕ := b.2.2[k.val]?.getD 0
def degreeBound (b : BasisEntry) : ℕ := b.1 + ∑ k : Fin 4, (anti b k + holo b k)

private def PairBound (p : CellPoly × CellPoly) (d : ℕ) : Prop :=
  p.1.totalDegree ≤ d ∧ p.2.totalDegree ≤ d

private theorem mulPair_bound {p q : CellPoly × CellPoly} {d e : ℕ}
    (hp : PairBound p d) (hq : PairBound q e) : PairBound (mulPair p q) (d + e) := by
  constructor
  · exact (totalDegree_sub _ _).trans (max_le
      ((totalDegree_mul _ _).trans (Nat.add_le_add hp.1 hq.1))
      ((totalDegree_mul _ _).trans (Nat.add_le_add hp.2 hq.2)))
  · exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_mul _ _).trans (Nat.add_le_add hp.1 hq.2))
      ((totalDegree_mul _ _).trans (Nat.add_le_add hp.2 hq.1)))

private theorem powPair_bound {p : CellPoly × CellPoly} {d : ℕ}
    (hp : PairBound p d) (n : ℕ) : PairBound (powPair p n) (n * d) := by
  induction n with
  | zero => simp [powPair, PairBound]
  | succ n ih => simpa [powPair, Nat.succ_mul] using mulPair_bound ih hp

private theorem fold_bound {ι : Type*} (l : List ι) (f : ι → CellPoly × CellPoly)
    (w : ι → ℕ) (hf : ∀ i, PairBound (f i) (w i))
    (p : CellPoly × CellPoly) (d : ℕ) (hp : PairBound p d) :
    PairBound (l.foldl (fun q i => mulPair q (f i)) p) (d + (l.map w).sum) := by
  induction l generalizing p d with
  | nil => simpa using hp
  | cons i l ih =>
    simpa [List.foldl_cons, Nat.add_assoc] using
      ih (mulPair p (f i)) (d + w i) (mulPair_bound hp (hf i))

theorem basisPolynomial_degree (b : BasisEntry) :
    (basisPolynomial b).totalDegree ≤ degreeBound b := by
  let f := fun k : Fin 4 =>
    let re : CellPoly := X (some ⟨2*k.val, by omega⟩)
    let im : CellPoly := X (some ⟨2*k.val+1, by omega⟩)
    mulPair (powPair (re, -im) (anti b k)) (powPair (re, im) (holo b k))
  have hf (k : Fin 4) : PairBound (f k) (anti b k + holo b k) := by
    have h1 : PairBound ((X (some ⟨2*k.val, by omega⟩) : CellPoly),
        -X (some ⟨2*k.val+1, by omega⟩)) 1 := by simp [PairBound]
    have h2 : PairBound ((X (some ⟨2*k.val, by omega⟩) : CellPoly),
        X (some ⟨2*k.val+1, by omega⟩)) 1 := by simp [PairBound]
    simpa [f] using mulPair_bound (powPair_bound h1 (anti b k)) (powPair_bound h2 (holo b k))
  have h := fold_bound (List.finRange 4) f (fun k => anti b k + holo b k)
    hf (1, 0) 0 (by simp [PairBound])
  refine (totalDegree_mul _ _).trans (Nat.add_le_add (le_of_eq (totalDegree_X_pow _ _)) ?_)
  simpa [degreeBound, basisPolynomial, anti, holo, f, List.finRange_succ,
    Fin.sum_univ_succ] using h.1

def amplitude (x : State) : Fin 4 → ℂ := ![g1 x, r1 x, g2 x, r2 x]

private def pairEval (ξ : ℝ) (x : State) (p : CellPoly × CellPoly) : ℂ :=
  ⟨evalCell ξ x p.1, evalCell ξ x p.2⟩

private theorem pairEval_mul (ξ : ℝ) (x : State) (p q : CellPoly × CellPoly) :
    pairEval ξ x (mulPair p q) = pairEval ξ x p * pairEval ξ x q := by
  apply Complex.ext <;> simp [pairEval, mulPair, evalCell, Complex.mul_re, Complex.mul_im]

private theorem pairEval_pow (ξ : ℝ) (x : State) (p : CellPoly × CellPoly) (n : ℕ) :
    pairEval ξ x (powPair p n) = (pairEval ξ x p) ^ n := by
  induction n with
  | zero => simp [powPair, pairEval, evalCell]; rfl
  | succ n ih => simp only [powPair, pairEval_mul, ih, pow_succ]

private theorem pairEval_fold {ι : Type*} (l : List ι) (f : ι → CellPoly × CellPoly)
    (p : CellPoly × CellPoly) (ξ : ℝ) (x : State) :
    pairEval ξ x (l.foldl (fun q i => mulPair q (f i)) p) =
      pairEval ξ x p * (l.map (fun i => pairEval ξ x (f i))).prod := by
  induction l generalizing p with
  | nil => simp
  | cons i l ih => simp [List.foldl_cons, ih, pairEval_mul, mul_assoc]

def complexMonomial (b : BasisEntry) (z : Fin 4 → ℂ) : ℂ :=
  ∏ k, star (z k) ^ anti b k * z k ^ holo b k

theorem basisPolynomial_eval (b : BasisEntry) (ξ : ℝ) (x : State) :
    evalCell ξ x (basisPolynomial b) = ξ ^ b.1 * (complexMonomial b (amplitude x)).re := by
  let f := fun k : Fin 4 =>
    let re : CellPoly := X (some ⟨2*k.val, by omega⟩)
    let im : CellPoly := X (some ⟨2*k.val+1, by omega⟩)
    mulPair (powPair (re, -im) (anti b k)) (powPair (re, im) (holo b k))
  have hf (k : Fin 4) : pairEval ξ x (f k) =
      star (amplitude x k) ^ anti b k * amplitude x k ^ holo b k := by
    simp only [f, pairEval_mul, pairEval_pow]
    congr 1 <;> congr 1 <;> fin_cases k <;>
      simp [pairEval, evalCell, amplitude, g1, r1, g2, r2] <;> rfl
  have h := pairEval_fold (List.finRange 4) f (1, 0) ξ x
  have h0 : pairEval ξ x (1, 0) = 1 := by
    apply Complex.ext <;> simp [pairEval, evalCell]
  rw [h0, one_mul] at h
  simp only [hf] at h
  have he : pairEval ξ x ((List.finRange 4).foldl (fun q i => mulPair q (f i)) (1, 0)) =
      complexMonomial b (amplitude x) := by
    simpa [complexMonomial, pairEval, evalCell, List.finRange_succ, Fin.prod_univ_succ] using h
  have hr := congrArg Complex.re he
  simpa [basisPolynomial, evalCell, pairEval, f, anti, holo] using
    congrArg (fun r : ℝ => ξ ^ b.1 * r) hr

def opticalWeight : Fin 4 → ℕ := ![0, 1, 0, 1]
def qubitWeight : Fin 4 → ℕ := ![1, 1, 2, 2]
def Balanced (b : BasisEntry) : Prop :=
  (∑ k, opticalWeight k * anti b k) = (∑ k, opticalWeight k * holo b k) ∧
  (∑ k, qubitWeight k * anti b k) = (∑ k, qubitWeight k * holo b k)

instance (b : BasisEntry) : Decidable (Balanced b) := inferInstanceAs (Decidable (_ ∧ _))

private theorem complexMonomial_scaled (b : BasisEntry) (z : Fin 4 → ℂ) (w : Fin 4 → ℕ)
    (e : ℂ) (he : star e * e = 1)
    (hb : (∑ k, w k * anti b k) = ∑ k, w k * holo b k) :
    complexMonomial b (fun k => e ^ w k * z k) = complexMonomial b z := by
  have hs (k : Fin 4) : star (e ^ w k * z k) ^ anti b k * (e ^ w k * z k) ^ holo b k =
      (star e ^ (w k * anti b k) * e ^ (w k * holo b k)) *
        (star (z k) ^ anti b k * z k ^ holo b k) := by
    simp only [star_mul, star_pow, mul_pow, ← pow_mul]
    ring
  simp only [complexMonomial, hs, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hb, ← mul_pow, he, one_pow, one_mul]

private theorem phase_unit (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) * Complex.exp ((t : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem basisPolynomial_invariant (b : BasisEntry) (hb : Balanced b) (ξ : ℝ) :
    IsGInvariant (fun x => evalCell ξ x (basisPolynomial b)) := by
  intro x θ α
  have ho : amplitude (opticalGauge θ x) =
      fun k => Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) ^ opticalWeight k * amplitude x k := by
    funext k
    fin_cases k <;> simp [amplitude, opticalGauge, opticalWeight]
  have hq : amplitude (qubitGauge α x) =
      fun k => Complex.exp ((α : ℂ) * Complex.I) ^ qubitWeight k * amplitude x k := by
    funext k
    fin_cases k <;> simp [amplitude, qubitGauge, qubitWeight, ← Complex.exp_nat_mul, mul_assoc]
  have hr : amplitude (reflection x) = fun k => star (amplitude x k) := by
    funext k
    fin_cases k <;> simp [amplitude, reflection]
  simp only [basisPolynomial_eval, ho, hq, hr,
    complexMonomial_scaled b _ opticalWeight _ (phase_unit (-θ)) hb.1,
    complexMonomial_scaled b _ qubitWeight _ (phase_unit α) hb.2]
  have hc : complexMonomial b (fun k => star (amplitude x k)) =
      star (complexMonomial b (amplitude x)) := by
    simp [complexMonomial]
  refine ⟨trivial, trivial, ?_⟩
  rw [hc]
  rfl

/-- Exact initial-state value, computed on exponents rather than expanded polynomials. -/
def initialWeight (b : BasisEntry) : ℕ :=
  0 ^ b.1 * (0 ^ anti b 1 * 0 ^ holo b 1) * (0 ^ anti b 3 * 0 ^ holo b 3)

theorem basisPolynomial_initial (b : BasisEntry) :
    evalCell 0 x0 (basisPolynomial b) = (initialWeight b : ℝ) := by
  rw [basisPolynomial_eval]
  have ha : amplitude x0 = ![(1 : ℂ), 0, 1, 0] := rfl
  rw [ha]
  simp [complexMonomial, Fin.prod_univ_succ, initialWeight,
    ← Complex.ofReal_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul, mul_assoc]

theorem sumBasis_degree {n d : ℕ} (c : Fin n → ℝ) (b : Fin n → BasisEntry)
    (h : ∀ i, degreeBound (b i) ≤ d) :
    (-(∑ i, C (c i) * basisPolynomial (b i))).totalDegree ≤ d := by
  rw [totalDegree_neg]
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C, zero_add] using (basisPolynomial_degree _).trans (h i))

theorem sumBasis_invariant {n : ℕ} (c : Fin n → ℝ) (b : Fin n → BasisEntry)
    (h : ∀ i, Balanced (b i)) (ξ : ℝ) :
    IsGInvariant (fun x => evalCell ξ x (-∑ i, C (c i) * basisPolynomial (b i))) := by
  intro x θ α
  have hi (i : Fin n) := basisPolynomial_invariant (b i) (h i) ξ x θ α
  simp only [evalCell, map_neg, map_sum, map_mul, eval_C]
  exact ⟨congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (hi i).1)),
    congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (hi i).2.1)),
    congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (hi i).2.2))⟩

theorem sumBasis_initial {n : ℕ} (c : Fin n → ℚ × ℚ) (b : Fin n → BasisEntry)
    (s : Finset (Fin n)) (h : ∀ i, initialWeight (b i) = if i ∈ s then 1 else 0) :
    evalCell 0 x0 (-∑ i, C (realScalar (c i)) * basisPolynomial (b i)) =
      -((∑ i ∈ s, (c i).1 : ℚ) : ℝ) - ((∑ i ∈ s, (c i).2 : ℚ) : ℝ) * Real.sqrt 2 := by
  simp only [evalCell, map_neg, map_sum, map_mul, eval_C]
  change -(∑ i, realScalar (c i) * evalCell 0 x0 (basisPolynomial (b i))) = _
  simp_rw [basisPolynomial_initial, h]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_mem, Finset.univ_inter]
  simp only [realScalar, Finset.sum_add_distrib, ← Finset.sum_mul, ← Rat.cast_sum]
  ring

theorem sumBasis_objective {n : ℕ} (c : Fin n → ℚ × ℚ) (b : Fin n → BasisEntry)
    (s : Finset (Fin n)) (q : ℚ × ℚ) (t : ℚ)
    (h : ∀ i, initialWeight (b i) = if i ∈ s then 1 else 0)
    (hc : (∑ i ∈ s, (c i).1) = q.1 + t ∧ (∑ i ∈ s, (c i).2) = q.2) :
    -realScalar q - evalCell 0 x0 (-∑ i, C (realScalar (c i)) * basisPolynomial (b i)) =
      (t : ℝ) := by
  rw [sumBasis_initial c b s h, hc.1, hc.2]
  simp only [realScalar, Rat.cast_add]
  ring

end LowerBoundCZ.Certification.Pinned
