module

public import RequestProject.AppendixE.FaceRestriction

/-! Degree-preserving normalization of mixed monomials, before charge and
reflection reduction. Coordinates are ξ,u,ū,g₁,ḡ₁,r₁,r̄₁,g₂,ḡ₂,r₂,r̄₂.
The output is a polynomial, so powers of (1-r̄r) are expanded by the ring
operations. No rationality or integral-coordinate claim is made. -/

@[expose] public section
noncomputable section

namespace CZExposure.QuotientNormalForm
open MvPolynomial

abbrev MixedPoly := MvPolynomial (Fin 11) ℂ
abbrev Powers := Fin 11 → ℕ

def relations : Ideal MixedPoly := Ideal.span
  {X 1 * X 2 - 1, X 3 * X 4 - (1 - X 5 * X 6), X 7 * X 8 - (1 - X 9 * X 10)}

def term (a : Powers) (c : ℂ) : MixedPoly := C c * ∏ i, X i ^ a i

def trimmed (a : Powers) : Powers :=
  ![a 0, a 1 - min (a 1) (a 2), a 2 - min (a 1) (a 2),
    a 3 - min (a 3) (a 4), a 4 - min (a 3) (a 4), a 5, a 6,
    a 7 - min (a 7) (a 8), a 8 - min (a 7) (a 8), a 9, a 10]

def normalTerm (a : Powers) (c : ℂ) : MixedPoly :=
  term (trimmed a) c * (1 - X 5 * X 6) ^ min (a 3) (a 4) *
    (1 - X 9 * X 10) ^ min (a 7) (a 8)

def Normal (a : Powers) : Prop :=
  (a 1 = 0 ∨ a 2 = 0) ∧ (a 3 = 0 ∨ a 4 = 0) ∧ (a 7 = 0 ∨ a 8 = 0)

private theorem split_powers {R : Type*} [CommRing R] (x y : R) (a b : ℕ) :
    x^a * y^b = x^(a - min a b) * y^(b - min a b) * (x*y)^min a b := by
  rw [mul_pow]
  calc x^a * y^b = (x^(a - min a b) * x^min a b) *
      (y^(b - min a b) * y^min a b) := by
        rw [← pow_add, ← pow_add, Nat.sub_add_cancel (Nat.min_le_left _ _),
          Nat.sub_add_cancel (Nat.min_le_right _ _)]
    _ = _ := by ring

private theorem term_split (a : Powers) (c : ℂ) :
    term a c = term (trimmed a) c * (X 1 * X 2)^min (a 1) (a 2) *
      (X 3 * X 4)^min (a 3) (a 4) * (X 7 * X 8)^min (a 7) (a 8) := by
  have heq : term a c = C c * X 0^a 0 * (X 1^a 1 * X 2^a 2) *
      (X 3^a 3 * X 4^a 4) * X 5^a 5 * X 6^a 6 *
      (X 7^a 7 * X 8^a 8) * X 9^a 9 * X 10^a 10 := by
    simp [term, Fin.prod_univ_succ]
    ring
  rw [heq, split_powers (X 1) (X 2), split_powers (X 3) (X 4), split_powers (X 7) (X 8)]
  simp [term, trimmed, Fin.prod_univ_succ]
  ring

theorem normalTerm_congr (a : Powers) (c : ℂ) : term a c - normalTerm a c ∈ relations := by
  let q := Ideal.Quotient.mk relations
  have hu : q (X 1 * X 2) = q 1 :=
    Ideal.Quotient.eq.mpr (Ideal.subset_span (by simp))
  have h1 : q (X 3 * X 4) = q (1 - X 5 * X 6) :=
    Ideal.Quotient.eq.mpr (Ideal.subset_span (by simp))
  have h2 : q (X 7 * X 8) = q (1 - X 9 * X 10) :=
    Ideal.Quotient.eq.mpr (Ideal.subset_span (by simp))
  apply Ideal.Quotient.eq.mp
  change q (term a c) = q (normalTerm a c)
  rw [term_split]
  simp only [normalTerm, map_mul, map_pow, hu, h1, h2, map_one, one_pow, mul_one]

theorem term_degree (a : Powers) (c : ℂ) : (term a c).totalDegree ≤ ∑ i, a i := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_finset_prod _ _).trans (by simp)

theorem normalTerm_degree (a : Powers) (c : ℂ) :
    (normalTerm a c).totalDegree ≤ ∑ i, a i := by
  have hb (i j : Fin 11) : (1 - X i * X j : MixedPoly).totalDegree ≤ 2 := by
    apply (totalDegree_sub _ _).trans
    simp only [totalDegree_one, Nat.zero_max]
    exact (totalDegree_mul _ _).trans (by simp)
  have h : (normalTerm a c).totalDegree ≤
      (∑ i, trimmed a i) + min (a 3) (a 4) * 2 + min (a 7) (a 8) * 2 :=
    (totalDegree_mul _ _).trans
    (add_le_add ((totalDegree_mul _ _).trans
      (add_le_add (term_degree (trimmed a) c)
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hb 5 6)))))
      ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hb 9 10))))
  apply h.trans
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  dsimp [trimmed]
  omega

theorem term_degreeOf (a : Powers) (c : ℂ) (j : Fin 11) :
    degreeOf j (term a c) ≤ a j := by
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le _ _ _).trans
  have h := Finset.sum_le_sum (fun (i : Fin 11) (_ : i ∈ Finset.univ) =>
    degreeOf_pow_le j (X i : MixedPoly) (a i))
  simpa [degreeOf_X, mul_ite] using h

private theorem normalTerm_degreeOf (a : Powers) (c : ℂ) (j : Fin 11)
    (hj : j ≠ 5 ∧ j ≠ 6 ∧ j ≠ 9 ∧ j ≠ 10) :
    degreeOf j (normalTerm a c) ≤ trimmed a j := by
  have hb (i k : Fin 11) (hi : j ≠ i) (hk : j ≠ k) :
      degreeOf j (1 - X i * X k : MixedPoly) ≤ 0 := by
    apply (degreeOf_sub_le _ _ _).trans
    apply max_le (by simp)
    exact (degreeOf_mul_le _ _ _).trans (by simp [degreeOf_X, hi, hk])
  have h1 := (degreeOf_pow_le j (1 - X 5 * X 6 : MixedPoly) (min (a 3) (a 4))).trans
    (Nat.mul_le_mul_left _ (hb 5 6 hj.1 hj.2.1))
  have h2 := (degreeOf_pow_le j (1 - X 9 * X 10 : MixedPoly) (min (a 7) (a 8))).trans
    (Nat.mul_le_mul_left _ (hb 9 10 hj.2.2.1 hj.2.2.2))
  exact (degreeOf_mul_le _ _ _).trans
    ((add_le_add ((degreeOf_mul_le _ _ _).trans
      (add_le_add (term_degreeOf (trimmed a) c j) h1)) h2).trans (by simp))

theorem normalTerm_normal (a : Powers) (c : ℂ) {b : Fin 11 →₀ ℕ}
    (hb : b ∈ (normalTerm a c).support) : Normal b := by
  have h (j : Fin 11) (hj : j ≠ 5 ∧ j ≠ 6 ∧ j ≠ 9 ∧ j ≠ 10) :=
    (monomial_le_degreeOf j hb).trans (normalTerm_degreeOf a c j hj)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h7 := h 7 (by decide)
  have h8 := h 8 (by decide)
  change b 1 ≤ a 1 - min (a 1) (a 2) at h1
  change b 2 ≤ a 2 - min (a 1) (a 2) at h2
  change b 3 ≤ a 3 - min (a 3) (a 4) at h3
  change b 4 ≤ a 4 - min (a 3) (a 4) at h4
  change b 7 ≤ a 7 - min (a 7) (a 8) at h7
  change b 8 ≤ a 8 - min (a 7) (a 8) at h8
  dsimp [Normal]
  omega

/-- Sum the normalized monomials with the original coefficients. -/
def normalize (p : MixedPoly) : MixedPoly :=
  ∑ a ∈ p.support, normalTerm a (coeff a p)

theorem term_eq_monomial (a : Fin 11 →₀ ℕ) (c : ℂ) : term a c = monomial a c := by
  rw [monomial_eq]
  simp [term, Finsupp.prod_fintype]

theorem normalize_congr (p : MixedPoly) : p - normalize p ∈ relations := by
  have heq : p - normalize p = ∑ a ∈ p.support,
      (monomial a (coeff a p) - normalTerm a (coeff a p)) := by
    rw [Finset.sum_sub_distrib, support_sum_monomial_coeff]
    rfl
  rw [heq]
  apply Ideal.sum_mem
  intro a _
  simpa only [term_eq_monomial] using normalTerm_congr a (coeff a p)

theorem normalize_degree (p : MixedPoly) : (normalize p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_finsetSum_le
  intro a ha
  apply (normalTerm_degree a (coeff a p)).trans
  simpa [Finsupp.sum_fintype] using le_totalDegree ha

theorem normalize_normal (p : MixedPoly) {a : Fin 11 →₀ ℕ}
    (ha : a ∈ (normalize p).support) : Normal a := by
  obtain ⟨b, _, hab⟩ := Finset.mem_biUnion.mp (support_sum ha)
  exact normalTerm_normal b (coeff b p) hab

/-- The constructed representative has the same quotient class, no larger
degree, and only the prescribed quotient-normal monomials in its support. -/
theorem exists_normal_expansion (p : MixedPoly) : ∃ q : MixedPoly,
    p - q ∈ relations ∧ q.totalDegree ≤ p.totalDegree ∧
      ∀ a ∈ q.support, Normal a :=
  ⟨normalize p, normalize_congr p, normalize_degree p, fun _ => normalize_normal p⟩

open ComplexConjugate

def realPart (i j : Fin 11) : MixedPoly := C (1/2) * (X i + X j)
def imagPart (i j : Fin 11) : MixedPoly := C (1/(2*Complex.I)) * (X i - X j)

def encodeCoordinate : Var → MixedPoly
  | .xi => X 0
  | .ctl i => if i = 0 then realPart 1 2 else imagPart 1 2
  | .st i => ![realPart 3 4, imagPart 3 4, realPart 5 6, imagPart 5 6,
      realPart 7 8, imagPart 7 8, realPart 9 10, imagPart 9 10] i

def toMixed : FaceRestriction.ComplexPoly →ₐ[ℂ] MixedPoly := aeval encodeCoordinate

theorem toMixed_degree (p : FaceRestriction.ComplexPoly) :
    (toMixed p).totalDegree ≤ p.totalDegree := by
  apply PolynomialSymmetry.totalDegree_aeval_le
  have hr (i j : Fin 11) : (realPart i j).totalDegree ≤ 1 := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_add (X i : MixedPoly) (X j)).trans (by simp)
  have hi (i j : Fin 11) : (imagPart i j).totalDegree ≤ 1 := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub (X i : MixedPoly) (X j)).trans (by simp)
  intro v
  cases v with
  | xi => simp [encodeCoordinate]
  | ctl i => fin_cases i <;> simp [encodeCoordinate, hr, hi]
  | st i => fin_cases i <;> simp [encodeCoordinate, hr, hi]

def mixedPoint (ξ : ℝ) (x : State) (u : ℂ) : Fin 11 → ℂ :=
  ![ξ, u, conj u, g1 x, conj (g1 x), r1 x, conj (r1 x),
    g2 x, conj (g2 x), r2 x, conj (r2 x)]

theorem eval_toMixed (p : FaceRestriction.ComplexPoly) (ξ : ℝ) (x : State) (u : ℂ) :
    eval (mixedPoint ξ x u) (toMixed p) = eval (fun v => (pt ξ x u v : ℂ)) p := by
  have hr (z : ℂ) : (1/2 : ℂ) * (z + conj z) = (z.re : ℂ) := by
    rw [Complex.re_eq_add_conj]
    ring
  have hi (z : ℂ) : (1/(2*Complex.I) : ℂ) * (z - conj z) = (z.im : ℂ) := by
    rw [Complex.im_eq_sub_conj]
    ring
  simp at hr hi
  have hc (v : Var) : eval (mixedPoint ξ x u) (encodeCoordinate v) = (pt ξ x u v : ℂ) := by
    cases v with
    | xi => simp [encodeCoordinate, mixedPoint, pt]
    | ctl i => fin_cases i <;>
        simp [encodeCoordinate, realPart, imagPart, mixedPoint, pt,
          Complex.re_eq_add_conj, Complex.im_eq_sub_conj, div_eq_mul_inv, mul_comm]
    | st i => fin_cases i <;>
        simp [encodeCoordinate, realPart, imagPart, mixedPoint, pt, hr, hi] <;> rfl
  induction p using MvPolynomial.induction_on with
  | C c => simp [toMixed]
  | add p q hp hq => simp_all
  | mul_X p i hp => simp_all [toMixed]

theorem eval_relations_zero {p : MixedPoly} (hp : p ∈ relations)
    (ξ : ℝ) {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ = 1) :
    eval (mixedPoint ξ x u) p = 0 := by
  have hI : relations ≤ RingHom.ker (eval (mixedPoint ξ x u)) := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    all_goals
      change eval (mixedPoint ξ x u) _ = 0
      simp only [map_sub, map_mul, eval_X, map_one]
      dsimp [mixedPoint]
      simp only [Complex.mul_conj]
      norm_cast
      simp only [Complex.normSq_eq_norm_sq]
    · simp [hu]
    · linarith [hx.1]
    · linarith [hx.2]
  exact hI hp

theorem eval_normalize (p : MixedPoly) (ξ : ℝ) {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ = 1) :
    eval (mixedPoint ξ x u) (normalize p) = eval (mixedPoint ξ x u) p := by
  have h := eval_relations_zero (normalize_congr p) ξ hx hu
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- Construct the normal representative of an actual real-coordinate factor. -/
def factorExpansion (p : Poly) : MixedPoly :=
  normalize (toMixed (MvPolynomial.map Complex.ofRealHom p))

theorem factorExpansion_degree (p : Poly) : (factorExpansion p).totalDegree ≤ p.totalDegree := by
  apply (normalize_degree _).trans
  apply (toMixed_degree _).trans
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)

theorem factorExpansion_normal (p : Poly) {a : Fin 11 →₀ ℕ}
    (ha : a ∈ (factorExpansion p).support) : Normal a := normalize_normal _ ha

theorem eval_factorExpansion (p : Poly) (ξ : ℝ) {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ = 1) :
    eval (mixedPoint ξ x u) (factorExpansion p) = (eval (pt ξ x u) p : ℂ) := by
  rw [factorExpansion, eval_normalize _ ξ hx hu, eval_toMixed]
  exact (MvPolynomial.map_eval Complex.ofRealHom (pt ξ x u) p).symm

def faceModes : Fin 11 → FaceRestriction.FaceAlgebra :=
  ![FaceRestriction.coordinate .xi, FaceRestriction.mode 0 1, FaceRestriction.mode 0 (-1),
    FaceRestriction.mode 1 1, FaceRestriction.mode 1 (-1), 0, 0,
    FaceRestriction.mode 2 1, FaceRestriction.mode 2 (-1), 0, 0]

def mixedRestriction : MixedPoly →ₐ[ℂ] FaceRestriction.FaceAlgebra := aeval faceModes

theorem evaluate_mixedRestriction (p : MixedPoly) (t : FaceRestriction.Parameters) :
    FaceRestriction.evaluate t (mixedRestriction p) =
      eval (mixedPoint (Real.exp t.1) (FaceRestriction.faceState t)
        (FaceRestriction.phase (t.2 0))) p := by
  have hm (i : Fin 11) : FaceRestriction.evaluate t (faceModes i) =
      mixedPoint (Real.exp t.1) (FaceRestriction.faceState t)
        (FaceRestriction.phase (t.2 0)) i := by
    fin_cases i <;> simp [faceModes, mixedPoint, FaceRestriction.evaluate_mode,
      FaceRestriction.evaluate_coordinate, pt, FaceRestriction.faceState,
      FaceRestriction.phase, ← Complex.exp_conj]
  induction p using MvPolynomial.induction_on with
  | C c => simp [mixedRestriction, FaceRestriction.evaluate,
      FaceRestriction.indexCharacter, FaceRestriction.character, FaceRestriction.exponent]
  | add p q hp hq => simp_all
  | mul_X p i hp => simp_all [mixedRestriction]

/-- The actual degree-bounded normal expansion retains the already proved
zero formal face restriction of every stationary square factor. -/
theorem stationary_expansion_restriction_zero {W : StatePoly} {N : ℕ} {h : Fin N → Poly}
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) (l : Fin N) :
    mixedRestriction (factorExpansion (h l)) = 0 := by
  apply FaceRestriction.eq_zero_of_evaluate
  intro t
  rw [evaluate_mixedRestriction, eval_factorExpansion _ _
    (FaceRestriction.faceState_mem t).1 (FaceRestriction.phase_norm _)]
  rw [(sos_factors_vanish_on_face hdrift (FaceRestriction.faceState_mem t)
    (FaceRestriction.phase_norm _) _).2 l]
  rfl

end CZExposure.QuotientNormalForm
