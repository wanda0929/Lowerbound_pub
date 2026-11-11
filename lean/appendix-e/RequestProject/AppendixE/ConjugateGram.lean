module

public import RequestProject.AppendixE.FaceGram

/-! Conjugate charge pairs, with the signs induced by reflection rephasing.
The zero charge is retained once, not folded into itself. -/

@[expose] public section
noncomputable section
namespace CZExposure.ConjugateGram
open MvPolynomial QuotientNormalForm SymmetryGram NormalFaceBasis ComplexConjugate
open scoped Matrix ComplexOrder

def swap : Fin 11 → Fin 11 := ![0, 2, 1, 4, 3, 6, 5, 8, 7, 10, 9]

def partner (a : Fin 11 →₀ ℕ) : Fin 11 →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => a (swap i)) (by simp)

@[simp] theorem partner_apply (a : Fin 11 →₀ ℕ) (i : Fin 11) :
    partner a i = a (swap i) := rfl

@[simp] theorem partner_partner (a : Fin 11 →₀ ℕ) : partner (partner a) = a := by
  ext i
  fin_cases i <;> rfl

theorem partner_degree (a : Fin 11 →₀ ℕ) :
    (term (partner a) 1).totalDegree = (term a 1).totalDegree := by
  simp only [term_degree_exact, Fin.sum_univ_succ, Fin.sum_univ_zero, partner_apply]
  dsimp [swap]
  omega

theorem partner_mem {a : Fin 11 →₀ ℕ} {d : ℕ} : partner a ∈ basis d ↔ a ∈ basis d := by
  rw [mem_basis, mem_basis, partner_degree]
  simp only [QuotientNormalForm.Normal, Excited, partner_apply]
  dsimp [swap]
  tauto

theorem partner_charge (a : Fin 11 →₀ ℕ) : monomialCharge (partner a) = -monomialCharge a := by
  apply Prod.ext <;>
    simp [monomialCharge, variableCharge, partner, swap, Fin.sum_univ_succ] <;> ring

def paritySign (a : Fin 11 →₀ ℕ) : ℝ := if Odd (a 1 + a 2) then -1 else 1

theorem paritySign_sq (a : Fin 11 →₀ ℕ) : paritySign a * paritySign a = 1 := by
  unfold paritySign
  split <;> norm_num

def column (a : Fin 11 →₀ ℕ) (ξ : ℝ) (x : State) (u : ℂ) : ℂ :=
  rephaser (decide (Odd (a 1 + a 2))) * eval (mixedPoint ξ x u) (term a 1)

theorem partner_column (a : Fin 11 →₀ ℕ) (ξ : ℝ) (x : State) (u : ℂ) :
    column (partner a) ξ x u = (paritySign a : ℂ) * conj (column a ξ x u) := by
  have hm : eval (mixedPoint ξ x u) (term (partner a) 1) =
      conj (eval (mixedPoint ξ x u) (term a 1)) := by
    simp [term, mixedPoint, partner, swap, Fin.prod_univ_succ, map_mul, map_pow]
    ring_nf
    simp
  have hp : partner a 1 + partner a 2 = a 1 + a 2 := by
    simp [swap, Nat.add_comm]
  simp only [column, hp, hm]
  by_cases h : Odd (a 1 + a 2) <;> simp [rephaser, paritySign, h, map_mul]

section Pair
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem real_conjugate_value (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (v : ι → ℂ) :
    value (B.map Complex.ofReal) (fun i => conj (v i)) = value (B.map Complex.ofReal) v := by
  simp only [value, Matrix.map_apply, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : B j i = B i j := by simpa using hB.apply i j
  rw [h]
  ring

def foldPair (s : ι → ℝ) (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A + (Matrix.diagonal s)ᴴ * B * Matrix.diagonal s

theorem foldPair_posSemidef (s : ι → ℝ) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (foldPair s A B).PosSemidef :=
  hA.add (hB.conjTranspose_mul_mul_same _)

theorem foldPair_value (s : ι → ℝ) (A B : Matrix ι ι ℝ) (hB : B.IsHermitian)
    (v : ι → ℂ) :
    value ((foldPair s A B).map Complex.ofReal) v =
      value (A.map Complex.ofReal) v +
        value (B.map Complex.ofReal) (fun i => (s i : ℂ) * conj (v i)) := by
  have h := real_conjugate_value B hB (fun i => (s i : ℂ) * v i)
  simp only [map_mul, Complex.conj_ofReal] at h
  rw [h]
  simp [foldPair, value, Matrix.diagonal_mul, Matrix.mul_diagonal,
    map_mul, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

end Pair

def sector (d : ℕ) (q : Charge) : Finset (Fin 11 →₀ ℕ) :=
  (basis d).filter (fun a => monomialCharge a = q)

def sectorInclusion {d : ℕ} {q : Charge} (a : sector d q) : basis d :=
  ⟨a.val, (Finset.mem_filter.mp a.property).1⟩

def opposite {d : ℕ} {q : Charge} : sector d q ≃ sector d (-q) where
  toFun a := ⟨partner a.val, Finset.mem_filter.mpr
    ⟨partner_mem.mpr (Finset.mem_filter.mp a.property).1,
      by rw [partner_charge, (Finset.mem_filter.mp a.property).2]⟩⟩
  invFun a := ⟨partner a.val, Finset.mem_filter.mpr
    ⟨partner_mem.mpr (Finset.mem_filter.mp a.property).1,
      by rw [partner_charge, (Finset.mem_filter.mp a.property).2, neg_neg]⟩⟩
  left_inv a := Subtype.ext (partner_partner a.val)
  right_inv a := Subtype.ext (partner_partner a.val)

def block {d : ℕ} (B : Matrix (basis d) (basis d) ℝ) (q : Charge) :
    Matrix (sector d q) (sector d q) ℝ := B.submatrix sectorInclusion sectorInclusion

def oppositeBlock {d : ℕ} (B : Matrix (basis d) (basis d) ℝ) (q : Charge) :
    Matrix (sector d q) (sector d q) ℝ :=
  (block B (-q)).submatrix opposite opposite

def compressedBlock {d : ℕ} (B : Matrix (basis d) (basis d) ℝ) (q : Charge) :
    Matrix (sector d q) (sector d q) ℝ :=
  if q = 0 then block B q else
    foldPair (fun a => paritySign a.val) (block B q) (oppositeBlock B q)

theorem compressedBlock_posSemidef {d : ℕ} {B : Matrix (basis d) (basis d) ℝ}
    (hB : B.PosSemidef) (q : Charge) : (compressedBlock B q).PosSemidef := by
  have hb : ∀ q, (block B q).PosSemidef := fun q => hB.submatrix sectorInclusion
  unfold compressedBlock
  split
  · exact hb q
  · exact foldPair_posSemidef _ (hb q) ((hb (-q)).submatrix opposite)

def blockValue {d : ℕ} (B : Matrix (basis d) (basis d) ℝ) (q : Charge)
    (ξ : ℝ) (x : State) (u : ℂ) : ℂ :=
  value ((block B q).map Complex.ofReal) (fun a => column a.val ξ x u)

theorem oppositeBlock_value {d : ℕ} (B : Matrix (basis d) (basis d) ℝ) (q : Charge)
    (ξ : ℝ) (x : State) (u : ℂ) :
    value ((oppositeBlock B q).map Complex.ofReal)
      (fun a => (paritySign a.val : ℂ) * conj (column a.val ξ x u)) =
      blockValue B (-q) ξ x u := by
  simp only [← partner_column]
  unfold blockValue value
  rw [← (opposite (d := d) (q := q)).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (opposite (d := d) (q := q)).sum_comp]
  rfl

/-- Zero charge contributes once. Each nonzero retained charge absorbs its
opposite, including the signs from odd control degree. -/
theorem compressedBlock_value {d : ℕ} {B : Matrix (basis d) (basis d) ℝ}
    (hB : B.PosSemidef) (q : Charge) (ξ : ℝ) (x : State) (u : ℂ) :
    value ((compressedBlock B q).map Complex.ofReal) (fun a => column a.val ξ x u) =
      blockValue B q ξ x u + if q = 0 then 0 else blockValue B (-q) ξ x u := by
  by_cases hq : q = 0
  · simp [compressedBlock, hq, blockValue]
  · have ho : (oppositeBlock B q).IsHermitian :=
      ((hB.submatrix (sectorInclusion (q := -q))).submatrix opposite).1
    rw [compressedBlock, if_neg hq, foldPair_value _ _ _ ho, oppositeBlock_value]
    simp [hq, blockValue]

def charges (d : ℕ) : Finset Charge :=
  (basis d).image (fun a : Fin 11 →₀ ℕ => monomialCharge a)

theorem sector_sum {d : ℕ} (q : Charge) (f : basis d → ℂ) :
    (∑ a : sector d q, f (sectorInclusion a)) =
      ∑ a : basis d, if monomialCharge a.val = q then f a else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => sectorInclusion a)
  · intro a _
    simp [sectorInclusion, (Finset.mem_filter.mp a.property).2]
  · intro a _ b _ hab
    exact Subtype.ext (congrArg (fun c : basis d => c.val) hab)
  · intro b hb
    have hq : monomialCharge b.val = q := (Finset.mem_filter.mp hb).2
    exact ⟨⟨b.val, Finset.mem_filter.mpr ⟨b.property, hq⟩⟩, Finset.mem_univ _, rfl⟩
  · intros; rfl

theorem sector_sum₂ {d : ℕ} (q : Charge) (f : basis d → basis d → ℂ) :
    (∑ i : sector d q, ∑ j : sector d q, f (sectorInclusion i) (sectorInclusion j)) =
      ∑ i : basis d, if monomialCharge i.val = q then
        ∑ j : basis d, if monomialCharge j.val = q then f i j else 0 else 0 := by
  calc
    _ = ∑ i : sector d q, ∑ j : basis d,
        if monomialCharge j.val = q then f (sectorInclusion i) j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact sector_sum q (fun j => f (sectorInclusion i) j)
    _ = _ := sector_sum q (fun i => ∑ j : basis d,
      if monomialCharge j.val = q then f i j else 0)

theorem sum_blockValue {d : ℕ} (B : Matrix (basis d) (basis d) ℝ)
    (hb : ∀ i j, monomialCharge i.val ≠ monomialCharge j.val → B i j = 0)
    (ξ : ℝ) (x : State) (u : ℂ) :
    (∑ q ∈ charges d, blockValue B q ξ x u) =
      value (B.map Complex.ofReal) (fun a => column a.val ξ x u) := by
  have he (q : Charge) : blockValue B q ξ x u =
      ∑ i : basis d, if monomialCharge i.val = q then
        ∑ j : basis d, if monomialCharge j.val = q then
          conj (column i.val ξ x u) * (B i j : ℂ) * column j.val ξ x u else 0 else 0 := by
    unfold blockValue value
    change (∑ i : sector d q, ∑ j : sector d q,
      conj (column (sectorInclusion i).val ξ x u) *
        (B (sectorInclusion i) (sectorInclusion j) : ℂ) *
          column (sectorInclusion j).val ξ x u) = _
    exact sector_sum₂ q (fun i j =>
      conj (column i.val ξ x u) * (B i j : ℂ) * column j.val ξ x u)
  simp_rw [he]
  rw [Finset.sum_comm]
  unfold value
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (monomialCharge i.val)]
  · simp only [ite_true, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : monomialCharge j.val = monomialCharge i.val
    · simp [h]
    · simp [h, hb i j (Ne.symm h)]
  · intro q _ hq
    simp [Ne.symm hq]
  · intro hi
    exact False.elim (hi (Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩))

def Keep (q : Charge) : Prop := 0 < q.1 ∨ q.1 = 0 ∧ 0 ≤ q.2

instance (q : Charge) : Decidable (Keep q) := inferInstanceAs (Decidable (_ ∨ _))

theorem keep_neg (q : Charge) : Keep (-q) ↔ ¬Keep q ∨ q = 0 := by
  rcases q with ⟨a,b⟩
  simp only [Keep, Prod.fst_neg, Prod.snd_neg, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  omega

theorem neg_mem_charges {d : ℕ} {q : Charge} : -q ∈ charges d ↔ q ∈ charges d := by
  have h {q : Charge} (hq : q ∈ charges d) : -q ∈ charges d := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨partner a, partner_mem.mpr ha, partner_charge a⟩
  exact ⟨fun hq => by simpa using h hq, h⟩

def retained (d : ℕ) : Finset Charge := (charges d).filter Keep

theorem retained_covers {d : ℕ} {q : Charge} (hq : q ∈ charges d) :
    q ∈ retained d ∨ -q ∈ retained d := by
  by_cases hk : Keep q
  · exact Or.inl (Finset.mem_filter.mpr ⟨hq, hk⟩)
  · exact Or.inr (Finset.mem_filter.mpr
      ⟨neg_mem_charges.mpr hq, (keep_neg q).mpr (Or.inl hk)⟩)

theorem retained_unique {d : ℕ} {q : Charge} (hq : q ∈ retained d)
    (hn : -q ∈ retained d) : q = 0 := by
  have hk := (Finset.mem_filter.mp hq).2
  have hn := (keep_neg q).mp (Finset.mem_filter.mp hn).2
  tauto

theorem sum_pairs (d : ℕ) (f : Charge → ℂ) :
    (∑ q ∈ retained d, (f q + if q = 0 then 0 else f (-q))) = ∑ q ∈ charges d, f q := by
  rw [Finset.sum_add_distrib]
  have he : (∑ q ∈ retained d, if q = 0 then 0 else f (-q)) =
      ∑ q ∈ (charges d).filter (fun q => ¬Keep q), f q := by
    have hh : (∑ q ∈ retained d, if q = 0 then 0 else f (-q)) =
        ∑ q ∈ (retained d).filter (fun q => q ≠ 0), f (-q) := by
      simp only [Finset.sum_filter, ite_not]
    rw [hh]
    apply Finset.sum_bij (fun q _ => -q)
    · intro q hq
      simp only [Finset.mem_filter, retained] at hq ⊢
      exact ⟨neg_mem_charges.mpr hq.1.1, by rw [keep_neg]; tauto⟩
    · intro a _ b _ h
      exact neg_injective h
    · intro q hq
      obtain ⟨hq, hk⟩ := Finset.mem_filter.mp hq
      refine ⟨-q, ?_, neg_neg q⟩
      simp only [Finset.mem_filter, retained]
      refine ⟨⟨neg_mem_charges.mpr hq, (keep_neg q).mpr (Or.inl hk)⟩, ?_⟩
      intro hz
      have : q = 0 := neg_eq_zero.mp hz
      subst q
      exact hk (by simp [Keep])
    · intros; rfl
  rw [he]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- One real positive matrix per retained charge, on the same degree-bounded
face columns. The equality remains a physical-domain identity. -/
theorem stationary_compressed {d : ℕ} {W : StatePoly} (hW : StationaryFeasible d W) :
    ∃ Q : (q : Charge) → Matrix (sector d q) (sector d q) ℝ,
      (∀ q, (Q q).PosSemidef) ∧
      ∀ (ξ : ℝ) (x : State), x ∈ Xset → ∀ u : ℂ, ‖u‖ = 1 →
        (∑ q ∈ retained d, value ((Q q).map Complex.ofReal)
          (fun a => column a.val ξ x u)) =
          (eval (pt ξ x u) (cpoly + lieDeriv W) : ℂ) := by
  obtain ⟨B, hB, hb, hv⟩ := FaceGram.stationary_face_matrix hW
  refine ⟨compressedBlock B, compressedBlock_posSemidef hB, ?_⟩
  intro ξ x hx u hu
  simp_rw [compressedBlock_value hB]
  rw [sum_pairs, sum_blockValue B hb]
  exact hv ξ x hx u hu

end CZExposure.ConjugateGram
