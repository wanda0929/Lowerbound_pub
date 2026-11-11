module

public import RequestProject.AppendixE.ConcreteStationary

/-! The concrete partitioned cones over real coefficients. We use Appendix E's
W convention (W_j = -n - V_j with a shared constant n). The redundant scalar squared-
magnitude interval family is absorbed into the full interval Gram blocks. -/

@[expose] public section
noncomputable section
namespace CZExposure.ConcretePartitioned
open MvPolynomial QuotientNormalForm QuotientCertificate SymmetryGram TerminalCertificate
open scoped Matrix ComplexOrder

/-- All quotient-normal columns, without the zero-cost-face restriction. -/
def fullBasis (d : ℕ) : Finset (Fin 11 →₀ ℕ) := by
  classical
  exact (PolynomialIntegration.exponentBox 11 d).filter
    (fun a => Normal a ∧ (∑ i, a i) ≤ d)

theorem mem_fullBasis {a : Fin 11 →₀ ℕ} {d : ℕ} : a ∈ fullBasis d ↔
    Normal a ∧ (term a 1).totalDegree ≤ d := by
  classical
  rw [fullBasis, Finset.mem_filter, NormalFaceBasis.term_degree_exact]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    simp only [PolynomialIntegration.exponentBox, Finset.mem_Iic]
    intro i
    change a i ≤ d
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans h.2

/-- Interface factors contain neither ξ nor either control coordinate. -/
def interfaceBasis (d : ℕ) : Finset (Fin 11 →₀ ℕ) :=
  (fullBasis d).filter (fun a => a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0)

def chargeSector (b : Finset (Fin 11 →₀ ℕ)) (q : Charge) : Finset (Fin 11 →₀ ℕ) :=
  b.filter (fun a => monomialCharge a = q)

def keptCharges (b : Finset (Fin 11 →₀ ℕ)) : Finset Charge :=
  (b.image (fun a : Fin 11 →₀ ℕ => monomialCharge a)).filter ConjugateGram.Keep

/-- A finite family of rephased real positive charge blocks, modulo the
three normalization relations. No abstract SOS membership is assumed. -/
def GramCone (b : Finset (Fin 11 →₀ ℕ)) (p : MixedPoly) : Prop :=
  ∃ Q : (q : keptCharges b) → Matrix (chargeSector b q.val) (chargeSector b q.val) ℝ,
    (∀ q, (Q q).PosSemidef) ∧
      p - (∑ q : keptCharges b, gram ((Q q).map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1)) ∈ relations

def OccupationCone (d : ℕ) (p : MixedPoly) : Prop :=
  ∃ p₀ p₁, GramCone (NormalFaceBasis.basis d) p₀ ∧
    GramCone (fullBasis (d - 1)) p₁ ∧ p = p₀ + X 0 * (1 - X 0) * p₁

/-- Both univariate interval blocks are explicit. At order zero, d-1 uses
the same natural-number truncation convention as the existing hierarchy. -/
def TerminalCone (d : ℕ) (p : UniPoly) : Prop :=
  ∃ Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
    ∃ R : Matrix (Fin ((d - 1) + 1)) (Fin ((d - 1) + 1)) ℝ,
      Q.PosSemidef ∧ R.PosSemidef ∧ p =
        (∑ i, ∑ j, monomialColumn d i * C (Q i j) * monomialColumn d j) +
        X () * (1 - X ()) *
          (∑ i, ∑ j, monomialColumn (d - 1) i * C (R i j) * monomialColumn (d - 1) j)

/-- Concrete cell, interface, and terminal conditions. Positivity of the
exposure ceiling is a soundness condition, not part of algebraic feasibility. -/
def Feasible (P : ExposurePartition) (U : ℝ) (d : ℕ) (W : ℕ → CellPoly) : Prop :=
  ∀ j < P.J,
    (W j).totalDegree ≤ 2 * d - 1 ∧
    (∀ ξ, IsGInvariant (fun x => evalCell ξ x (W j))) ∧
    OccupationCone d (embed (cpoly + cellOp (1 / (U * P.width j)) (W j))) ∧
    (j + 1 < P.J → GramCone (interfaceBasis d)
      (embed (ofState (atXi 0 (W (j + 1)) - atXi 1 (W j))))) ∧
    TerminalCone d (-terminalRestriction (W j))

/-- The shared scalar offset in the manuscript's V,n presentation. -/
def shifted (n : ℝ) (V : CellPoly) : CellPoly := -C n - V

theorem shifted_involutive (n : ℝ) (V : CellPoly) : shifted n (shifted n V) = V := by
  simp [shifted]

theorem evalCell_shifted (n ξ : ℝ) (x : State) (V : CellPoly) :
    evalCell ξ x (shifted n V) = -n - evalCell ξ x V := by
  simp [shifted, evalCell]

theorem shifted_degree_iff (n : ℝ) (V : CellPoly) (D : ℕ) :
    (shifted n V).totalDegree ≤ D ↔ V.totalDegree ≤ D := by
  have h (p : CellPoly) : (shifted n p).totalDegree ≤ p.totalDegree := by
    exact (totalDegree_sub _ _).trans (by simp)
  constructor
  · intro hd
    have hh := h (shifted n V)
    rw [shifted_involutive] at hh
    exact hh.trans hd
  · exact fun hd => (h V).trans hd

theorem shifted_invariant_iff (n ξ : ℝ) (V : CellPoly) :
    IsGInvariant (fun x => evalCell ξ x (shifted n V)) ↔
      IsGInvariant (fun x => evalCell ξ x V) := by
  simp only [IsGInvariant, evalCell_shifted, sub_right_inj]

theorem cellOp_shifted (n κ : ℝ) (V : CellPoly) :
    cellOp κ (shifted n V) = -cellOp κ V := by
  simp [shifted, cellOp, ofCell, Finset.sum_neg_distrib]
  ring

theorem interface_shifted (n : ℝ) (V Vnext : CellPoly) :
    atXi 0 (shifted n Vnext) - atXi 1 (shifted n V) = atXi 1 V - atXi 0 Vnext := by
  simp [shifted, atXi]

theorem terminal_shifted (n : ℝ) (V : CellPoly) :
    -terminalRestriction (shifted n V) = terminalRestriction V + C n := by
  simp [shifted, terminalRestriction]

/-- Appendix C's V,n constraints over the same complete real matrix cones.
This predicate states the three residuals independently of the W definition. -/
def PotentialFeasible (P : ExposurePartition) (U : ℝ) (d : ℕ)
    (n : ℝ) (V : ℕ → CellPoly) : Prop :=
  ∀ j < P.J,
    (V j).totalDegree ≤ 2 * d - 1 ∧
    (∀ ξ, IsGInvariant (fun x => evalCell ξ x (V j))) ∧
    OccupationCone d (embed (cpoly - cellOp (1 / (U * P.width j)) (V j))) ∧
    (j + 1 < P.J → GramCone (interfaceBasis d)
      (embed (ofState (atXi 1 (V j) - atXi 0 (V (j + 1)))))) ∧
    TerminalCone d (terminalRestriction (V j) + C n)

theorem feasible_shifted_iff (P : ExposurePartition) (U : ℝ) (d : ℕ)
    (n : ℝ) (V : ℕ → CellPoly) :
    Feasible P U d (fun j => shifted n (V j)) ↔ PotentialFeasible P U d n V := by
  simp only [Feasible, PotentialFeasible, shifted_degree_iff, shifted_invariant_iff,
    cellOp_shifted, interface_shifted, terminal_shifted]
  simp only [sub_eq_add_neg]

/-- Every W family has a V presentation for any chosen shared offset n. -/
theorem potential_shifted_iff (P : ExposurePartition) (U : ℝ) (d : ℕ)
    (n : ℝ) (W : ℕ → CellPoly) :
    PotentialFeasible P U d n (fun j => shifted n (W j)) ↔ Feasible P U d W := by
  rw [← feasible_shifted_iff]
  simp only [shifted_involutive]

theorem GramCone.zero (b : Finset (Fin 11 →₀ ℕ)) : GramCone b 0 := by
  refine ⟨fun _ => 0, fun _ => Matrix.PosSemidef.zero, ?_⟩
  simp [gram]

/-- Every concrete stationary certificate embeds with identical cells,
zero interval multipliers, and zero interface jumps, at the same order. -/
theorem of_stationary {d : ℕ} {W : StatePoly} (hW : ConcreteStationary.Feasible d W)
    (P : ExposurePartition) (U : ℝ) : Feasible P U d (fun _ => rename some W) := by
  obtain ⟨hd, hsym, Q, T, hQ, hT, he, ht⟩ := hW
  have hg : GramCone (NormalFaceBasis.basis d) (embed (cpoly + lieDeriv W)) :=
    ⟨Q, hQ, he⟩
  intro j _
  refine ⟨(totalDegree_rename_le _ _).trans hd, ?_, ?_, ?_, ?_⟩
  · intro ξ
    simpa only [evalCell_rename_some] using hsym
  · rw [cellOp_rename_some]
    exact ⟨_, 0, hg, GramCone.zero _, by simp⟩
  · intro _
    simpa [atXi_rename_some, ofState] using GramCone.zero (interfaceBasis d)
  · exact ⟨T, 0, hT, Matrix.PosSemidef.zero, by simpa using ht⟩

/-- Normalization relations vanish at physical states and unit controls;
real positive matrices are nonnegative on complex columns. -/
theorem GramCone.eval_nonneg {b : Finset (Fin 11 →₀ ℕ)} {p : MixedPoly}
    (hp : GramCone b p) (ξ : ℝ) {x : State} (hx : x ∈ Xset)
    {u : ℂ} (hu : ‖u‖ = 1) : 0 ≤ (eval (mixedPoint ξ x u) p).re := by
  obtain ⟨Q, hQ, he⟩ := hp
  have hv := eval_relations_zero he ξ hx hu
  simp only [map_sub, map_sum, eval_gram] at hv
  have hr := congrArg Complex.re hv
  simp only [Complex.sub_re, Complex.re_sum, Complex.zero_re, sub_eq_zero] at hr
  rw [hr]
  exact Finset.sum_nonneg (fun q _ => ConcreteStationary.value_re_nonneg (hQ q) _)

theorem OccupationCone.eval_nonneg {d : ℕ} {p : MixedPoly}
    (hp : OccupationCone d p) {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    {x : State} (hx : x ∈ Xset) {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ (eval (mixedPoint ξ x u) p).re := by
  obtain ⟨p₀, p₁, h₀, h₁, rfl⟩ := hp
  have h0 := h₀.eval_nonneg ξ hx hu
  have h1 := h₁.eval_nonneg ξ hx hu
  simpa [mixedPoint, Complex.mul_re, Complex.mul_im] using
    add_nonneg h0 (mul_nonneg (mul_nonneg hξ.1 (sub_nonneg.mpr hξ.2)) h1)

theorem TerminalCone.eval_nonneg {d : ℕ} {p : UniPoly} (hp : TerminalCone d p)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ eval (fun _ => ξ) p := by
  obtain ⟨Q, R, hQ, hR, rfl⟩ := hp
  have h0 := hQ.dotProduct_mulVec_nonneg
    (fun i => eval (fun _ => ξ) (monomialColumn d i))
  have h1 := hR.dotProduct_mulVec_nonneg
    (fun i => eval (fun _ => ξ) (monomialColumn (d - 1) i))
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at h0 h1
  simpa only [map_add, map_sum, map_mul, map_sub, map_one, eval_X, eval_C, mul_assoc]
    using add_nonneg h0 (mul_nonneg (mul_nonneg hξ.1 (sub_nonneg.mpr hξ.2)) h1)

theorem Feasible.drift_nonneg {P : ExposurePartition} {U : ℝ} {d : ℕ}
    {W : ℕ → CellPoly} (hW : Feasible P U d W) (j : ℕ) (hj : j < P.J)
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (x : State) (hx : x ∈ Xset)
    (u : ℂ) (hu : ‖u‖ = 1) :
    0 ≤ eval (pt ξ x u) (cpoly + cellOp (1 / (U * P.width j)) (W j)) := by
  simpa only [ResidualSymmetry.eval_embed, Complex.ofReal_re] using
    (hW j hj).2.2.1.eval_nonneg hξ hx hu

theorem Feasible.interface_nonneg {P : ExposurePartition} {U : ℝ} {d : ℕ}
    {W : ℕ → CellPoly} (hW : Feasible P U d W) (j : ℕ) (hj : j + 1 < P.J)
    (x : State) (hx : x ∈ Xset) : evalCell 1 x (W j) ≤ evalCell 0 x (W (j + 1)) := by
  have h := ((hW j (by omega)).2.2.2.1 hj).eval_nonneg 0 hx (u := 1) (by simp)
  simpa only [ResidualSymmetry.eval_embed, Complex.ofReal_re, eval_pt_ofState,
    map_sub, eval_atXi, sub_nonneg] using h

theorem Feasible.terminal_nonpos {P : ExposurePartition} {U : ℝ} {d : ℕ}
    {W : ℕ → CellPoly} (hW : Feasible P U d W) (j : ℕ) (hj : j < P.J)
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (x : State) (hx : x ∈ XCZ) :
    evalCell ξ x (W j) ≤ 0 := by
  have h := (hW j hj).2.2.2.2.eval_nonneg hξ
  rwa [map_neg, terminalRestriction_on_orbit _ (hW j hj).2.1 ξ hx, neg_nonneg] at h

/-- Every concrete certificate bounds successful pulses below its ceiling,
without any external completeness inputs or abstract SOS conversion. -/
theorem Feasible.weak_duality {P : ExposurePartition} {U : ℝ} {d : ℕ}
    {W : ℕ → CellPoly} (hW : Feasible P U d W) (γ : Pulse) (hγ : γ.exposure < U) :
    evalCell 0 x0 (W 0) ≤ γ.exposure :=
  split_weak_duality_of_nonneg hW.drift_nonneg hW.interface_nonneg hW.terminal_nonpos γ hγ

/-- One successful pulse below U extends the bound to the physical infimum.
Existence of that pulse is an explicit hypothesis, not a consequence here. -/
theorem Feasible.le_Cstar {P : ExposurePartition} {U : ℝ} {d : ℕ}
    {W : ℕ → CellPoly} (hW : Feasible P U d W) (hU : ∃ γ : Pulse, γ.exposure < U) :
    (evalCell 0 x0 (W 0) : EReal) ≤ Cstar := by
  refine le_iInf fun γ => EReal.coe_le_coe_iff.2 ?_
  by_cases hγ : γ.exposure < U
  · exact hW.weak_duality γ hγ
  · obtain ⟨γ', hγ'⟩ := hU
    exact (hW.weak_duality γ' hγ').trans (by linarith)

theorem fullBasis_mono {d e : ℕ} (hde : d ≤ e) : fullBasis d ⊆ fullBasis e := by
  intro a ha
  obtain ⟨hn, hd⟩ := mem_fullBasis.mp ha
  exact mem_fullBasis.mpr ⟨hn, hd.trans hde⟩

theorem interfaceBasis_mono {d e : ℕ} (hde : d ≤ e) :
    interfaceBasis d ⊆ interfaceBasis e :=
  Finset.filter_subset_filter _ (fullBasis_mono hde)

/-- Preserve the polynomial by padding existing sectors and adding zero
matrices for newly retained charges. -/
theorem GramCone.mono {b c : Finset (Fin 11 →₀ ℕ)} {p : MixedPoly}
    (hp : GramCone b p) (hbc : b ⊆ c) : GramCone c p := by
  classical
  obtain ⟨Q, hQ, he⟩ := hp
  have hs (q : Charge) : chargeSector b q ⊆ chargeSector c q :=
    Finset.filter_subset_filter _ hbc
  have hk : keptCharges b ⊆ keptCharges c :=
    Finset.filter_subset_filter _ (Finset.image_subset_image hbc)
  let R : (q : keptCharges c) → Matrix (chargeSector c q.val) (chargeSector c q.val) ℝ :=
    fun q => if h : q.val ∈ keptCharges b then FaceGram.pad (Q ⟨q.val, h⟩) else 0
  let f (q : Charge) : MixedPoly := if h : q ∈ keptCharges b then
    gram ((Q ⟨q, h⟩).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) else 0
  have hsum : (∑ q : keptCharges c, gram ((R q).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1)) =
      ∑ q : keptCharges b, gram ((Q q).map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) := by
    calc
      _ = ∑ q : keptCharges c, f q.val := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq : q.val ∈ keptCharges b
        · simp only [R, f, dif_pos hq]
          exact ResidualSymmetry.pad_gram (hs q.val) _ _
        · simp [R, f, hq, gram]
      _ = ∑ q ∈ keptCharges c, f q := Finset.sum_coe_sort _ _
      _ = ∑ q ∈ keptCharges b, f q :=
        (Finset.sum_subset hk (by intro q _ hq; simp [f, hq])).symm
      _ = _ := by
        rw [← Finset.sum_coe_sort (keptCharges b) f]
        apply Finset.sum_congr rfl
        intro q _
        simp [f, q.property]
  refine ⟨R, ?_, ?_⟩
  · intro q
    dsimp only [R]
    split
    · exact FaceGram.pad_posSemidef (hQ _)
    · exact Matrix.PosSemidef.zero
  · rw [hsum]
    exact he

theorem GramCone.add {b : Finset (Fin 11 →₀ ℕ)} {p r : MixedPoly}
    (hp : GramCone b p) (hr : GramCone b r) : GramCone b (p + r) := by
  obtain ⟨Q, hQ, he⟩ := hp
  obtain ⟨R, hR, hf⟩ := hr
  refine ⟨fun q => Q q + R q, fun q => (hQ q).add (hR q), ?_⟩
  have hg : ∀ q, gram (((Q q + R q)).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) =
      gram ((Q q).map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) +
      gram ((R q).map Complex.ofReal) (fun i =>
        C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) := by
    intro q
    simp [gram, map_add, mul_add, add_mul, Finset.sum_add_distrib]
  simp_rw [hg, Finset.sum_add_distrib]
  convert relations.add_mem he hf using 1
  ring

/-- A single nonnegative squared magnitude in a retained charge sector
is a one-entry diagonal Gram contribution; rephasing cancels exactly. -/
theorem GramCone.monomial_kept {b : Finset (Fin 11 →₀ ℕ)}
    {a : Fin 11 →₀ ℕ} (ha : a ∈ b) (hk : ConjugateGram.Keep (monomialCharge a))
    {s : ℝ} (hs : 0 ≤ s) : GramCone b (C (s : ℂ) * conjugate (term a 1) * term a 1) := by
  classical
  let q : keptCharges b := ⟨monomialCharge a,
    Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, hk⟩⟩
  let Q : (k : keptCharges b) → Matrix (chargeSector b k.val) (chargeSector b k.val) ℝ :=
    fun _ => Matrix.diagonal (fun i => if i.val = a then s else 0)
  have hQ : ∀ k, (Q k).PosSemidef := by
    intro k
    dsimp only [Q]
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    split_ifs <;> positivity
  have hg (k : keptCharges b) : gram ((Q k).map Complex.ofReal) (fun i =>
      C (rephaser (decide (Odd (i.val 1 + i.val 2)))) * term i.val 1) =
      ∑ i : chargeSector b k.val,
        if i.val = a then C (s : ℂ) * conjugate (term a 1) * term a 1 else 0 := by
    simp only [gram, Q, Matrix.map_apply, Matrix.diagonal_apply]
    simp only [apply_ite, Complex.ofReal_zero, map_zero, ite_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val = a
    · simp only [hi, if_true, map_mul, conjugate_C]
      calc
        _ = C (s : ℂ) * C (starRingEnd ℂ (rephaser (decide (Odd (a 1 + a 2)))) *
          rephaser (decide (Odd (a 1 + a 2)))) * conjugate (term a 1) * term a 1 := by
            rw [map_mul]; ring
        _ = _ := by rw [rephaser_unit]; simp
    · simp [hi]
  refine ⟨Q, hQ, ?_⟩
  simp_rw [hg]
  have he : (∑ k : keptCharges b, ∑ i : chargeSector b k.val,
      if i.val = a then C (s : ℂ) * conjugate (term a 1) * term a 1 else 0) =
      C (s : ℂ) * conjugate (term a 1) * term a 1 := by
    rw [Finset.sum_eq_single q]
    · let i : chargeSector b q.val := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
      rw [Finset.sum_eq_single i]
      · simp [i]
      · intro j _ hj
        have hn : j.val ≠ a := fun h => hj (Subtype.ext h)
        simp [hn]
      · simp
    · intro k _ hkq
      apply Finset.sum_eq_zero
      intro i _
      have hn : i.val ≠ a := by
        intro hi
        apply hkq
        apply Subtype.ext
        simpa only [hi] using (Finset.mem_filter.mp i.property).2.symm
      simp [hn]
    · simp
  rw [he, sub_self]
  exact relations.zero_mem

/-- Opposite charge representatives have identical squared magnitudes
as polynomials, not merely on normalized physical states. -/
theorem partner_squared (a : Fin 11 →₀ ℕ) :
    conjugate (term (ConjugateGram.partner a) 1) * term (ConjugateGram.partner a) 1 =
      conjugate (term a 1) * term a 1 := by
  apply ResidualSymmetry.mixedPoint_ext
  intro ξ x u
  simp [map_mul, term, mixedPoint, ConjugateGram.partner,
    ConjugateGram.swap, Fin.prod_univ_succ, map_pow]
  ring

theorem fullBasis_partner {d : ℕ} {a : Fin 11 →₀ ℕ} (ha : a ∈ fullBasis d) :
    ConjugateGram.partner a ∈ fullBasis d := by
  rw [mem_fullBasis, ConjugateGram.partner_degree]
  obtain ⟨hn, hd⟩ := mem_fullBasis.mp ha
  refine ⟨?_, hd⟩
  simpa [QuotientNormalForm.Normal, ConjugateGram.partner_apply, ConjugateGram.swap,
    or_comm] using hn

/-- Every normal support monomial is available, regardless of which of
its two charge representatives is retained. No face restriction is needed. -/
theorem GramCone.monomial {d : ℕ} {a : Fin 11 →₀ ℕ} (ha : a ∈ fullBasis d)
    {s : ℝ} (hs : 0 ≤ s) :
    GramCone (fullBasis d) (C (s : ℂ) * conjugate (term a 1) * term a 1) := by
  by_cases hk : ConjugateGram.Keep (monomialCharge a)
  · exact GramCone.monomial_kept ha hk hs
  · have hkp : ConjugateGram.Keep (monomialCharge (ConjugateGram.partner a)) := by
      rw [ConjugateGram.partner_charge, ConjugateGram.keep_neg]
      exact Or.inl hk
    have h := GramCone.monomial_kept (fullBasis_partner ha) hkp hs
    simpa only [mul_assoc, partner_squared] using h

/-- Finite nonnegative scalar families, including repeated squared
magnitudes, fit into the interval Gram blocks at the same degree. -/
theorem GramCone.scalar_family {ι : Type*} (t : Finset ι) {d : ℕ}
    (a : ι → Fin 11 →₀ ℕ) (s : ι → ℝ)
    (ha : ∀ i ∈ t, a i ∈ fullBasis d) (hs : ∀ i ∈ t, 0 ≤ s i) :
    GramCone (fullBasis d) (∑ i ∈ t, C (s i : ℂ) * conjugate (term (a i) 1) * term (a i) 1) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using GramCone.zero (fullBasis d)
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (GramCone.monomial (ha i (by simp)) (hs i (by simp))).add
      (ih (fun j hj => ha j (by simp [hj])) (fun j hj => hs j (by simp [hj])))

/-- Adding Appendix C's redundant scalar interval family does not enlarge
the occupation cone or require any increase of hierarchy order. -/
theorem OccupationCone.absorb_scalar_family {ι : Type*} {d : ℕ} {p : MixedPoly}
    (hp : OccupationCone d p) (t : Finset ι) (a : ι → Fin 11 →₀ ℕ) (s : ι → ℝ)
    (ha : ∀ i ∈ t, a i ∈ fullBasis (d - 1)) (hs : ∀ i ∈ t, 0 ≤ s i) :
    OccupationCone d (p + X 0 * (1 - X 0) *
      ∑ i ∈ t, C (s i : ℂ) * conjugate (term (a i) 1) * term (a i) 1) := by
  obtain ⟨p₀, p₁, h₀, h₁, rfl⟩ := hp
  refine ⟨p₀, p₁ + _, h₀, h₁.add (GramCone.scalar_family t a s ha hs), ?_⟩
  ring

/-- Adding a separately parameterized scalar family leaves the cone equal,
for any prescribed finite list of allowed support monomials. -/
theorem occupation_iff_with_scalar_family {ι : Type*} {d : ℕ} {p : MixedPoly}
    (t : Finset ι) (a : ι → Fin 11 →₀ ℕ) (ha : ∀ i ∈ t, a i ∈ fullBasis (d - 1)) :
    OccupationCone d p ↔ ∃ (r : MixedPoly) (s : ι → ℝ),
      OccupationCone d r ∧ (∀ i ∈ t, 0 ≤ s i) ∧
      p = r + X 0 * (1 - X 0) *
        ∑ i ∈ t, C (s i : ℂ) * conjugate (term (a i) 1) * term (a i) 1 := by
  constructor
  · intro hp
    exact ⟨p, fun _ => (0 : ℝ), hp, by simp, by simp⟩
  · rintro ⟨r, s, hr, hs, rfl⟩
    exact hr.absorb_scalar_family t a s ha hs

theorem OccupationCone.mono {d e : ℕ} {p : MixedPoly}
    (hp : OccupationCone d p) (hde : d ≤ e) : OccupationCone e p := by
  obtain ⟨p₀, p₁, h₀, h₁, he⟩ := hp
  refine ⟨p₀, p₁, h₀.mono ?_, h₁.mono (fullBasis_mono (by omega)), he⟩
  intro a ha
  obtain ⟨hn, hf, hd⟩ := NormalFaceBasis.mem_basis.mp ha
  exact NormalFaceBasis.mem_basis.mpr ⟨hn, hf, hd.trans hde⟩

/-- Extend a univariate Gram matrix without changing its polynomial. -/
theorem terminalGram_pad {d e : ℕ} (hde : d ≤ e)
    (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hQ : Q.PosSemidef) :
    ∃ T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℝ, T.PosSemidef ∧
      (∑ i, ∑ j, monomialColumn e i * C (T i j) * monomialColumn e j) =
      ∑ i, ∑ j, monomialColumn d i * C (Q i j) * monomialColumn d j := by
  classical
  let D : Matrix (Fin (d + 1)) (Fin (e + 1)) ℝ :=
    fun i j => if i.val = j.val then 1 else 0
  refine ⟨Dᴴ * Q * D, hQ.conjTranspose_mul_mul_same D, ?_⟩
  apply MvPolynomial.funext
  intro x
  let v : Fin (e + 1) → ℝ := fun i => x () ^ i.val
  have hv : D *ᵥ v = fun i : Fin (d + 1) => x () ^ i.val := by
    funext i
    change (∑ j : Fin (e + 1), (if i.val = j.val then (1 : ℝ) else 0) * v j) = _
    rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
    · simp [v]
    · intro j _ hji
      have hn : i.val ≠ j.val := by
        intro he
        exact hji (Fin.ext he.symm)
      simp [hn]
    · simp
  have he : v ⬝ᵥ ((Dᴴ * Q * D) *ᵥ v) =
      (D *ᵥ v) ⬝ᵥ (Q *ᵥ (D *ᵥ v)) := by
    have hD : Dᴴ = Dᵀ := by ext i j; simp
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      hD, Matrix.vecMul_transpose]
  rw [hv] at he
  simpa [v, monomialColumn, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using he

theorem TerminalCone.mono {d e : ℕ} {p : UniPoly}
    (hp : TerminalCone d p) (hde : d ≤ e) : TerminalCone e p := by
  obtain ⟨Q, R, hQ, hR, he⟩ := hp
  obtain ⟨T, hT, ht⟩ := terminalGram_pad hde Q hQ
  obtain ⟨S, hS, hs⟩ := terminalGram_pad (show d - 1 ≤ e - 1 by omega) R hR
  exact ⟨T, S, hT, hS, by rw [ht, hs]; exact he⟩

theorem Feasible.mono {P : ExposurePartition} {U : ℝ} {d e : ℕ}
    {W : ℕ → CellPoly} (hW : Feasible P U d W) (hde : d ≤ e) : Feasible P U e W := by
  intro j hj
  obtain ⟨hd, hsym, hocc, hint, hterm⟩ := hW j hj
  exact ⟨hd.trans (by omega), hsym, hocc.mono hde,
    fun h => (hint h).mono (interfaceBasis_mono hde), hterm.mono hde⟩

/-- Supremum of initial values over concrete partitioned certificates.
Extended reals allow empty feasible sets or unbounded objectives. -/
def optimum (P : ExposurePartition) (U : ℝ) (d : ℕ) : EReal :=
  ⨆ (W : ℕ → CellPoly) (_ : Feasible P U d W), (evalCell 0 x0 (W 0) : EReal)

/-- The manuscript objective, with the shared offset optimized explicitly. -/
def potentialOptimum (P : ExposurePartition) (U : ℝ) (d : ℕ) : EReal :=
  ⨆ (n : ℝ) (V : ℕ → CellPoly) (_ : PotentialFeasible P U d n V),
    (-n - evalCell 0 x0 (V 0) : ℝ)

theorem potentialOptimum_eq (P : ExposurePartition) (U : ℝ) (d : ℕ) :
    potentialOptimum P U d = optimum P U d := by
  apply le_antisymm
  · refine iSup_le fun n => iSup₂_le fun V hV => ?_
    have hW := (feasible_shifted_iff P U d n V).2 hV
    have h := le_iSup₂ (f := fun (W : ℕ → CellPoly) (_ : Feasible P U d W) =>
      (evalCell 0 x0 (W 0) : EReal)) (fun j => shifted n (V j)) hW
    simpa only [evalCell_shifted] using h
  · refine iSup₂_le fun W hW => ?_
    have hV := (potential_shifted_iff P U d 0 W).2 hW
    have h := le_iSup₂ (f := fun (V : ℕ → CellPoly) (_ : PotentialFeasible P U d 0 V) =>
      ((-(0 : ℝ) - evalCell 0 x0 (V 0) : ℝ) : EReal)) (fun j => shifted 0 (W j)) hV
    apply le_trans ?_ (le_iSup (fun n : ℝ =>
      ⨆ (V : ℕ → CellPoly) (_ : PotentialFeasible P U d n V),
        ((-n - evalCell 0 x0 (V 0) : ℝ) : EReal)) 0)
    simpa only [evalCell_shifted, neg_zero, zero_sub, neg_neg] using h

theorem stationary_le_optimum (P : ExposurePartition) (U : ℝ) (d : ℕ) :
    ConcreteStationary.optimum d ≤ optimum P U d := by
  refine iSup₂_le fun W hW => ?_
  have h := le_iSup₂ (f := fun (W : ℕ → CellPoly) (_ : Feasible P U d W) =>
    (evalCell 0 x0 (W 0) : EReal)) (fun _ => rename some W) (of_stationary hW P U)
  simpa only [evalCell_rename_some] using h

theorem optimum_le_Cstar (P : ExposurePartition) {U : ℝ}
    (hU : ∃ γ : Pulse, γ.exposure < U) (d : ℕ) : optimum P U d ≤ Cstar :=
  iSup₂_le fun _ hW => hW.le_Cstar hU

theorem optimum_nonneg (P : ExposurePartition) (U : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ optimum P U d :=
  (ConcreteStationary.optimum_nonneg hd).trans (stationary_le_optimum P U d)

theorem optimum_mono (P : ExposurePartition) (U : ℝ) : Monotone (optimum P U) := by
  intro d e hde
  exact iSup₂_le fun W hW => le_iSup₂_of_le
    (f := fun (W : ℕ → CellPoly) (_ : Feasible P U e W) => (evalCell 0 x0 (W 0) : EReal))
    W (hW.mono hde) le_rfl

/-- Conditional convergence on any fixed partition by squeezing between
the concrete stationary optimum and the physical infimum. Neither reverse
SOS conversion nor partitioned degree monotonicity is assumed. -/
theorem fixed_partition_convergence
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (P : ExposurePartition) (U : ℝ)
    (hU : ∃ γ : Pulse, γ.exposure < U) :
    Filter.Tendsto (optimum P U) Filter.atTop (nhds Cstar) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (ConcreteStationary.stationary_convergence hSuperposition)
    tendsto_const_nhds (stationary_le_optimum P U) (optimum_le_Cstar P hU)

/-- Positive-order partitioned optima are finite under the manuscript's
successful-pulse-below-ceiling hypothesis. -/
theorem optimum_finite (P : ExposurePartition) {U : ℝ}
    (hU : ∃ γ : Pulse, γ.exposure < U) {d : ℕ} (hd : 1 ≤ d) :
    optimum P U d ≠ ⊤ ∧ optimum P U d ≠ ⊥ := by
  obtain ⟨γ, hγ⟩ := hU
  have hU : ∃ γ : Pulse, γ.exposure < U := ⟨γ, hγ⟩
  exact ⟨ne_top_of_le_ne_top (Cstar_finite γ).1 (optimum_le_Cstar P hU d),
    ne_bot_of_le_ne_bot (by simp) (optimum_nonneg P U hd)⟩

/-- Finite-real epsilon form of fixed-partition convergence. The upper bound
still requires a successful pulse strictly below the chosen ceiling. -/
theorem optimum_epsilon
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (P : ExposurePartition) {U : ℝ}
    (hU : ∃ γ : Pulse, γ.exposure < U) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D,
      0 ≤ Cstar.toReal - (optimum P U d).toReal ∧
        Cstar.toReal - (optimum P U d).toReal < ε := by
  obtain ⟨γ, hγ⟩ := hU
  have hU : ∃ γ : Pulse, γ.exposure < U := ⟨γ, hγ⟩
  obtain ⟨D, hD, hεD⟩ :=
    ConcreteStationary.optimum_epsilon hSuperposition hε
  refine ⟨D, hD, fun d hDd => ?_⟩
  have hd := hD.trans hDd
  have hf := optimum_finite P hU hd
  have hs := ConcreteStationary.optimum_finite γ hd
  have hu := EReal.toReal_le_toReal (optimum_le_Cstar P hU d)
    hf.2 (Cstar_finite γ).1
  have hl := EReal.toReal_le_toReal (stationary_le_optimum P U d) hs.2 hf.1
  have he := (hεD d hDd).2
  constructor <;> linarith

end CZExposure.ConcretePartitioned
