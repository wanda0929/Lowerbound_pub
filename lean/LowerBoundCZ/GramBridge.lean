import LowerBoundCZ.CertificateContracts

/-! Algebraic transport from ordered archive Gram blocks to the concrete
Appendix E cones. Numerical PSD and polynomial residual checks remain external;
neither cone membership nor a trajectory bound is an input. -/
noncomputable section
namespace LowerBoundCZ.Certification.GramBridge
open CZExposure MvPolynomial QuotientNormalForm QuotientCertificate SymmetryGram
open ConcretePartitioned TerminalCertificate
open scoped Matrix ComplexOrder

/-- Real changes of columns, including signed permutations and sparse integer
face columns, preserve both the Gram polynomial and positive semidefiniteness. -/
theorem gram_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (D : Matrix ι κ ℝ) (z : κ → MixedPoly) :
    gram ((Dᴴ * B * D).map Complex.ofReal) z =
      gram (B.map Complex.ofReal) (fun i => ∑ j, C (D i j : ℂ) * z j) := by
  simp only [gram, Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial, Complex.ofReal_sum, Complex.ofReal_mul, map_sum, map_mul,
    conjugate_C, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

def column (a : Fin 11 →₀ ℕ) : MixedPoly :=
  C (rephaser (decide (Odd (a 1 + a 2)))) * term a 1

/-- The archive may omit target basis elements or use dependent columns.
No invertibility or full-rank assumption on the change of basis is needed. -/
theorem block_cone {b : Finset (Fin 11 →₀ ℕ)} (q : keptCharges b)
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (D : Matrix (Fin n) (chargeSector b q.val) ℝ) (hB : B.PosSemidef) :
    GramCone b (gram (B.map Complex.ofReal)
      (fun i => ∑ j, C (D i j : ℂ) * column j.val)) := by
  classical
  let R := Dᴴ * B * D
  let Q : (k : keptCharges b) → Matrix (chargeSector b k.val) (chargeSector b k.val) ℝ :=
    fun k => if h : k = q then h ▸ R else 0
  refine ⟨Q, ?_, ?_⟩
  · intro k
    by_cases h : k = q
    · subst k
      simpa [Q, R] using hB.conjTranspose_mul_mul_same D
    · simp [Q, h, Matrix.PosSemidef.zero]
  · rw [Finset.sum_eq_single q]
    · simp only [Q, dif_pos rfl]
      rw [gram_congruence]
      simpa only [column, sub_self] using relations.zero_mem
    · intro k _ hk
      simp [Q, hk, gram]
    · simp

theorem gram_conjugate {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (hB : B.IsHermitian) (z : ι → MixedPoly) :
    gram (B.map Complex.ofReal) (fun i => conjugate (z i)) =
      gram (B.map Complex.ofReal) z := by
  simp only [gram, Matrix.map_apply, QuotientSymmetry.conjugate_involutive]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : B j i = B i j := by simpa using hB.apply i j
  rw [h]
  ring

/-- Polynomial, rather than pointwise, version of conjugate-charge transport.
The minus sign on odd control degree is essential. -/
theorem conjugate_partner_column (a : Fin 11 →₀ ℕ) :
    conjugate (column (ConjugateGram.partner a)) =
      C (ConjugateGram.paritySign a : ℂ) * column a := by
  have hp : ConjugateGram.partner a 1 + ConjugateGram.partner a 2 = a 1 + a 2 := by
    simp [ConjugateGram.swap, Nat.add_comm]
  simp only [column, map_mul, conjugate_C, QuotientSymmetry.conjugate_term,
    map_one, ConjugateGram.partner_partner, hp]
  by_cases h : Odd (a 1 + a 2) <;>
    simp [rephaser, ConjugateGram.paritySign, h]

/-- An ordered source block. `indices` point to the *partners* of the source
monomials in the positive-charge target basis. `weights` are the source face
columns, with rows indexing the original Gram matrix. Repetitions are allowed.
The large numerical matrix is an external input, not an existential cone. -/
structure Block (b : Finset (Fin 11 →₀ ℕ)) where
  size : ℕ
  columns : ℕ
  charge : keptCharges b
  indices : Fin columns → chargeSector b charge.val
  weights : Matrix (Fin size) (Fin columns) ℝ
  matrix : Matrix (Fin size) (Fin size) ℝ

namespace Block
variable {b : Finset (Fin 11 →₀ ℕ)}

def source (A : Block b) (i : Fin A.size) : MixedPoly :=
  ∑ j, C (A.weights i j : ℂ) * column (ConjugateGram.partner (A.indices j).val)

def polynomial (A : Block b) : MixedPoly := gram (A.matrix.map Complex.ofReal) A.source

def transport (A : Block b) : Matrix (Fin A.size) (chargeSector b A.charge.val) ℝ :=
  fun i k => ∑ j, if A.indices j = k then
    A.weights i j * ConjugateGram.paritySign (A.indices j).val else 0

theorem source_transport (A : Block b) (i : Fin A.size) :
    conjugate (A.source i) = ∑ k, C (A.transport i k : ℂ) * column k.val := by
  classical
  simp only [source, map_sum, map_mul, conjugate_C, Complex.conj_ofReal,
    conjugate_partner_column, transport, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (A.indices j)]
  · simp [mul_assoc]
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem cone (A : Block b) (h : A.matrix.PosSemidef) : GramCone b A.polynomial := by
  have he : (fun i => conjugate (A.source i)) =
      (fun i => ∑ k, C (A.transport i k : ℂ) * column k.val) :=
    funext A.source_transport
  have hc := block_cone A.charge A.matrix A.transport h
  rw [← he, gram_conjugate _ h.1] at hc
  exact hc

end Block

/-- Source-order monomials and sparse integer face columns before any charge
conversion. Entries of Q(sqrt(2)) are exact pairs of rational numbers. -/
structure RawBlock where
  size : ℕ
  columns : ℕ
  charge : Charge
  powers : Fin columns → Fin 11 →₀ ℕ
  weights : Matrix (Fin size) (Fin columns) ℤ
  entries : Matrix (Fin size) (Fin size) (ℚ × ℚ)

def scalar (x : ℚ × ℚ) : ℝ := (x.1 : ℝ) + (x.2 : ℝ) * Real.sqrt 2

def RawBlock.matrix (a : RawBlock) : Matrix (Fin a.size) (Fin a.size) ℝ :=
  fun i j => scalar (a.entries i j)

structure RawBlock.Valid (a : RawBlock) (b : Finset (Fin 11 →₀ ℕ)) : Prop where
  nonempty : 0 < a.columns
  keep : ConjugateGram.Keep (-a.charge)
  charge_eq : ∀ i, monomialCharge (a.powers i) = a.charge
  membership : ∀ i, ConjugateGram.partner (a.powers i) ∈ b

def RawBlock.toBlock (a : RawBlock) {b : Finset (Fin 11 →₀ ℕ)} (h : a.Valid b) : Block b where
  size := a.size
  columns := a.columns
  charge := ⟨-a.charge, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
    ⟨ConjugateGram.partner (a.powers ⟨0, h.nonempty⟩), h.membership _, by
      rw [ConjugateGram.partner_charge, h.charge_eq]⟩, h.keep⟩⟩
  indices := fun i => ⟨ConjugateGram.partner (a.powers i), Finset.mem_filter.mpr
    ⟨h.membership i, by rw [ConjugateGram.partner_charge, h.charge_eq]⟩⟩
  weights := fun i j => (a.weights i j : ℝ)
  matrix := a.matrix

/-- The decoder preserves the entire source polynomial, including every
off-diagonal entry. It does not assume a polynomial identity for the decoder. -/
theorem RawBlock.polynomial_eq (a : RawBlock) {b : Finset (Fin 11 →₀ ℕ)} (h : a.Valid b) :
    (a.toBlock h).polynomial = gram (a.matrix.map Complex.ofReal)
      (fun i => ∑ j, C ((a.weights i j : ℝ) : ℂ) * column (a.powers j)) := by
  unfold Block.polynomial
  congr 1

theorem RawBlock.cone (a : RawBlock) {b : Finset (Fin 11 →₀ ℕ)} (h : a.Valid b)
    (hQ : a.matrix.PosSemidef) :
    GramCone b (gram (a.matrix.map Complex.ofReal)
      (fun i => ∑ j, C ((a.weights i j : ℝ) : ℂ) * column (a.powers j))) := by
  rw [← a.polynomial_eq h]
  exact (a.toBlock h).cone hQ

def blocksPolynomial {b : Finset (Fin 11 →₀ ℕ)} (A : List (Block b)) : MixedPoly :=
  (A.map Block.polynomial).sum

theorem blocks_cone {b : Finset (Fin 11 →₀ ℕ)} (A : List (Block b))
    (h : ∀ a ∈ A, a.matrix.PosSemidef) : GramCone b (blocksPolynomial A) := by
  induction A with
  | nil => exact GramCone.zero b
  | cons a A ih =>
    exact (a.cone (h a (by simp))).add (ih (fun c hc => h c (by simp [hc])))

theorem cone_congr {b : Finset (Fin 11 →₀ ℕ)} {p r : MixedPoly}
    (h : p - r ∈ relations) (hr : GramCone b r) : GramCone b p := by
  obtain ⟨Q, hQ, he⟩ := hr
  refine ⟨Q, hQ, ?_⟩
  convert relations.add_mem h he using 1
  ring

/-- A cell's uncompressed and support-localizer blocks. Scalar interval
blocks are one-by-one support blocks, so no special numerical rule is needed. -/
structure Cell (d : ℕ) where
  moment : List (Block (NormalFaceBasis.basis d))
  interval : List (Block (fullBasis (d - 1)))

def Cell.polynomial {d : ℕ} (a : Cell d) : MixedPoly :=
  blocksPolynomial a.moment + X 0 * (1 - X 0) * blocksPolynomial a.interval

theorem Cell.cone {d : ℕ} (a : Cell d) {p : MixedPoly}
    (hm : ∀ B ∈ a.moment, B.matrix.PosSemidef)
    (hi : ∀ B ∈ a.interval, B.matrix.PosSemidef)
    (he : p - a.polynomial ∈ relations) : OccupationCone d p := by
  let r := blocksPolynomial a.interval
  refine ⟨p - X 0 * (1 - X 0) * r, r, ?_, blocks_cone _ hi, by ring⟩
  apply cone_congr _ (blocks_cone _ hm)
  convert he using 1
  simp only [Cell.polynomial, r]
  ring

structure Terminal (d : ℕ) where
  moment : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ
  interval : Matrix (Fin ((d - 1) + 1)) (Fin ((d - 1) + 1)) ℝ

def Terminal.polynomial {d : ℕ} (a : Terminal d) : TerminalCertificate.UniPoly :=
  (∑ i, ∑ j, TerminalCertificate.monomialColumn d i * C (a.moment i j) *
    TerminalCertificate.monomialColumn d j) + X () * (1 - X ()) *
  (∑ i, ∑ j, TerminalCertificate.monomialColumn (d - 1) i * C (a.interval i j) *
    TerminalCertificate.monomialColumn (d - 1) j)

/-- All source matrices and basis maps are explicit data. -/
structure Archive (a : Lower.Payload) where
  cells : Fin a.partition.J → Cell a.order
  interfaces : Fin (a.partition.J - 1) → List (Block (interfaceBasis a.order))
  terminal : Fin a.partition.J → Terminal a.order

/-- Finite algebraic external obligations. In particular, there is no
`PotentialFeasible`, `GramCone`, `OccupationCone`, or physical bound field. -/
structure MatrixChecks {a : Lower.Payload} (A : Archive a) : Prop where
  moment_psd : ∀ j, ∀ B ∈ (A.cells j).moment, B.matrix.PosSemidef
  interval_psd : ∀ j, ∀ B ∈ (A.cells j).interval, B.matrix.PosSemidef
  interface_psd : ∀ j, ∀ B ∈ A.interfaces j, B.matrix.PosSemidef
  terminal_psd : ∀ j, (A.terminal j).moment.PosSemidef ∧ (A.terminal j).interval.PosSemidef
  drift : ∀ j, embed (cpoly - cellOp (1 / (a.ceiling * a.partition.width j.val))
    (a.potential j.val)) - (A.cells j).polynomial ∈ relations
  interface_identity : ∀ j, embed (ofState (atXi 1 (a.potential j.val) -
    atXi 0 (a.potential (j.val + 1)))) - blocksPolynomial (A.interfaces j) ∈ relations
  terminal_identity : ∀ j, terminalRestriction (a.potential j.val) + C a.offset =
    (A.terminal j).polynomial

/-- Generic feasibility additionally requires the potential's structural properties.
For the pinned potential these are theorems, not certificate inputs. -/
structure Checks {a : Lower.Payload} (A : Archive a) : Prop extends MatrixChecks A where
  degree : ∀ j < a.partition.J, (a.potential j).totalDegree ≤ 2 * a.order - 1
  invariant : ∀ j < a.partition.J, ∀ ξ, IsGInvariant (fun x => evalCell ξ x (a.potential j))

theorem Checks.feasible {a : Lower.Payload} {A : Archive a} (h : Checks A) :
    PotentialFeasible a.partition a.ceiling a.order a.offset a.potential := by
  intro j hj
  refine ⟨h.degree j hj, h.invariant j hj, ?_, ?_, ?_⟩
  · exact (A.cells ⟨j, hj⟩).cone (h.moment_psd ⟨j, hj⟩)
      (h.interval_psd ⟨j, hj⟩) (h.drift ⟨j, hj⟩)
  · intro hi
    let k : Fin (a.partition.J - 1) := ⟨j, by omega⟩
    apply cone_congr (h.interface_identity k)
    exact blocks_cone (A.interfaces k) (h.interface_psd k)
  · change TerminalCone a.order (terminalRestriction (a.potential j) + C a.offset)
    rw [h.terminal_identity ⟨j, hj⟩]
    exact ⟨(A.terminal ⟨j, hj⟩).moment, (A.terminal ⟨j, hj⟩).interval,
      (h.terminal_psd ⟨j, hj⟩).1, (h.terminal_psd ⟨j, hj⟩).2, rfl⟩

end LowerBoundCZ.Certification.GramBridge
