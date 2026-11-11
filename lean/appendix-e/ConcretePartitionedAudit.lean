import RequestProject.AppendixE.ConcretePartitioned

noncomputable section
namespace CZExposure.ConcretePartitioned
open MvPolynomial QuotientNormalForm TerminalCertificate
open scoped Matrix ComplexOrder

#print Feasible
#check @of_stationary
#print axioms of_stationary
#check @Feasible.weak_duality
#check @Feasible.le_Cstar
#print axioms Feasible.weak_duality
#print axioms Feasible.le_Cstar
#print optimum
#check @fixed_partition_convergence
#print axioms fixed_partition_convergence
#check @Feasible.mono
#print axioms optimum_mono
#print potentialOptimum
#print axioms potentialOptimum_eq
#check feasible_shifted_iff
#print axioms occupation_iff_with_scalar_family

run_cmd do
  for name in [``mem_fullBasis, ``GramCone.zero, ``of_stationary,
      ``GramCone.eval_nonneg, ``OccupationCone.eval_nonneg, ``TerminalCone.eval_nonneg,
      ``Feasible.drift_nonneg, ``Feasible.interface_nonneg, ``Feasible.terminal_nonpos,
      ``Feasible.weak_duality, ``Feasible.le_Cstar,
      ``stationary_le_optimum, ``optimum_le_Cstar, ``optimum_nonneg,
      ``fixed_partition_convergence,
      ``fullBasis_mono, ``interfaceBasis_mono, ``GramCone.mono, ``OccupationCone.mono,
      ``terminalGram_pad, ``TerminalCone.mono, ``Feasible.mono, ``optimum_mono,
      ``shifted_involutive, ``evalCell_shifted, ``shifted_degree_iff, ``shifted_invariant_iff,
      ``cellOp_shifted, ``interface_shifted, ``terminal_shifted,
      ``feasible_shifted_iff, ``potential_shifted_iff, ``potentialOptimum_eq,
      ``GramCone.add, ``GramCone.monomial_kept, ``partner_squared, ``fullBasis_partner,
      ``GramCone.monomial, ``GramCone.scalar_family, ``OccupationCone.absorb_scalar_family,
      ``occupation_iff_with_scalar_family,
      ``Cstar_nonneg, ``Cstar_finite, ``coe_Cstar_toReal,
      ``polynomial_certificates_epsilon,
      ``ConcreteStationary.optimum_finite, ``ConcreteStationary.optimum_epsilon,
      ``optimum_finite, ``optimum_epsilon,
      ``cell_step, ``split_weak_duality] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Full interval columns must not inherit the zero-cost-face restriction.
example : (0 : Fin 11 →₀ ℕ) ∈ fullBasis 0 ∧
    (0 : Fin 11 →₀ ℕ) ∉ NormalFaceBasis.basis 0 := by
  simp [mem_fullBasis, NormalFaceBasis.mem_basis, term,
    QuotientNormalForm.Normal, NormalFaceBasis.Excited]

-- State-only means no ξ and neither control coordinate, not merely charge zero.
example : Finsupp.single (3 : Fin 11) 2 ∈ interfaceBasis 2 ∧
    Finsupp.single (0 : Fin 11) 1 ∉ interfaceBasis 2 ∧
    Finsupp.single (1 : Fin 11) 1 ∉ interfaceBasis 2 ∧
    Finsupp.single (2 : Fin 11) 1 ∉ interfaceBasis 2 := by
  simp [interfaceBasis, mem_fullBasis, NormalFaceBasis.term_degree_exact,
    QuotientNormalForm.Normal, Finsupp.single_apply]

-- Exercise a nonzero terminal interval multiplier, not just the stationary
-- constant case. It vanishes at both endpoints but is negative outside [0,1].
example : TerminalCone 2 (X () * (1 - X ()) * C 3) ∧
    eval (fun _ : Unit => (2 : ℝ)) (X () * (1 - X ()) * C 3) < 0 := by
  constructor
  · refine ⟨0, constantGram 1 3, Matrix.PosSemidef.zero,
      constantGram_psd 1 (by norm_num), ?_⟩
    rw [constantGram_identity]
    simp
  · norm_num

-- No partition-specific matrix assumption and no increase of order.
example (P : ExposurePartition) (U : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    Feasible P U d (fun _ => 0) := by
  simpa using of_stationary
    (ConcreteStationary.of_stationary (stationaryFeasible_zero hd)) P U

-- The sign convention is next-cell minus previous-cell for W, and the
-- interface condition is required only at genuine interior boundaries.
example {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (h : Feasible P U d W) {j : ℕ} (hj : j + 1 < P.J) :
    GramCone (interfaceBasis d)
      (QuotientCertificate.embed (ofState (atXi 0 (W (j + 1)) - atXi 1 (W j)))) :=
  (h j (by omega)).2.2.2.1 hj

-- Endpoint tests alone would accept this polynomial; the midpoint rules it out.
example (d : ℕ) : ¬ TerminalCone d (- (X () * (1 - X ()))) := by
  intro h
  have hn := h.eval_nonneg (ξ := 1 / 2) (by constructor <;> norm_num)
  norm_num at hn

-- Terminal soundness covers every target phase and both cell endpoints,
-- not just the representative used to build the terminal matrices.
example {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (h : Feasible P U d W) {j : ℕ} (hj : j < P.J) {x : State} (hx : x ∈ XCZ) :
    evalCell 0 x (W j) ≤ 0 ∧ evalCell 1 x (W j) ≤ 0 :=
  ⟨h.terminal_nonpos j hj 0 (by constructor <;> norm_num) x hx,
    h.terminal_nonpos j hj 1 (by constructor <;> norm_num) x hx⟩

-- The physical infimum bound keeps the successful-below-ceiling witness explicit.
example {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (h : Feasible P U d W) (γ : Pulse) (hγ : γ.exposure < U) :
    (evalCell 0 x0 (W 0) : EReal) ≤ Cstar := h.le_Cstar ⟨γ, hγ⟩

-- The supremum uses the initial value of the first cell, not a terminal value.
example {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (h : Feasible P U d W) : (evalCell 0 x0 (W 0) : EReal) ≤ optimum P U d :=
  le_iSup₂ (f := fun (W : ℕ → CellPoly) (_ : Feasible P U d W) =>
    (evalCell 0 x0 (W 0) : EReal)) W h

-- Stationary inclusion applies even at order zero and without a ceiling witness.
example (P : ExposurePartition) : ConcreteStationary.optimum 0 ≤ optimum P 0 0 :=
  stationary_le_optimum P 0 0

-- Lower and upper bounds use different hypotheses; only the upper bound
-- needs an actual successful pulse below the ceiling.
example (P : ExposurePartition) {U : ℝ} (γ : Pulse) (hγ : γ.exposure < U)
    {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ optimum P U d ∧ optimum P U d ≤ Cstar :=
  ⟨optimum_nonneg P U hd, optimum_le_Cstar P ⟨γ, hγ⟩ d⟩

-- Skipped-order transport keeps every cell polynomial, even at order zero.
example {P : ExposurePartition} {U : ℝ} {W : ℕ → CellPoly}
    (h : Feasible P U 0 W) : Feasible P U 4 W := h.mono (by omega)

example (P : ExposurePartition) (U : ℝ) (d : ℕ) :
    optimum P U d ≤ optimum P U (d + 1) := optimum_mono P U (by omega)

-- Natural subtraction at order zero retains a constant interval block.
-- Padding must preserve its nonconstant polynomial rather than replace it
-- by a constant terminal witness as in the stationary case.
example : TerminalCone 4 (X () * (1 - X ()) * C 3) := by
  have h : TerminalCone 0 (X () * (1 - X ()) * C 3) := by
    refine ⟨0, constantGram 0 3, Matrix.PosSemidef.zero,
      constantGram_psd 0 (by norm_num), ?_⟩
    rw [constantGram_identity]
    simp
  exact h.mono (by omega)

-- A degree-two state monomial appears precisely at its degree boundary.
example : Finsupp.single (3 : Fin 11) 2 ∈ interfaceBasis 2 ∧
    Finsupp.single (3 : Fin 11) 2 ∉ interfaceBasis 1 := by
  simp [interfaceBasis, mem_fullBasis, NormalFaceBasis.term_degree_exact,
    QuotientNormalForm.Normal, Finsupp.single_apply]

-- A nonzero shared offset changes the objective and terminal condition,
-- while asymmetric neighboring potentials keep the interface sign visible.
example : evalCell 0 x0 (shifted 3 (C 5)) = -8 := by
  rw [evalCell_shifted]
  norm_num [evalCell]

example : -terminalRestriction (shifted 3 (X none + C 5)) = X () + C 8 := by
  rw [terminal_shifted]
  simp [terminalRestriction, map_ofNat]
  ring

example : atXi 0 (shifted 3 (C 7)) - atXi 1 (shifted 3 (X none + C 2)) = C (-4) := by
  rw [interface_shifted]
  simp [atXi, map_ofNat]
  ring

-- Constant cancellation is covered even at the degree-zero boundary.
example : (shifted 3 (C (-3))).totalDegree ≤ 0 := by
  rw [shifted_degree_iff]
  simp

example {P : ExposurePartition} {U : ℝ} {d : ℕ} {W : ℕ → CellPoly}
    (h : Feasible P U d W) : PotentialFeasible P U d 3 (fun j => shifted 3 (W j)) :=
  (potential_shifted_iff P U d 3 W).2 h

-- The independently defined V,n optimum inherits monotonicity by equality.
example (P : ExposurePartition) (U : ℝ) : Monotone (potentialOptimum P U) := by
  intro d e hde
  rw [potentialOptimum_eq, potentialOptimum_eq]
  exact optimum_mono P U hde

-- Zero charge is represented once, and constants use the full interval basis.
example : GramCone (fullBasis 0) (C 7) := by
  have h := GramCone.monomial (a := 0) (d := 0)
    (by simp [mem_fullBasis, term, QuotientNormalForm.Normal]) (s := 7) (by norm_num)
  simpa [term] using h

-- Both u and its conjugate have odd control parity, but only one charge
-- is retained. Unequal positive weights must add to 5, not double to 10.
example : GramCone (fullBasis 1) (C 5 * X 1 * X 2) := by
  let a : Fin 2 → Fin 11 →₀ ℕ := ![Finsupp.single 1 1, Finsupp.single 2 1]
  let s : Fin 2 → ℝ := ![2, 3]
  have h := GramCone.scalar_family Finset.univ a s (d := 1) (by
    intro i _
    fin_cases i <;> simp [a, mem_fullBasis, NormalFaceBasis.term_degree_exact,
      QuotientNormalForm.Normal, Finsupp.single_apply]) (by
    intro i _
    fin_cases i <;> norm_num [s])
  convert h using 1
  simp [a, s, Fin.sum_univ_two, term, Fin.prod_univ_succ,
    QuotientCertificate.conjugate_X, ConjugateGram.swap, map_ofNat]
  ring

-- Nonnegative weights matter: a negative constant cannot enter any Gram cone.
example (d : ℕ) : ¬ GramCone (fullBasis d) (C (-1)) := by
  intro h
  have hn := h.eval_nonneg 0 (x := representative) representative_mem.1
    (u := 1) (by simp)
  norm_num at hn

-- Absorption preserves the base certificate and the precise interval multiplier.
example {p : MixedPoly} (hp : OccupationCone 1 p) :
    OccupationCone 1 (p + X 0 * (1 - X 0) * C 7) := by
  have h := hp.absorb_scalar_family ({0} : Finset ℕ) (fun _ => 0) (fun _ => 7)
    (by intro i _; simp [mem_fullBasis, term, QuotientNormalForm.Normal])
    (by intro i _; norm_num)
  simpa [term] using h

end CZExposure.ConcretePartitioned
