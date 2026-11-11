import RequestProject.AppendixE.ConcreteStationary

noncomputable section
namespace CZExposure.ConcreteStationary
open MvPolynomial TerminalCertificate
open scoped Matrix ComplexOrder

#print Feasible
#check @of_stationary
#print axioms of_stationary
#check @Feasible.weak_duality
#print axioms Feasible.weak_duality
#print axioms Feasible.le_Cstar
#print optimum
#check @stationary_convergence
#print axioms stationary_convergence
#check @Feasible.mono
#print axioms Feasible.mono
#print axioms optimum_mono

run_cmd do
  for name in [``of_stationary, ``value_re_nonneg, ``Feasible.drift_nonneg,
      ``Feasible.terminal_nonpos, ``Feasible.weak_duality, ``Feasible.le_Cstar,
      ``Lunsplit_le_optimum, ``optimum_le_Cstar, ``optimum_nonneg,
      ``stationary_convergence, ``sector_mono, ``retained_mono,
      ``Feasible.mono, ``optimum_mono] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- The same source polynomial is feasible at the same order, including the
-- terminal block; no supplied concrete matrix or order increase is needed.
example {d : ℕ} (hd : 1 ≤ d) : Feasible d 0 :=
  of_stationary (stationaryFeasible_zero hd)

-- Positive constant W has zero derivative but violates the terminal sign.
-- Drift feasibility alone must not make it a concrete certificate.
example (d : ℕ) : ¬Feasible d (C 1) := by
  intro h
  have ht := h.terminal_nonpos representative_mem
  norm_num at ht

-- Terminal soundness covers a non-real phase on the target orbit, not just
-- the real representative at which the terminal matrix was constructed.
example {d : ℕ} {W : StatePoly} (h : Feasible d W) :
    eval (mkState Complex.I 0 1 0) W ≤ 0 := by
  apply h.terminal_nonpos
  norm_num [XCZ, Xset]

-- Imaginary components must contribute to positivity, including cross terms.
example : (SymmetryGram.value
    ((!![1,-2;-2,4] : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal)
    ![1 + Complex.I, 2 + 3 * Complex.I]).re = 34 := by
  norm_num [SymmetryGram.value, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

-- Soundness can be used directly from concrete witnesses, without obtaining
-- an abstract StationaryFeasible proof or invoking of_stationary.
example {d : ℕ} {W : StatePoly} (h : Feasible d W) (γ : Pulse) :
    eval x0 W ≤ γ.exposure ∧ (eval x0 W : EReal) ≤ Cstar :=
  ⟨h.weak_duality γ, h.le_Cstar⟩

-- Bounds refer to the independently defined concrete supremum, in the
-- required direction, at every positive order.
example {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ optimum d ∧ Lunsplit d ≤ optimum d ∧ optimum d ≤ Cstar :=
  ⟨optimum_nonneg hd, Lunsplit_le_optimum d, optimum_le_Cstar d⟩

-- A supplied successful pulse bounds the entire concrete optimum, not just
-- one chosen witness. No attainment or finite-optimum assumption is needed.
example (d : ℕ) (γ : Pulse) : optimum d ≤ (γ.exposure : EReal) :=
  (optimum_le_Cstar d).trans (iInf_le _ γ)

-- Nesting applies to arbitrary concrete certificates, not only those
-- constructed by of_stationary. It includes order zero and skipped orders.
example {W : StatePoly} (h : Feasible 0 W) : Feasible 1 W := h.mono (by omega)
example {W : StatePoly} (h : Feasible 2 W) : Feasible 5 W := h.mono (by omega)
example (d : ℕ) : optimum d ≤ optimum (d + 1) := optimum_mono (by omega)

-- A sector gains columns at the degree boundary; treating its old and new
-- index sets as identical would lose this monomial.
example : let a := Finsupp.single (5 : Fin 11) 2
    a ∈ ConjugateGram.sector 2 (SymmetryGram.monomialCharge a) ∧
    a ∉ ConjugateGram.sector 1 (SymmetryGram.monomialCharge a) := by
  simp [ConjugateGram.sector, NormalFaceBasis.mem_basis,
    NormalFaceBasis.term_degree_exact, QuotientNormalForm.Normal,
    NormalFaceBasis.Excited, Finsupp.single_apply]

end CZExposure.ConcreteStationary
