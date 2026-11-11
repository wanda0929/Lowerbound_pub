import RequestProject.AppendixE.TerminalCertificate

noncomputable section
namespace CZExposure.TerminalCertificate
open MvPolynomial Complex

#print axioms orbit_of_mem
#print axioms invariant_value
#print axioms eval_terminalRestriction
#print axioms terminalRestriction_on_orbit
#print axioms terminalRestriction_stationary
#print axioms constant_square
#print axioms stationary_terminal
#print axioms constantGram_psd
#print axioms constantGram_identity
#print axioms stationary_terminal_gram
#print axioms stationary_embedding
#check @stationary_terminal_gram

run_cmd do
  for name in [``orbit_of_mem, ``terminalRestriction_on_orbit,
      ``stationary_terminal_gram, ``stationary_embedding] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- A non-real target phase: g1=i requires g2=+1, not -1.
example : ∃ α, qubitGauge α representative = mkState I 0 1 0 := by
  apply orbit_of_mem
  norm_num [XCZ, Xset]

-- Keep ξ, replace Re g2 by -1, and kill the excited amplitude factor.
example : terminalRestriction
    (X none ^ 3 + C 2 * X (some 4) + X (some 2) * X (some 0)) =
      (X () ^ 3 - 2 : UniPoly) := by
  norm_num [terminalRestriction, representative, mkState]
  change X () ^ 3 + C 2 * C (-1) + C 0 = (X () ^ 3 - 2 : UniPoly)
  norm_num [show (C (2 : ℝ) : UniPoly) = 2 from map_ofNat C 2]
  ring

-- The constant basis element exists even at order zero.
example : (constantGram 0 3).PosSemidef ∧
    (∑ i, ∑ j, monomialColumn 0 i * C (constantGram 0 3 i j) * monomialColumn 0 j) =
      (C 3 : UniPoly) :=
  ⟨constantGram_psd 0 (by norm_num), constantGram_identity 0 3⟩

-- Wrong-sign terminal constants must not produce positive-semidefinite blocks.
example : ¬ (constantGram 3 (-2)).PosSemidef := by
  simp [constantGram, Matrix.posSemidef_diagonal_iff]
  exact ⟨0, by norm_num⟩

end CZExposure.TerminalCertificate
