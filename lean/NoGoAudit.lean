import LowerBoundCZ.NoGo

/-! The no-go construction must not rely on project axioms or admitted proofs.
Run with `lake env lean NoGoAudit.lean` from `lean/`. -/

open LowerBoundCZ Complex

-- Nonunit couplings detect the former erroneous factor |c| instead of 1/|c|.
example : chirpExposureClosed 2 1 1 = Real.pi / 4 := by
  norm_num [chirpExposureClosed]
  ring

example : chirpExposureClosed (1 / 2) 1 1 = Real.pi := by
  norm_num [chirpExposureClosed]
  ring

-- Positive and negative detunings exercise both halves of the phase range.
example : phaseFactor 2 3 = 2 / 5 := by
  norm_num [phaseFactor, omega]

example : phaseFactor 2 (-3) = 8 / 5 := by
  norm_num [phaseFactor, omega]

-- A target beyond the principal-argument range remains a valid unit phase.
example : ∀ ε > 0, ∃ L : ClosedLoop 1,
    L.exposure < ε ∧ L.g L.S = exp (((3 : ℝ) / 2 * Real.pi) * I) := by
  simpa only [ofReal_mul, ofReal_div, ofReal_ofNat] using
    theorem_free 1 (by norm_num) (Q := 3 / 2) (by norm_num) (by norm_num) rfl

-- Two zero-detuning returns close at +1, not at principal argument 2π.
example : ∃ L : ClosedLoop 1,
    L.exposure = chirpExposure (kappa 1) 0 2 ∧ L.g L.S = 1 := by
  simpa [phaseFactor, ofReal_mul] using
    exists_chirp_loop 1 (by norm_num) 0 2 (by norm_num)

#print axioms exists_chirp_loop
#print axioms exists_detuning_for_phase
#print axioms chirpExposure_eq_closed
#print axioms theorem_free
#print axioms theorem_relax'

run_cmd do
  for name in [``exists_chirp_loop, ``exists_detuning_for_phase,
      ``chirpExposure_eq_closed, ``chirpExposureClosed_tendsto_zero,
      ``theorem_free_trivial_zero, ``theorem_free, ``theorem_relax, ``theorem_relax'] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
