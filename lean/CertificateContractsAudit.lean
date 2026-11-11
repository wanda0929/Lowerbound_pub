import LowerBoundCZ.PinnedCertificates
import LowerBoundCZ.SlackReachability
import LowerBoundCZ.SlackCalculus
import LowerBoundCZ.SlackEndpoint
import LowerBoundCZ.PopulationBarrier
import LowerBoundCZ.SlackAllocation
import LowerBoundCZ.PinnedAllocations
import LowerBoundCZ.SlackCrossing
import LowerBoundCZ.PinnedInterfaces
import LowerBoundCZ.OccupationLedger
import LowerBoundCZ.PinnedRegions
import LowerBoundCZ.OccupationCoverage
import LowerBoundCZ.MandatoryPrefix
import LowerBoundCZ.StrengthenedBound

open LowerBoundCZ.Certification

-- Data lengths are kernel-checked: the decoder's fallback values must never
-- supply missing entries in the finite ranges used by the pinned payloads.
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
example : LowerBoundCZ.CertificateData.phases.size = 12672 := by
  simp only [LowerBoundCZ.CertificateData.phases, Array.size_append]
  decide
example : LowerBoundCZ.CertificateData.basis.size = 776 := by
  simp only [LowerBoundCZ.CertificateData.basis, Array.size_append]
  decide
example : LowerBoundCZ.CertificateData.multipliers.size = 3880 := by
  simp only [LowerBoundCZ.CertificateData.multipliers, Array.size_append]
  decide
example : LowerBoundCZ.CertificateData.center.size = 5 := by decide
example : LowerBoundCZ.CertificateData.inverse.size = 25 := by decide
example : LowerBoundCZ.CertificateData.jacobianLower.size = 25 := by decide
example : LowerBoundCZ.CertificateData.jacobianUpper.size = 25 := by decide

-- The new mathematical bridge must not inherit either legacy bound axiom.
#print axioms labCstar_le_activeCstar
#print axioms Lower.Checks.active_lower
#print axioms LabPulse.compress
#print axioms labCstar_eq_activeCstar
#print axioms Lower.Checks.lab_lower
#print axioms Pinned.order7_degree
#print axioms Pinned.order7_invariant
#print axioms Pinned.order7_objective
#print axioms Pinned.order7_lab_lower_of_grams
#print axioms Upper.AD.jacobian_eq_fderiv
#print axioms Upper.Checks.exists_root
#print axioms Upper.pulse_of_root
#print axioms Pinned.upper_lab_bound
#print axioms Pinned.lab_window
#print axioms Slack.dark_box_excludes
#print axioms Slack.slack_telescope
#print axioms Slack.profile_credit
#print axioms Slack.endpoint_composition
#print axioms Slack.endpoint_pos
#print axioms Slack.population_budget
#print axioms Slack.population_box_excludes

run_cmd do
  for name in [``toLab_exposure, ``labCstar_le_activeCstar, ``Lower.Checks.active_lower,
      ``LabPulse.compress, ``LabPulse.compress_duration, ``LabPulse.compress_duration_le,
      ``LabPulse.compress_terminal, ``LabPulse.compress_path, ``LabPulse.compress_exposure,
      ``LabPulse.compress_exposure_le, ``activeCstar_le_labCstar,
      ``labCstar_eq_activeCstar, ``Lower.Checks.lab_lower, ``Pinned.order7_lab_lower,
      ``GramBridge.gram_congruence, ``GramBridge.RawBlock.polynomial_eq,
      ``GramBridge.RawBlock.cone, ``GramBridge.Checks.feasible,
      ``Pinned.order7_degree, ``Pinned.order7_invariant, ``Pinned.order7_initial_support,
      ``Pinned.order7_initial_coefficients, ``Pinned.order7_objective,
      ``Pinned.order7_lab_lower_of_grams, ``Upper.AD.Expr.hasFDerivAt,
      ``Upper.AD.program_eval, ``Upper.AD.jacobian_eq_fderiv,
      ``Upper.AD.Enclosures.analyticChecks, ``Upper.Checks.inverse_injective,
      ``Upper.Checks.exists_root, ``Upper.segmentPath_deriv,
      ``Upper.physicalSegment_exposure, ``Upper.exists_assembly,
      ``Upper.residual_zero_terminal, ``Upper.pulse_of_root,
      ``Pinned.upper_lab_bound, ``Pinned.lab_window,
      ``Slack.dark_deriv, ``Slack.dark_speed_identity, ``Slack.dark_budget,
      ``Slack.dark_box_excludes, ``Slack.polynomial_integral,
      ``Slack.occupation_integral, ``Slack.slack_telescope,
      ``Slack.profile_integral, ``Slack.profile_credit, ``Slack.exposure_crossings,
      ``Slack.endpoint_composition, ``Slack.endpoint_pos, ``Slack.endpoint_excludes,
      ``Slack.barrierSeries_sqrt_le, ``Slack.barrierG_deriv, ``Slack.barrierG_closed,
      ``Slack.barrier_speed_le, ``Slack.population_budget,
      ``Slack.barrierEnergy_rat, ``Slack.population_rational_excludes,
      ``Slack.population_box_excludes, ``Slack.gram_value_mono, ``Slack.gram_budget,
      ``Slack.AllocatedBlock.eval_le, ``Slack.tensorMixed_nonneg,
      ``Slack.allocation_local_slack, ``Slack.AllocationRegion.local_slack,
      ``Slack.AllocationRegion.trajectory_slack, ``PinnedAllocation.widths,
      ``PinnedAllocation.checks, ``PinnedAllocation.trajectory_slack,
      ``Slack.eval_interfacePolynomial, ``Slack.InterfaceCertificate.credit,
      ``Slack.crossings_exist, ``Slack.crossings_exist_of_grams,
      ``Slack.Crossings.coordinates, ``Slack.Crossings.cell_domain,
      ``Slack.Crossings.jump, ``Slack.Crossings.telescope,
      ``Slack.Crossings.credit, ``Slack.Crossings.credited_telescope,
      ``PinnedInterface.certificate, ``PinnedInterface.excluded_iff,
      ``PinnedInterface.grid_cover, ``PinnedInterface.population_cover,
      ``PinnedInterface.retained, ``PinnedInterface.point_mem,
      ``PinnedInterface.eval_coord, ``PinnedInterface.crossing_credit,
      ``PinnedInterface.credited_telescope, ``OccupationLedger.index_unique,
      ``OccupationLedger.index_lt, ``OccupationLedger.primitive_credit,
      ``OccupationLedger.interval_credit, ``OccupationLedger.prefix_sum_le,
      ``OccupationLedger.traversal_exists, ``OccupationLedger.occupation_credit,
      ``OccupationLedger.slack_nonneg, ``OccupationLedger.credited_telescope,
      ``PinnedRegion.checks, ``PinnedRegion.trajectory_slack,
      ``OccupationCoverage.grid_cover, ``OccupationCoverage.excludedQ_iff,
      ``OccupationCoverage.primitive_derivative, ``OccupationCoverage.not_excluded,
      ``OccupationCoverage.retained_cover, ``OccupationCoverage.xi_mem,
      ``OccupationCoverage.normalized_coordinate, ``OccupationCoverage.selected_checks,
      ``OccupationCoverage.rate_eq_derivative, ``OccupationCoverage.pointwise_slack,
      ``OccupationCoverage.credited_telescope, ``MandatoryPrefix.prefix_credit,
      ``MandatoryPrefix.endpoint_positive, ``MandatoryPrefix.endpoint_value,
      ``MandatoryPrefix.threshold, ``MandatoryPrefix.traversal,
      ``MandatoryPrefix.credited_telescope, ``Strengthened.endpoint_value,
      ``Strengthened.endpoint_matches, ``Strengthened.pulse_lower,
      ``Strengthened.active_lower, ``Strengthened.lab_lower, ``Strengthened.lab_window] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- V=-W: the interface is left minus right, not the reverse.
example (x : CZExposure.State) :
    Slack.interfaceSlack (fun j => MvPolynomial.C ((j : ℝ)^2)) 2 x = -5 := by
  norm_num [Slack.interfaceSlack, CZExposure.evalCell]

-- Both requested orders concern the actual integral-model trajectory.
example (γ : ActivePulse) (s : ℝ) (hs : s ∈ Set.Icc 0 γ.S) :
    Slack.barrierValue 8 (γ.x s) ≤ min (γ.cumI s) (γ.exposure-γ.cumI s) ∧
    Slack.barrierValue 64 (γ.x s) ≤ min (γ.cumI s) (γ.exposure-γ.cumI s) :=
  ⟨Slack.population_budget 8 γ hs, Slack.population_budget 64 γ hs⟩

-- Complex source columns and off-diagonal terms must not be replaced by
-- real parts of columns or by a diagonal-only quadratic form (19 ≠ 21).
example : (CZExposure.SymmetryGram.value
    ((!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal)
    ![1 + Complex.I, 2 - Complex.I]).re = 21 := by
  norm_num [CZExposure.SymmetryGram.value, Fin.sum_univ_two, Complex.mul_re,
    Complex.mul_im]

-- Two separately dominated projections of the same block cannot each
-- consume weight 1. A per-projection cap would incorrectly accept this.
example : ¬ (∑ _ : Fin 2, (1 : ℚ)) ≤ 1 := by norm_num [Fin.sum_univ_two]

-- Conversely a saturated shared budget is allowed, including two projections
-- of the same Q. This exercises equality, not just a strictly slack budget.
example {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.PosSemidef) (z : Fin 2 → ℂ) :
    (∑ k : Fin 2, (![3/4, 1/4] k : ℝ) *
      (CZExposure.SymmetryGram.value (Q.map Complex.ofReal) z).re) ≤
      (CZExposure.SymmetryGram.value (Q.map Complex.ofReal) z).re := by
  apply Slack.gram_budget Q (fun _ : Fin 2 => Q) ![3/4, 1/4] hQ
  · intro k; simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef)
  · intro k; fin_cases k <;> norm_num
  · norm_num [Fin.sum_univ_two]

-- Independent central-binomial values detect a wrong recurrence or index.
example : Slack.barrierCoeff 8 = 6435/32768 := by norm_num [Slack.barrierCoeff]
example : Slack.barrierCoeff 64 =
    11975573020964041433067793888190275875/170141183460469231731687303715884105728 := by
  norm_num [Slack.barrierCoeff]

-- Exact boundary and both sides; a strict test must retain equality.
example : ¬ Slack.PopulationBoxExcluded 0 1 0 (1/3) := by
  norm_num [Slack.PopulationBoxExcluded, Slack.barrierEnergy, Slack.barrierH, Slack.barrierCoeff]
example : Slack.PopulationBoxExcluded 0 1 0 (33/100) := by
  norm_num [Slack.PopulationBoxExcluded, Slack.barrierEnergy, Slack.barrierH, Slack.barrierCoeff]
example : ¬ Slack.PopulationBoxExcluded 0 1 0 (34/100) := by
  norm_num [Slack.PopulationBoxExcluded, Slack.barrierEnergy, Slack.barrierH, Slack.barrierCoeff]

-- The cross-term branch is essential here; the squared-sum test alone fails.
example : Slack.PopulationBoxExcluded 0 (1/4) 1 (3/20) ∧
    8*Slack.barrierEnergy 0 (1/4)+Slack.barrierEnergy 0 1 ≤ 72*(3/20 : ℝ)^2 := by
  norm_num [Slack.PopulationBoxExcluded, Slack.barrierEnergy, Slack.barrierH, Slack.barrierCoeff]
-- Unequal sector weights must not be silently interchanged.
example : ¬ Slack.PopulationBoxExcluded 0 (1/4) 1 (1/5) ∧
    Slack.PopulationBoxExcluded 0 1 (1/4) (1/5) := by
  norm_num [Slack.PopulationBoxExcluded, Slack.barrierEnergy, Slack.barrierH, Slack.barrierCoeff]

-- Asymmetric boxes exercise both corner signs. Boundary equality and a box
-- containing zero signed gap must be retained, not excluded by squaring.
example : Slack.DarkBoxExcluded 0 (1/10) (9/10) 1 1 := by
  norm_num [Slack.DarkBoxExcluded]
example : Slack.DarkBoxExcluded (9/10) 1 0 (1/10) 1 := by
  norm_num [Slack.DarkBoxExcluded]
example : ¬ Slack.DarkBoxExcluded 0 0 (1/2) (1/2) 1 := by
  norm_num [Slack.DarkBoxExcluded]
example : ¬ Slack.DarkBoxExcluded 1 1 0 0 2 := by
  norm_num [Slack.DarkBoxExcluded]
example : ¬ Slack.DarkBoxExcluded 0 1 0 1 0 := by
  norm_num [Slack.DarkBoxExcluded]

-- The pinned entry point accepts matrix checks only: no degree, symmetry,
-- objective equality, or final bound is supplied by the caller.
example (A : GramBridge.Archive Pinned.order7) (h : GramBridge.MatrixChecks A) :
    (5861/2000 : EReal) ≤ labCstar := Pinned.order7_lab_lower_of_grams A h

-- Both endpoints concern the same physical infimum; numerical inputs do not
-- include an existing root, a successful pulse, or either endpoint inequality.
example (A : GramBridge.Archive Pinned.order7) (hl : GramBridge.MatrixChecks A)
    (hu : Pinned.UpperChecks) :
    ((2.9305 : ℝ) : EReal) ≤ labCstar ∧
      labCstar < ((2.935875225844105 : ℝ) : EReal) := by
  convert Pinned.lab_window A hl hu using 1
  norm_num [LowerBoundCZ.upperEndpoint, EReal.coe_div]
  rfl

-- Half-amplitude compression halves exposure, rather than doubling it or
-- merely preserving it. No extra differentiability assumption is supplied.
example (γ : LabPulse) (hu : ∀ t ∈ Set.Icc 0 γ.S, ‖γ.u t‖ = 1 / 2) :
    γ.compress.exposure = γ.exposure / 2 := by
  rw [γ.compress_exposure]
  have h : (∫ t in (0 : ℝ)..γ.S, CZExposure.cost (γ.x t) * ‖γ.u t‖) =
      ∫ t in (0 : ℝ)..γ.S, CZExposure.cost (γ.x t) * (1 / 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le γ.S_nonneg] at ht
    dsimp only
    rw [hu t ht]
  rw [h, intervalIntegral.integral_mul_const]
  unfold LabPulse.exposure
  ring

-- Zero-based selected phases, with distinct values and neighboring controls.
example (fixed : Fin 12672 → ℝ) (p : Upper.Parameters) :
    Upper.phase fixed p 731 = p 1 ∧ Upper.phase fixed p 6676 = p 2 ∧
    Upper.phase fixed p 8661 = p 3 ∧ Upper.phase fixed p 11922 = p 4 ∧
    Upper.phase fixed p 730 = fixed 730 ∧ Upper.phase fixed p 732 = fixed 732 := by
  norm_num [Upper.phase]

-- A zero-duration segment preserves arbitrary complex amplitudes and cost.
example (k : ℕ) (phase : ℝ) (z : Upper.SectorRecord) :
    Upper.segment k 0 phase z = z := by
  cases z
  simp [Upper.segment]

-- A quarter rotation in sector 1 with phase zero sends ground to -i Rydberg.
-- The integrated population is pi/2; this detects coupling and cost factors.
example : Upper.segment 1 Real.pi 0 ⟨1, 0, 0⟩ = ⟨0, -Complex.I, Real.pi / 2⟩ := by
  norm_num [Upper.segment, show 2 * (Real.pi * (1 / 2)) = Real.pi by ring,
    show Real.pi * (1 / 2) = Real.pi / 2 by ring]
  constructor
  · change starRingEnd ℂ 1 = 1
    exact map_one _
  · rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

-- A nonzero phase distinguishes u from its conjugate in the Rydberg equation.
example : (Upper.segment 1 Real.pi (Real.pi / 2) ⟨1, 0, 0⟩).rydberg = -1 := by
  norm_num [Upper.segment, show Real.pi * (1 / 2) = Real.pi / 2 by ring]
  change Complex.I * starRingEnd ℂ Complex.I = 1
  simp [Complex.conj_I, mul_neg]

-- Same negative charge, but opposite control parity. Omitting the parity
-- sign changes the transported off-diagonal entry from -1 to +1.
open CZExposure GramBridge
open scoped Matrix

private noncomputable def parityBlock : RawBlock where
  size := 2
  columns := 2
  charge := (0, -1)
  powers := fun i => Finsupp.onFinset Finset.univ
    (fun j => if i = 0 then if j = 4 then 1 else 0 else if j = 2 ∨ j = 6 then 1 else 0)
    (by simp)
  weights := !![1, 0; 0, 1]
  entries := !![(2, 0), (1, 0); (1, 0), (3, 0)]

private theorem parityValid : parityBlock.Valid (ConcretePartitioned.fullBasis 2) where
  nonempty := by decide
  keep := by norm_num [parityBlock, ConjugateGram.Keep]
  charge_eq := by
    intro i
    fin_cases i <;> decide
  membership := by
    intro i
    rw [ConcretePartitioned.mem_fullBasis, ConjugateGram.partner_degree,
      NormalFaceBasis.term_degree_exact]
    unfold QuotientNormalForm.Normal
    fin_cases i <;> decide

example :
    let a := parityBlock.toBlock parityValid
    (a.transportᴴ * a.matrix * a.transport)
      (a.indices ⟨0, by decide⟩) (a.indices ⟨1, by decide⟩) = -1 := by
  let a := parityBlock.toBlock parityValid
  have h01 : a.indices (0 : Fin 2) ≠ a.indices (1 : Fin 2) := by
    intro h
    have hx := congrArg (fun v => v.val (3 : Fin 11)) h
    change (1 : ℕ) = 0 at hx
    contradiction
  have hp0 : ConjugateGram.paritySign (a.indices (0 : Fin 2)).val = 1 := by
    change (if Odd (0 : ℕ) then (-1 : ℝ) else 1) = 1
    norm_num
  have hp1 : ConjugateGram.paritySign (a.indices (1 : Fin 2)).val = -1 := by
    change (if Odd (1 : ℕ) then (-1 : ℝ) else 1) = -1
    norm_num
  have hw : a.weights = (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    change ((!![1, 0; 0, 1] i j : ℤ) : ℝ) = _
    fin_cases i <;> fin_cases j <;> norm_num
  have hm : a.matrix = (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    change scalar (!![(2, 0), (1, 0); (1, 0), (3, 0)] i j) = _
    fin_cases i <;> fin_cases j <;> norm_num [scalar]
  have ht (i j : Fin 2) : a.transport i (a.indices j) = (!![1, 0; 0, -1] : Matrix _ _ ℝ) i j := by
    unfold Block.transport
    rw [hw]
    change (∑ k : Fin 2, if a.indices k = a.indices j then
      (!![1, 0; 0, 1] : Matrix _ _ ℝ) i k * ConjugateGram.paritySign (a.indices k).val else 0) = _
    rw [Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> norm_num [h01, Ne.symm h01, hp0, hp1]
  change (a.transportᴴ * a.matrix * a.transport)
    (a.indices (0 : Fin 2)) (a.indices (1 : Fin 2)) = -1
  rw [hm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  change (∑ k : Fin 2, (∑ l : Fin 2, a.transport l (a.indices (0 : Fin 2)) *
    (!![2, 1; 1, 3] : Matrix _ _ ℝ) l k) * a.transport k (a.indices (1 : Fin 2))) = -1
  simp_rw [ht]
  norm_num [Fin.sum_univ_two]
