# Lean 4 formalization of the manuscript proofs

For the integrated main-bound, NoGo, Appendix B/D and conditional Appendix E
snapshot, see [Unified acceptance](UnifiedAcceptance.md). Its receipt and logs
distinguish current validation from the historical results described below.

This library formalizes the mathematical proofs in `main.tex` and
`control-appendices.tex` for
*Certifying the Rydberg-exposure limit of a globally driven controlled-Z gate*.

Both libraries now use Lean/mathlib 4.28. The [Appendix E project](appendix-e/README.md)
is a local Lake dependency and can still be built independently. Its concrete
integral model and weak-duality proofs are used by the new certificate contracts.

**The historical headline theorem is not an end-to-end verification.** It
still depends on the legacy bound axioms below. The current manuscript has
an order-7 base bound of 2.9305 and a slack-strengthened bound of
2.931287735220; the historical Lean theorem only states 2.93.

[Model and certificate contracts](CertificateContracts.md) records the new
interfaces and the remaining analytic and numerical obligations. The contracts
introduce no axioms. `PinnedCertificates` now supplies the actual order-7
potential and upper-witness payloads; it does not assert their `Checks` proofs.
Both numerical checkers were rerun. `GramBridge.Checks.feasible` now proves
the lower Gram-to-cone correspondence, including conjugate-charge and parity
conversion. The pinned potential's degree, all three symmetries and exact
objective 5861/2000 are proved in Lean; its lower-bound entry point accepts
only `GramBridge.MatrixChecks`. The upper analytic chain is also proved:
forward-mode differentiation, a root in the certified closed box, exact
segment dynamics/cost, physical pulse construction and CZ closure.
`Pinned.upper_lab_bound` takes only explicit numerical enclosures.
`Pinned.lab_window` combines them into
**2.9305 ≤ labCstar < 2.935875225844105** for the same integral model.
This remains the base-window entry point. The new `Strengthened.lab_window`
proves **2.931287735220 ≤ labCstar < 2.935875225844105**, conditional on the
explicit finite certificate checks. It assumes no physical slack inequality,
mandatory traversal or strengthened lower bound. It is not an unconditional
kernel-checked instance of every numerical certificate input.
The strengthened-bound modules now prove the physical dark-box exclusion,
the `W_8`/`W_64` population barriers and their rational box exclusions,
exact slack telescoping, exposure-profile integration (including stalls),
and pinned endpoint-polynomial composition and positivity. The population
barrier proof is uniform in the series order and handles zero population.
`SlackAllocation` now proves the implication from source matrix domination,
per-original-block budgets and tensor coefficient identities/signs to the
pinned potential's physical local slack inequality. `bind_allocations.py`
now generates `AllocationData`: all 736 original cell-2 Gram blocks (including
unallocated blocks), 1,078 projections, and 1,024 fixed replacement regions.
`PinnedAllocation.trajectory_slack` applies the bridge to these fixed data,
conditional only on `PinnedAllocation.NumericalChecks`: finite PSD, matrix-order,
budget, polynomial-identity and coefficient-sign checks. It does not accept an
arbitrary archive or an assumed physical slack inequality. The data instance is
now concrete; an unconditional Lean proof of the numerical checks is not
claimed. The final conditional assembly is in `StrengthenedBound`.
`SlackCrossing` now derives the four ordered crossings from the base
Gram checks, identifies the left/right local coordinates as 1/0, and proves
the exact five-cell accounting identity. Finite interface matrix and Bernstein
checks imply the crossing credits in that identity; they are not assumed as
physical inequalities. The last cell stops at the actual pulse endpoint,
not at the exposure ceiling. `PinnedInterfaces` now binds all 536 original
interface blocks and their combined diagonal allocations. Its four fixed
credits apply on the 64×64 population grid: closed-box coverage and physical
exclusion by W64 are proved in Lean, including population 0, 1 and grid edges.
`PinnedInterface.crossing_credit` and `credited_telescope` require only fixed
finite numerical checks and the candidate exposure cap 2.932, not a box-choice
or coverage oracle. `ProfileData` now binds the final 320 occupation profiles
and one tail profile, selecting the 16 allocation and 32 disjoint dark
replacements once. `OccupationLedger` proves their primitive integration,
nonoverlapping index accounting, and insertion into the five-cell/interface
total, conditional on the local profile inequalities and a mandatory-prefix
traversal. It constructs that traversal from continuity once exposure reaches
the tail endpoint 2.931285651554. `MandatoryPrefix` now proves this threshold
using only the first 319 profiles, already reached at the base bound 2.9305,
plus the four interface credits and a positive terminal polynomial.
`PinnedRegions` now binds all five cells'
3,680 original Gram blocks, 6,190 used projections and 9,728 remaining retained
regions. Its finite matrix/budget/identity/sign checks imply the physical local
profile inequality on each such box, covering inherited, W8-retained,
dark-retained and tail profiles. The 16 replacements remain in `PinnedAllocations`.
`OccupationCoverage` now selects a retained closed box for every physical state
in a profile's exposure interval under the counterexample cap 2.932, using the
proved W8/dark exclusions. It proves the normalized-coordinate substitution
and identifies the local Bernstein rate with the derivative of the ledger
primitive. Its `credited_telescope` discharges the ledger's local `hpoint`
premise for all 321 profiles, including replacements. New inputs are finite
fixed-table, endpoint and polynomial-coefficient checks, not physical coverage
or local-inequality assumptions. `MandatoryPrefix.traversal` discharges the
mandatory-prefix premise; its `credited_telescope` needs neither traversal nor
local-inequality assumptions from the caller. The bootstrap omits slots 319
and 320 rather than using their unproved traversal circularly.
`StrengthenedBound` now connects the **final** endpoint polynomial to the full
ledger and proves the bound for the active infimum and laboratory `labCstar`.
Each active pulse has strictly greater exposure than the lower endpoint;
the infimum has a non-strict lower bound, without assuming attainment.
All finite checks remain explicit external inputs, not unconditional kernel
instances. The new endpoint identity was checked coefficient-by-coefficient
against the hash-pinned original potential and final certificate.
The trust boundary and validation scope are in
[`CertificateContracts.md`](CertificateContracts.md#strengthened-bound-proof-and-finite-checks).
The numerical matrix archive, PSD/identity checks and interval enclosures remain external inputs, not an
unconditional Lean certificate instance. See the contracts document for the
pinned hashes, decoder and exact scope of these checks.
In particular, `Lower.Checks.active_lower` proves the implication from concrete
SOS conditions to the integral-model bound without either legacy bound axiom.
`LabPulse.compress` now connects the laboratory model to Appendix E's proved
active-time normalization, preserving the endpoint and not increasing cost or
duration. `labCstar_eq_activeCstar` proves equality of the two integral-model
infima, and `Lower.Checks.lab_lower` transfers the certificate bound to the
laboratory problem. These proofs introduce no extra assumptions or axioms.

## Build

```bash
cd lean
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get   # optional; uses the mathlib cache
lake build
lake env lean NoGoAudit.lean
lake env lean AppendixEAudit.lean
lake env lean CertificateContractsAudit.lean
```

## Paper-to-Lean map

| Paper | Lean |
|---|---|
| Lemma bang (maximum-amplitude reduction) | `bang_cost_le_lab`, `lemma_bang_infima` |
| Lemma master (metric line element) | `polar_ndot`, `polar_Phidot`, `master_geom`, `finsler_density` |
| Lemma osc (driven oscillators) | `oscillator_eq`, `kinetic_identity`, `osc_cost_density` |
| Lemma mu (μ-lock) | `mu_formula`, `mu_lock` |
| Lemma ratio (nonlocal phase) | `riccati`, `syncError_deriv`, `phase_vel`, `zeta_dot` |
| Theorem free (per-sector phases) | `theorem_free_trivial_zero`, `chirpExposureClosed_tendsto_zero`, `theorem_free` |
| Theorem relax (lock-free infimum) | `theorem_relax`, `theorem_relax'` |
| Theorem fiber (companion-state bound) | `fiber_pointwise`, `fiber_pointwise_ratio`, `abs_overlap_le_moduli`, `cFib` |
| Schmidt integral | `schmidt_algebra`, `schmidt_indefinite_eval` |
| Theorem split_exact (five-cell dual) | `split_weak_duality`, `split_exact_of_barrier`, `split_exact_bound` |
| Auditor PSD residual | `residual_quadratic_lower`, `residual_pos`, `gram_residual_pos` |
| Interval / Krawczyk upper bound | `newton_fixed_is_root`, `unique_root_of_contraction`, `Cstar_lt_upperEndpoint` |
| Headline window | `certified_window`, `certified_gap_lt` |
| First-tier physical upper bound | `Certification.Upper.AD.jacobian_eq_fderiv`, `Upper.Checks.exists_root`, `Upper.pulse_of_root`, `Pinned.upper_lab_bound` (all under `Certification`) |
| First-tier physical base window | `Certification.Pinned.lab_window` — external matrix/interval inputs, no legacy bound axioms |
| Appendix E (SOS completeness, PARTIAL/CONDITIONAL) | `LowerBoundCZ.AppendixE` — see [`AppendixE.md`](AppendixE.md) |

## Trust boundary

The historical result imports the following assumptions rather than proving
them. Their comments describe the intended external provenance, not a checked
archive-to-Lean bridge. In particular, items 2 and 3 already assert physical
conclusions and are too broad for the new first-tier certificate interface.
The Appendix E results retain their separately documented explicit inputs.

1. **`fiveCellExactDual`** — asserts existence of abstract barrier traces and
   segment costs with value `293/100`. Its type does not encode the archived
   polynomials, Gram matrices or physical trajectories. The comment refers
   to the external order-6 audit; this is not an archive-to-Lean bridge.
2. **`split_exact_competitive`** — directly assumes exposure at least 2.93
   for every competitive exact-CZ trajectory (`C < U`). It does not derive
   this fact from `fiveCellExactDual`; that axiom is not used by the headline.
3. **`intervalKrawczykCertificate`** — directly assumes existence of an exact
   CZ trajectory with exposure below `2.935875225844105`. The generic Newton
   lemmas do not connect the archived interval calculation to this witness.

The two-sided window follows from assumptions 2 and 3. Abstract telescoping,
residual positivity and global-contraction lemmas are separately proved, but
do not by themselves supply the missing certificate bridges. The no-go
corrections below do not discharge those assumptions.

The no-go construction no longer uses external facts. `exists_chirp_loop`
constructs the rotating-frame solution and checks the ODE, normalization,
control bound, initial and terminal conditions, and exposure integral.
Its terminal phase is expressed by `g(S) = exp(i Φ)`, not by an equality
between the principal argument and an unrestricted real phase.
`exists_detuning_for_phase` supplies an explicit inverse of the phase map.
`chirpExposure_eq_closed` proves the closed form with prefactor
`π / (2 |c|)`, and `chirpExposureClosed_tendsto_zero` proves its decay.
`theorem_free` and `theorem_relax'` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

`NoGoAudit.lean` enforces that transitive dependency allowlist and checks
nonunit couplings, both signs of detuning, a phase beyond the principal-arg
range, and a two-return loop. The earlier principal-arg and exposure axioms
each allowed a proof of `False`; both were reproduced on the unchanged
source before replacing all three chirp axioms with proofs.
