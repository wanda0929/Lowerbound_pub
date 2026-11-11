# Model and certificate contracts

Scope: first-tier verification, with external numerical certificate checks but
Lean proofs of their implications for physical pulses. The interfaces are in
`LowerBoundCZ/CertificateContracts.lean`, namespace `LowerBoundCZ.Certification`.
They introduce no axioms. `PinnedCertificates.lean` now instantiates both
payloads from exact archived data, but does not assert either `Checks` proof.

## Target and manuscript snapshot

The inspected `main.tex` SHA-256 is
`2422672d783027c09268b52be0530c93a7a7bcc109b13f011b3dda7eced2202b`.
The current manuscript is stronger than the historical Lean result:

| Result | Exact lower endpoint | Status here |
| --- | --- | --- |
| Historical order-6 certificate | 2.93 | Recovered archive; integration milestone only |
| Current Theorem `thm:split_exact`, order 7 | 2.9305 | Gram-to-cone transport proved; external algebraic inputs remain explicit |
| Current Theorem `thm:slack_strengthened` | 2.931287735220 | `Strengthened.lab_lower` proved, conditional on explicit finite certificate checks |

The upper endpoint is 2.935875225844105. Connecting the historical order-6
certificate does **not** verify the current headline. The generic lower
interface supports an order-7 base certificate but does not express the
slack-strengthening argument. That argument must not be imported as a bound
on all trajectories.

## Model correspondence

| Paper object | Lean definition and meaning |
| --- | --- |
| Dimensionless laboratory time tau | `LabPulse.S`; finite, nonnegative |
| Shared amplitude-limited drive v | `LabPulse.u`; measurable, norm at most 1 |
| Full-amplitude active-time drive u | `ActivePulse = CZExposure.Pulse`; measurable, norm equal to 1 |
| Four complex amplitudes | `State = Fin 8 → ℝ`, via `g1`, `r1`, `g2`, `r2` |
| Two-sector Schrodinger equation | `vf`, with couplings 1/2 and sqrt(2)/2; coordinatewise integral ODE |
| Initial condition | `x0 = (1,0,1,0)` in complex amplitudes; follows at time zero from the integral ODE |
| Normalization | `Xset`, both sectors normalized throughout the interval |
| Exact CZ closure | `XCZ`: r1 = r2 = 0 and g2 = -g1^2, with normalization |
| Exposure rate | `cost = (2*norm(r1)^2 + norm(r2)^2)/4` |
| Exposure | Integral of `cost` in the respective time variable |
| Optimal values | `labCstar`, `activeCstar`, both `EReal` infima; infeasibility is +infinity |

There is no bandwidth bound, no common duration cap, and no detuning variable
independent of the phase control in these definitions. The integral ODE admits
phase switching; it does not demand derivatives at switching points.

**Proved:** `labCstar_eq_activeCstar`, with no compression hypothesis and no
assumption that a successful pulse exists. `toLab` embeds active pulses at
the same cost. In the other direction, `LabPulse.compress` constructs a
full-amplitude integral-solution pulse from every `LabPulse`:

- duration is exactly the integral of the original control norm, and does
  not exceed the original duration;
- at each original time t, the compressed state at accumulated active time
  equals the original state at t, preserving in particular the exact endpoint;
- compressed exposure equals the original integral of cost times control
  norm, hence is no greater than the original laboratory exposure.

`LabPulse.toSegment` proves the conversion from the coordinatewise integral
equation to Appendix E's vector-valued `PhysicalSegment` equation. It then
reuses `PhysicalSegment.toUnitPulse`, not the conditional `lemma_bang_infima`.
The existing `ActiveClock`, `ActiveExposure`, and `ActiveDynamics` proofs handle
zero-amplitude plateaux, measurable controls, null sets and the integral ODE;
no strictly positive amplitude or differentiable inverse clock is assumed.
The earlier open item was the connection to `LabPulse`, not absence of this
underlying Appendix E construction. The transitive axiom audit covers the
constructor and all exposed compression results.

The old `LowerBoundCZ.Cstar` still denotes the differentiable real-valued
model. Its existing `Results` theorems remain legacy conditional results. No
equality with either new infimum is claimed and no old theorem has been
silently redirected to a different model.

## Lower certificate interface

`Lower.Payload` carries the partition, ceiling U, order d, scalar n, cell
potentials V and target L. `Lower.Checks` asks for positive order/ceiling,
L ≤ U, `ConcretePartitioned.PotentialFeasible`, and -n - V_0(0,x0) = L.
The concrete predicate includes:

- degree and symmetry conditions for each potential;
- occupation Gram identities for c - L_j V_j, modulo normalization relations;
- interface Gram identities for V_j(1) - V_(j+1)(0);
- terminal interval Gram identities for V_j + n;
- positive semidefiniteness of the associated real rephased charge blocks.

There is no field asserting a bound on physical trajectories.
`Lower.Checks.active_lower` already proves the bound on `activeCstar` using
the existing concrete weak duality and W_j = -n - V_j. Pulses with exposure
at least U are handled by L ≤ U, so this proof does not need a successful
pulse below U, or any completeness hypothesis.
`Lower.Checks.lab_lower` transfers this result to the amplitude-limited
laboratory infimum using the proved equality of optimal values.

`GramBridge.Checks.feasible` now constructs `PotentialFeasible` from ordered
source Gram blocks. The generic `Checks` structure adds degree and invariance
to `MatrixChecks`, which contains only PSD conditions, drift/interface residual
identities modulo the normalization ideal, and terminal identities.
`Pinned.order7_lab_lower_of_grams` takes only `MatrixChecks`: the pinned
potential's degree, invariance and objective are proved inside Lean. It combines
these with weak duality and the laboratory/active-time equivalence. No input
asserts cone membership or a physical bound.

The source and target charge conventions differ: the archive keeps negative
charges, while Lean's `ConjugateGram.Keep` keeps positive charges. `RawBlock`
records source-order exponents, integer face weights and exact Q(sqrt(2))
matrix entries. `RawBlock.toBlock` conjugates the monomial indices;
`RawBlock.polynomial_eq` proves that decoding preserves the source polynomial.
The matrix transport is D-transpose * Q * D, with the odd-control parity sign
included in D. `gram_congruence`, `gram_conjugate` and
`conjugate_partner_column` prove this transformation at polynomial level;
PSD follows by congruence, including singular and rectangular cases.

`Block.cone` inserts each transformed block into its retained charge sector,
zero-padding absent columns. `blocks_cone` sums blocks, `Cell.cone` assembles
the occupation localizer, and the terminal blocks retain their explicit
univariate order. One-by-one interval blocks use the same construction.
The pinned order-7 layout has only singleton nonzero face columns; unused
non-excited columns are removed before checking target-basis membership.
The theorem also handles general sparse integer face columns and repeated
indices, without requiring an invertible basis transformation.

### Recovered order-6 payload correspondence

Source: `https://ampcode.com/@wz-s-space/min-exposure-sdp`, commit
`42a6cb9ad9cab73301c262e9ca32a9fe47db94a4`, file
`verification_results/split-knot-headroom-2930/attempts/o6-shoulder-1-26/certificate-293.json.gz`.
Decompressed SHA-256:
`907835bf180ec890e7988057b25c308df7109f58f0f64802ac714b694602ddba`.
Recorded auditor revision: `45d45bf11abbacd0be693bf0068f78de77d91997`.

| Archive field | Required correspondence |
| --- | --- |
| `order`, `knots` | d=6, five cells at 0,1/26,1/3,2/3,25/26,1 |
| `exposure_upper`, `bound_target` | U=2935887/1000000, L=293/100 |
| `normalization` | Shared n, with objective sign checked against -n-V_0(0,x0) |
| `liouville_multipliers_by_cell` | Decode exact Q(sqrt(2)) coefficients into V_j using `cell_major_liouville_v1` ordering |
| `occupation_grams_by_cell` | Drift cone, charge/rephasing conventions and zero-cost-face restricted basis |
| `interface_grams_by_knot` | Interface cone in its full state-only basis |
| `terminal_grams_by_cell` | Two univariate interval Gram blocks per cell |
| `split_grid_hash`, `formulation_hash`, `gram_order` | Check decoder/auditor convention identity, not just data integrity |

The file hash and metadata were checked. The exact decoder, basis matching,
and a `Checks` instance have **not** been supplied. The auditor has not been
rerun in this phase. A hash alone establishes no feasibility claim.

## Upper certificate interface

Pinned source repository: `wanda0929/Finite_blockade_pulse`, commit
`cd82ca17f45ba860572c7bdbbcae24b3e8abb07a`.

| File | SHA-256 |
| --- | --- |
| `verification/reference_data/jan22_cz_exposure_candidate_12672.json` | `fbd9f18240972d437468f63ef0b704bc1af94917690c15736a5777ab3ce4d676` |
| `verification/jan22_cz_exposure_interval_upper.py` | `7144feb6dd8a1b79c331004a8f4ff9c12308e11fc7b66bb164a542f0d86f2bac` |

Both files were retrieved and inspected. The identical files in the pinned
publication snapshot below were freshly verified with python-flint 0.9.0.
The candidate has 12,672 phases. All decimal strings must denote exact
rationals, not the rounded `float` in the checker's summary JSON.

`Upper.segment`, `propagate`, `residual`, `branch`, and `exposure` define the
actual finite recurrence rather than arbitrary residual/cost functions. The
parameter vector contains duration and phases at **zero-based** indices
731, 6676, 8661, 11922; other phases are fixed. Segment duration is S/12672.
The checker constructs u=cos(phi)+i sin(phi); thus phi is minus the manuscript's
laser phase chi when u=exp(-i chi). This convention must be preserved in the
trajectory reconstruction; `UpperSegments` proves the resulting vector field
is exactly Appendix E's `vf`, without conjugating either sector.

`Upper.Payload` carries the fixed phases, center, radius, preconditioner R,
Jacobian enclosure and contraction constant. `Pinned.UpperChecks` is now
`Upper.AD.Enclosures Pinned.upper`, with these numerical inputs:

| Checker calculation | Lean interface condition |
| --- | --- |
| Positive box radius and duration | `radius_pos`, `duration_pos` |
| Interval automatic differentiation | `jacobian_enclosure` for the explicit forward-mode program |
| Row-sum defect bound below 1 | `defect_bound`, `contraction_nonneg`, `contraction_lt_one` in the infinity norm |
| Strict Krawczyk image inclusion | `krawczyk_interior` on the closed parameter box |
| Negative real phase cross throughout box | `cz_branch` |
| Exposure enclosure strictly below endpoint | `exposure_bound` |

No field assumes a root exists, a pulse succeeds, or an infimum bound holds.
The binding adapter exports exact box/enclosure data; its
`unique_exact_terminal_root: true` output is never an input theorem.
Preconditioner injectivity is derived from the defect bound and finite
dimensionality. No convexity or closedness assumption on the Jacobian set is
needed: the mean-value proof works separately for each scalar coordinate.

Proved in Lean, not numerical assumptions:

1. `AD.Expr.hasFDerivAt` proves the forward-mode rules by expression induction.
   `AD.program_eval` proves the amplitude program equals the sector recurrence,
   by induction over the finite phase list. `AD.jacobian_eq_fderiv` connects
   its five derivative components to the actual residual Jacobian. The
   program mirrors the pinned Python real/complex add, negate, multiply,
   conjugate, sine and cosine operations. Division by the constant 12672
   is normalized to reciprocal multiplication; `constant_quotient_rule`
   proves agreement with the checker's quotient rule. Population derivatives
   are not needed for the residual Jacobian.
2. `Checks.newton_mapsTo`, `newton_lipschitz` and `exists_root` prove a local
   self-map contraction on the complete closed parameter box, and construct
   an actual residual zero. No global contraction assumption is used.
3. `segmentPath_deriv`, `physicalSegment_exposure` and `exists_assembly`
   prove normalization, the integral ODE and exact population cost, and
   concatenate all 12,672 segments into a measurable unit-control path.
4. `residual_zero_terminal` proves exact CZ closure using normalization and
   the negative real phase cross; residual zero alone is insufficient.
5. `pulse_of_root` constructs the successful `ActivePulse` with exactly the
   recurrence's exposure. `Pinned.upper_lab_bound` transfers the strict bound
   to `labCstar`. `Pinned.lab_window` combines both certificates on that same
   physical infimum: 2.9305 ≤ labCstar < 2.935875225844105.

The mathematical interval-enclosure assertions are the first-tier external
boundary; the structural propagation/derivative identities must be proved,
not silently moved across that boundary.

## Acceptance and next work

Run `lake build`, `lake env lean CertificateContractsAudit.lean`,
`lake env lean NoGoAudit.lean`, and `lake env lean AppendixEAudit.lean` in `lean/`.
The new bridge's axiom audit permits only propext, Classical.choice and
Quot.sound. This does not instantiate the external checks.

The current concrete binding is generated by `bind_certificates.py` from
`wanda0929/Lowerbound_pub`, revision
`139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2`. It emits
`LowerBoundCZ/CertificateData.lean` and `certificate-bindings.json`.
Run it with python-flint 0.9.0, Cargo and without Python optimization:

```bash
python bind_certificates.py /path/to/publication-checkout \
  --audit-lower --output /tmp/cz-bindings
```

The generator rejects wrong revisions, archive hashes, schemas, shapes,
orders, grids and objectives before writing output. The order-7 compressed
and decompressed hashes are respectively
`53731503c1be0bc7c9645b4cc98c7208b6bddbdfc7d5b407340e33ca27b6ce16` and
`1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52`.

The lower payload contains all five sets of 776 exact Q(sqrt(2)) multipliers.
Its potential is **minus** the multiplier-weighted real monomial sum, with
no factor of two for conjugate representatives. The source objective is
checked exactly as -n + sum(lambda at the initial state) = 5861/2000.
The report reconstructs the ordered charge bases, odd-control rephasing,
sparse integer zero-cost-face columns, redundant interval diagonal blocks,
and interface ordering. All 4,226 matrix dimensions match that layout.
This is a layout check, not a polynomial identity or PSD proof.

The upper payload contains all 12,672 exact rational phases, the five-dimensional
box, the exact rational inverse and the exported Jacobian interval endpoints.
The original verifier was rerun successfully. The adapter additionally checks
strict inclusion for the exact rational box (not merely a rounded Arb box),
contraction below one, negative branch and exposure below the target. The
contraction bound is approximately 3.18e-75. Exported endpoints and provenance
are in the JSON report. Lean kernel tests check every exported array length;
the conditional lower theorem passes the transitive axiom allowlist.

**The Gram-to-feasibility implication is now proved, not assumed.** The
`lean_gram_bridge` report specifies each source/target exponent vector, the
retained charge, parity signs, sparse integer weights and per-matrix hashes.
The exporter checks target normality, degree and face/interface restrictions
for every used column, not merely matrix dimensions. The core-only Rust
auditor was freshly rerun with this export:
18,739 exact identities, zero residuals, every Gram PSD, exact endpoint
5861/2000. The `--audit-lower` mode reproduces this check against the
hash-verified JSON and includes its output in the binding report. Without
that flag the report explicitly records `lower_psd_replayed: false`.
The 9,210,439 numerical matrix entries remain in the hash-pinned external
archive; they are not embedded as millions of Lean literals. `RawBlock.cone`
and `Checks.feasible` are kernel-checked universally over those matrices.
The external boundary is still explicit: the decoder's JSON extraction and
layout checks, and the numerical PSD/identity checks. No unconditional
`Order7Checks` instance or kernel replay of the complete numerical archive is
claimed. `PotentialBasis` proves the source decoder's degree bound, optical and
qubit phase invariance, reflection invariance and initial-state evaluation.
Kernel computation checks all 776 pinned basis entries: each has degree at
most 13 and balanced phase weights. Thus all five cell potentials satisfy
the order-7 structural conditions. Only indices 0, 3, 11, 28 and 61 survive
at the initial state. Their exact rational coefficient sum, together with the
pinned offset, proves the objective 5861/2000, including cancellation of the
sqrt(2) component. These proofs use neither `native_decide` nor external
numerical hypotheses. They do not prove the separate slack-strengthened bound.

For the upper side, the structural analytic chain above is now proved.
`Pinned.UpperChecks` is still an explicit external input, not an unconditional
Lean theorem: Python execution, Arb outward rounding, interval evaluation and
the archive decoder are not kernel-verified. The real program and its
derivative identities are kernel-verified; the numerical claim that the
exported intervals enclose its values remains the agreed first-tier boundary.
The slack-strengthening implication is now proved below. Legacy bound axioms
remain in the historical API, but neither `Pinned.lab_window` nor
`Strengthened.lab_window` depends on them.

## Strengthened-bound proof and finite checks

The component history below culminates in `Strengthened.lab_window`: the
first-tier conditional physical bound is now proved.
No unconditional numerical-check instance or full fresh PSD replay is claimed.

The `Slack` namespace now proves the following without additional axioms:

- `dark_deriv`, `dark_speed_identity`, and `dark_budget`: the common-drive
  dark coordinate obeys the physical ODE and the two-endpoint exposure budget.
  Absolute continuity and integration are derived from the integral model.
- `dark_box_excludes`: the two signed-corner rational tests exclude actual
  trajectories in the given exposure interval. Corner monotonicity, the
  population reverse triangle inequality, and strict boundary handling are
  proved; the checker does not supply a trajectory-exclusion assumption.
- `barrierSeries_sqrt_le`, `barrierG_deriv`, and `population_budget`: the
  binomial recurrence proves the population barriers for every order,
  including `W_8` and `W_64`. The derivative bound, absolute continuity,
  zero-population endpoints, and both excursion/return budgets follow from
  the integral dynamics. No residual-coefficient or reachability oracle is
  supplied. The barrier remains continuously differentiable at zero.
- `barrierEnergy_rat` and `population_box_excludes`: the checker's exact
  rational energy formula, including its factors 3, 8 and 72, is connected
  to the physical barrier. Monotonicity makes the lower population corner
  sufficient to exclude the entire closed rectangle. Both strict branches
  of the rational test are covered; equality is retained.
- `occupation_integral` and `slack_telescope`: exact local slack integration
  and telescoping over adjacent time intervals, with each interface once.
- `exposure_crossings`, `profile_integral`, and `profile_credit`: guaranteed
  exposure intervals are traversed in order, and a local polynomial profile
  inequality implies its integrated credit, including zero-cost stalls.
- `crossings_exist_of_grams`: the pinned base certificate implies that every
  physical pulse reaches all four internal knots, strictly in time order.
  The threshold is proved from the Gram checks, not a separate physical-bound
  input. `Crossings.coordinates` identifies the same crossing as local
  coordinate 1 in the left cell and 0 in the right cell. `cell_domain` keeps
  each interval inside its cell for candidate exposure at most the ceiling.
- `Crossings.telescope`: the exact five-cell identity, with four interfaces
  counted once and with the sign V_left(1)-V_right(0). The last cell ends at
  the actual pulse endpoint; its terminal coordinate is not replaced by 1.
- `InterfaceCertificate.credit`, `Crossings.credit`, and
  `Crossings.credited_telescope`: finite source identities, matrix domination,
  budgets and Bernstein residual signs imply the physical interface credits
  and their contribution to the total accounting. Box membership/evaluation
  remain explicit domain conditions, not assumed slack inequalities. For the
  full-population checker, use one combined diagonal allocation per original
  block with weight one: its Q-minus-combined-allocation test must not be
  confused with independent per-projection weight caps. The fixed instance
  and coverage proof are now in `PinnedInterfaces`, described below. Evaluating
  the state-only identity at control 1 imposes no condition on the actual
  control at a crossing.
- `gram_value_mono`, `gram_budget`, and `AllocatedBlock.eval_le`: matrix
  domination implies domination on complex source columns, and nonnegative
  weights summing to at most one **per original block** permit adding its
  projections. All four source localizers are supported, including their
  zero endpoints. No positivity of a projected quadratic form is assumed.
- `allocation_local_slack` and `AllocationRegion.trajectory_slack`: finite
  polynomial identities modulo the normalization ideal and nonnegative
  degree-(14,7,7) tensor coefficients imply the actual pinned order-7 drift
  slack is at least the exposure profile times the physical cost. The three
  coordinates are exposure, first-sector population, second-sector population;
  affine box normalization and evaluation are proved in Lean. The input is
  **not** a pointwise or integrated slack bound.
- `endpoint_composition` and `endpoint_pos`: the pinned final endpoint
  polynomial is exactly the rescaled parent polynomial plus its declared
  gain and endpoint adjustment, and is strictly positive on the unit interval.

`bind_slack.py` checks publication revision
`139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2` and the three hashes hard-coded in
the exporter before decoding `SlackData`. The final target is exactly
`146564386761/50000000000`. This export checks provenance and gain-field
consistency; it does not verify the physical interpretation of that gain.

`bind_allocations.py` additionally binds the replacement allocation with
decompressed SHA-256 `c92d741884064a671643081415ad701c2cb6c2f0f6ecdf5f7bac4f1bf6e84b73`.
It runs the pinned regional checker, exports original-block ownership and
source-column layouts, checks selected rows/phases and reduced-polynomial
identities, and exports the tensor residual coefficients in exposure-major
order (then first population, then second). Its scope is 16 replacement
intervals, 1,024 regions, 1,078 used projections, 638,611 block-budget checks,
and 983,040 residual signs. It does not replay predecessor PSD proofs.

Run with python-flint in the environment:

```bash
python bind_allocations.py /path/to/pinned-publication \
  --output /tmp/allocations.json.gz --lean-dir LowerBoundCZ
lake build
lake env lean --run AllocationDataAudit.lean /tmp/allocation-values.txt
python bind_allocations.py /path/to/pinned-publication \
  --output /tmp/allocations.json.gz --lean-dump /tmp/allocation-values.txt
```

**The fixed data are now a generated Lean instance.** `AllocationData` and its
eight source shards contain all 736 original cell-2 Gram matrices, their complex
facial columns, 1,078 reduced projections, 1,180 shared allocation groups,
1,024 region maps and 16 profiles. Unallocated source blocks remain present.
`AllocationCodec` uses pure decimal decoding, with no IO or additional axiom in
the mathematical definitions. Matrices retain exact rational and sqrt(2)
parts. `PinnedAllocations` embeds reduced matrices at the original selected
row indices, retains off-diagonal entries, and computes the degree-(14,7,7)
tensor residual by exact rational affine power-to-Bernstein conversion.
`AllocationData/bindings.json` records the input and generated-file hashes.

`PinnedAllocation.checks` and `PinnedAllocation.trajectory_slack` apply the
proved bridge to these fixed definitions. Their `NumericalChecks` argument
contains only source PSD, embedded matrix domination, nonnegative weights,
per-original-block budgets, source/tensor polynomial identities modulo the
normalization ideal, and tensor coefficient signs. No variable certificate,
pointwise slack inequality or integrated physical credit is an input. The
source identity is stated for each region; its original matrices and cell-2
drift are the same in all regions. This avoids reducing enormous closed
data expressions while the kernel checks the interface conversion.

`AllocationDataAudit.lean` validates shapes, row ownership and budgets, and
exports the values Lean actually decodes. The independent comparison checks
all 1,792,426 full Gram entries (including the reconstructed lower triangle),
all source columns and projections, all 638,707 allocated weights and all
profiles. It also compares nine asymmetric/boundary tensor coefficients with
the independent checker. This tensor comparison is a sample, not an exhaustive
evaluation of Lean's tensor function; the external regional checker tests all
983,040 residual signs. The 1,078 used projection checks were also replayed
with 384-bit Arb, covering 626 original blocks. The full predecessor chain
was not replayed in this step.

These executable checks are validation evidence, **not kernel proofs of
`NumericalChecks`**. In particular, the external inverse-order matrix test is
not silently converted into a Lean proof of embedded matrix domination, and
the full source/tensor ideal identities remain explicit finite numerical
inputs. This is the agreed first-tier trust boundary, not a new analytic oracle.

### Fixed four-interface instance and population coverage

`bind_interfaces.py` binds the original source and native basis hashes, the
joint-slack allocation hash
`98560cc0bd55714dfb74814e377caac64cb4c736652e33868925da7b25703fd7`,
and the reachable-crossing hash
`21c24c558802babba6e55f891b8135099eae0af949578f52b1cad3c10d2d7569`.
`InterfaceData.lean` contains every original block: 134 per interface, 536
total, including the six blocks without allocations. It retains exact
Q(sqrt(2)) source entries, native state columns, combined rational diagonal
allocations, four population polynomials and the four strengthened credits.
`InterfaceData.json` records provenance, generated-file hash and external checks.

`PinnedInterface.NumericalChecks` contains only PSD/matrix-order conditions,
source/tensor coefficient identities and residual signs on retained boxes.
All these predicates refer to the fixed data. `certificate` instantiates the
previous interface API with one combined allocation of weight one per block.
There is no numerical field asserting a physical crossing bound or coverage.

`grid_cover` and `population_cover` prove coverage by closed 64×64 boxes,
including populations 0 and 1 and shared boundaries. `excluded_iff` proves
that the executable rational discriminator is exactly the physical W64
exclusion predicate (strict comparisons; equality is not discarded).
`retained` uses the physical barrier theorem and the exact crossing exposure
to rule out the discarded box for every candidate pulse of exposure at most
733/250. This cap already exceeds the final target. `crossing_credit` selects
a box from the coverage theorem, proves it retained, and obtains its fixed
credit. `credited_telescope` inserts all four into the five-cell accounting.
Neither theorem accepts a box-selection, coverage or physical-slack oracle.

Validation commands (python-flint required):

```bash
python bind_interfaces.py /path/to/pinned-publication
lake build
lake env lean --run InterfaceDataAudit.lean /tmp/interface-values.txt
python bind_interfaces.py /path/to/pinned-publication --lean-dump /tmp/interface-values.txt
```

The external replay checks 530 allocated source-block matrix inequalities at
384-bit Arb precision and all 615,296 retained-box Bernstein inequalities.
Retained box counts are 731, 4096, 4096, 691; discarded counts are
3365, 0, 0, 3405. The decoder comparison checks all 247,744 full Gram entries,
all columns/combined diagonals/powers/credits, all 64 energy values and all
16,384 box classifications. It also compares 36 asymmetric/boundary tensor
coefficients with the independent checker's tensor conversion. This is a
sample of Lean's residual function, not its exhaustive evaluation. Boundary
coverage examples and the transitive axiom allowlist are checked in Lean.
These executions do not construct a kernel proof of `NumericalChecks` and
do not replay the whole predecessor chain or establish the final physical bound.

`bind_profiles.py` now binds all 321 final occupation profiles: 320 prefix
intervals plus the separate mandatory tail. It selects allocation replacements
176–191 and 32 disjoint dark replacements over the reachability profiles;
replaced baseline profiles are not also credited. The exported packet records
source hashes, original indices, local/global endpoints, grids, ownership,
Bernstein and signed-power coefficients, and exact integrated credits. Its
total is checked against reachability-prefix credit + allocation gain + dark
gain + tail credit, using exact rational arithmetic. This binds the profiles,
not by itself their regional Gram/projection allocations; those are now bound
separately by `bind_regions.py`, below.

`OccupationLedger.primitive_credit` and `interval_credit` connect each fixed
signed-power primitive to its physical integral, including zero-cost stalls.
`index_unique` prevents double-counting across the five cells; `prefix_sum_le`
adds adjacent intervals and retains a nonnegative uncredited remainder.
`slack_nonneg` derives that remainder's sign from the original Gram checks.
`credited_telescope` adds the profile sum to all four fixed interface credits
and the actual terminal potential. It still takes **analytic** premises
`Traversal` and local `hpoint` inequalities, not a `NumericalChecks` claiming
those physical facts. The local `hpoint` premise is now discharged for the
full payload by `OccupationCoverage`, below; `MandatoryPrefix` now discharges
the traversal using only profiles already reached at the base bound.

`traversal_exists` constructs all interval crossings, given finite fixed-data
`LayoutChecks` and the explicit premise `right 320 ≤ γ.exposure`. The latter
means exposure at least **2.931285651554**. Even the main prefix ends at
**2.930957146313**, beyond the currently established base bound 2.9305. A
bootstrap proof is therefore essential: one cannot assume that
every trajectory traverses the full prefix and then use its credits to prove
that very threshold. `LayoutChecks` concerns only rational endpoint comparisons;
the stronger physical threshold must not be relabeled as external data. The
noncircular bootstrap is now proved by `MandatoryPrefix.threshold`, below.

Validation (decoding/accounting only, not a Gram or predecessor-chain replay):

```bash
python bind_profiles.py /path/to/pinned-publication --output LowerBoundCZ/ProfileData.lean
lake build
lake env lean -M 11000 --run ProfileDataAudit.lean /tmp/profile-values.txt
python bind_profiles.py /path/to/pinned-publication --lean-dump /tmp/profile-values.txt
```

The audit compares all 4,815 signed-power coefficients, 642 endpoints and 321
credits against the original pinned profiles. It checks widths, joins, cell
ownership, the five-cell sum and every layout endpoint bound. The transitive
axiom allowlist is enforced for the new analytic results. Runtime data checks
are not kernel proofs of `LayoutChecks` or of local profile validity.

`PinnedRegions` now supplies the remaining fixed regional Gram-to-local-profile
instances. `RegionalData` contains all 3,680 original occupation Gram blocks
(736 per cell, including unallocated blocks), 6,190 used projections, 7,406
shared per-block allocation groups, 2,653 allocation maps and 9,728 retained
boxes. The 305 profile slots covered here comprise 198 W8-reachable, 74 inherited,
32 dark-restricted and one tail profile. The 16 replacement slots 176–191 are
deliberately omitted: they remain in `PinnedAllocations`, not counted twice.
All source matrices are fixed; shared source columns are checked against each
cell's original metadata, not assumed equal. The decoder audit checks raw cell
indices before the total `Fin 5` decoding, all lookup bounds and block ownership.

`PinnedRegion.NumericalChecks` contains only finite widths, block PSD/matrix
domination/weight budgets, normalization-ideal coefficient identities and tensor
signs. `checks` supplies the existing algebraic bridge and `trajectory_slack`
proves the local inequality for an actual pulse whose state lies in that box.
No physical inequality, cone-feasibility conclusion, box-selection oracle or
integrated-credit assertion is accepted as numerical input.

```bash
python bind_regions.py /path/to/pinned-publication --output LowerBoundCZ
lake build
lake env lean -M 12000 --run RegionalDataAudit.lean /tmp/regions-decoded.txt
python bind_regions.py /path/to/pinned-publication --lean-dump /tmp/regions-decoded.txt
```

The exporter replays all 9,338,880 retained-box coefficient inequalities using
exact signed-power tensors and checks the per-original-block budgets. The
decoder comparison covers every source upper-triangle entry (both rational
and sqrt(2) parts), source column/phase, projection entry, weight, allocation
map, retained box and profile. Four asymmetric tensor coefficients are also
compared between Lean's residual function and the independent flint tensor
calculation, one each for reachable, inherited, dark and tail profiles. Those
four comparisons do not constitute an exhaustive execution of Lean's residual
function. This run does **not** replay original PSD/domination checks or prove
the normalization-ideal identities in the kernel; these remain explicit finite
external obligations. No unconditional instance of `NumericalChecks` is claimed.

The separate regional matrix-domination replay passed for all **6,190** used
projections on **3,171** source blocks across all five cells. The per-projection
results and provenance are in `LowerBoundCZ/RegionalData/domination.json`.
Reproduce it with:

```bash
lake env lean -M 12000 --run RegionalDataAudit.lean /tmp/regions-decoded.txt
python bind_regions.py /path/to/pinned-publication \
  --lean-dump /tmp/regions-decoded.txt \
  --domination-report LowerBoundCZ/RegionalData/domination.json
```

This first compares the complete Lean-decoded payload with the pinned archive,
then checks every one of the 6,190 used projection records, grouped by original
cell/block to reuse the validated inverse. On the active principal block it
uses 384-bit Arb solves and positive interval LDL pivots to establish
R>0 and R^-1-E^T Q^-1 E>0. Together with the existing source PSD audit, this
implies Q-E R E^T is PSD. The checker verifies that omitted source rows are
exactly zero and all selected rows are active, so singular zero faces are
preserved rather than treated as positive definite. This is the same embedding
used by `PinnedRegion.embedded`; weights/budgets are separately checked.

The report records each projection's Lean index, original ID, cell/block,
selected rows and record hash, plus the decoded-data, checker, source and base
audit-binding hashes. Source PSD is **reused**, not replayed here. Controls
include a valid asymmetric matrix with a zero face and reject an oversized
projection, an omitted nonzero source row and duplicate selected rows.
No normalization-ideal identity or kernel `NumericalChecks` instance is
supplied by this replay; the other first-tier obligations remain separate.

The exporter classifies 12,336 omitted boxes (8,052 W8 and 4,284 dark).
`OccupationCoverage` now applies the physical exclusion lemmas to the fixed
grids. `grid_cover` proves closed coverage, including 0, 1 and interior grid
boundaries. `excludedQ_iff` identifies the executable strict rational tests
with the physical W8/dark predicates. `retained_cover` therefore selects a
retained box for any physical pulse under cap 2.932 whose cumulative exposure
is inside the given profile interval. It does not assume a box-selection or
trajectory-unreachability oracle.

`CoverageData` explicitly routes all 23,088 box entries: 10,752 to the fixed
replacement/regional instances and 12,336 to exclusion. `DataChecks` contains
only finite grid sizes, local interval bounds, rational endpoint equalities,
polynomial coefficient identities, lookup assignments and rational exclusion
tests. All indices range over fixed finite types. These data checks are
external first-tier obligations, not new axioms or analytic premises.

`primitive_derivative` proves differentiation of the ledger's signed-power
primitive, including the factor 1/(k+1). The finite `coefficients` field equates
the resulting power polynomial with the stored Bernstein polynomial, rather
than assuming an identity along arbitrary trajectories. `normalized_coordinate`
proves that local xi normalization equals global cumulative-exposure
normalization. `rate_eq_derivative` then identifies the selected local rate
with the ledger primitive's derivative. No positive instantaneous cost or
inverse cumulative-exposure map is needed.

`pointwise_slack` combines retained coverage with the fixed Gram implications.
`OccupationCoverage.credited_telescope` uses it to discharge the older ledger's
local `hpoint` premise for every profile, including replacements. Its remaining
trajectory-level inputs are the counterexample cap and `Traversal`; it does
not assume that the original 2.9305 bound already guarantees the longer prefix.

```bash
python bind_coverage.py /path/to/pinned-publication --output LowerBoundCZ/CoverageData.lean
lake build
lake env lean -M 12000 --run CoverageDataAudit.lean /tmp/coverage-decoded.txt
python bind_coverage.py /path/to/pinned-publication --lean-dump /tmp/coverage-decoded.txt
```

The audit checks all 23,088 lookups/classifications, 321 exact endpoint and
power/Bernstein identities, all retained-cell/bounds/profile assignments, and
all strict rational exclusions. It compares the decoded lookup table with
the pinned original classifiers and rejects shifted replacement and tail
ownership. Boundary examples and all new theorem dependencies are kernel
checked. Executable finite-data checks are not a kernel proof of `DataChecks`.

### Mandatory traversal now follows from already-reached credits

`MandatoryPrefix` avoids importing the historical chain of predecessor bound
labels. Its `prefix_credit` uses only slots 0–318: 64 intervals in each of the
first four cells and 63 in the last. Their last endpoint is approximately
2.9297599187664427, strictly below the base bound 2.9305. Continuity and
monotonicity therefore supply those crossings before any strengthened bound
is used. The original Gram certificate makes each discarded remainder
nonnegative. Slots 319 and 320 contribute nothing to this bootstrap.

Let L=2.9305, B=2.931285651554, K be these 319 credits and H the four interface
credits. `EndpointChecks.identity` is one fixed degree-13 polynomial identity:
the terminal restriction of the original potential, evaluated at
xi=36*(L+(B-L)*t)/U-35, plus offset+L+K+H-B equals the stored Bernstein
polynomial. All 14 coefficients are strictly positive; their minimum is
approximately 1.85821427724e-7. This is exact rational algebra (with both
Q(sqrt(2)) components checked), not sampled positivity or a physical-bound
assumption. `endpoint_value` proves the connection to the actual terminal
state using CZ-orbit invariance and the already proved initial objective.

`threshold` combines that positivity with the partial integral ledger and
interface credits to prove B ≤ γ.exposure for every active pulse, conditional
only on the finite certificate inputs. `traversal` then applies the existing
continuity construction to all 321 intervals. The new
`MandatoryPrefix.credited_telescope` requires neither `Traversal`, crossing
times nor `hpoint` from its caller; only the candidate cap remains a physical
premise. This closes mandatory traversal without changing the model or data.

```bash
python bind_prefix.py /path/to/pinned-publication --output LowerBoundCZ/PrefixData.lean
lake build
lake env lean -M 12000 --run PrefixDataAudit.lean /tmp/prefix-decoded.txt
python bind_prefix.py /path/to/pinned-publication --lean-dump /tmp/prefix-decoded.txt
```

The audit checks the full layout, the shorter prefix's base-bound comparisons,
all terminal polynomial coefficients and signs, and compares Lean-decoded
terminal coefficients, credits and Bernstein data against the hash-pinned
source. Negative controls reject extending the base-reached prefix by one
interval, changing a Bernstein coefficient, reversing the terminal sign and
including the two unproved credits. These executable checks are not kernel
instances of `LayoutChecks` or `EndpointChecks`. No PSD replay is claimed here.

**Final physical implication now closed:**

`Strengthened.endpoint_value` rescales the bootstrap polynomial and adds the
two previously omitted credits. It proves that its value on the actual pulse
equals the complete occupation/interface credit plus terminal-minus-initial
potential minus the final bound. `EndpointCheck` is only a fixed degree-13
polynomial equality to the archived final Bernstein polynomial; it has no
trajectory quantifier or inequality about physical exposure.

`endpoint_matches` identifies this polynomial with `Slack.endpoint`.
`pulse_lower` derives the scalar premise of `Slack.endpoint_excludes` from
`MandatoryPrefix.credited_telescope`, rather than assuming that premise. This
proves 2.931287735220 < exposure for every active pulse. Taking the infimum
gives the non-strict bound (`active_lower`); the proved laboratory/active model
equivalence gives `lab_lower`. No attainment assumption is made. Combining
with the existing upper certificate gives `Strengthened.lab_window`:

**2.931287735220 ≤ labCstar < 2.935875225844105.**

This is the first-tier **conditional** theorem. Its explicit finite inputs are
the base Gram matrix/identity checks, fixed allocation/regional/interface
checks, layout/coverage checks, bootstrap endpoint checks, final endpoint
identity and (for the window) upper interval enclosures. There is no remaining
physical slack, traversal, endpoint-value or lower-bound assumption. An
unconditional kernel certificate instance would require proving these finite
inputs and archive decoding inside the trust boundary; it is not claimed here.

```bash
lake build
lake env lean -M 12000 --run PrefixDataAudit.lean /tmp/prefix.txt /tmp/final.txt
python bind_prefix.py /path/to/pinned-publication --lean-dump /tmp/prefix.txt
python bind_prefix.py /path/to/pinned-publication --final --lean-dump /tmp/final.txt
lake env lean -M 12000 CertificateContractsAudit.lean
```

The final audit reconstructs the terminal polynomial from all 776 original
potential basis entries, includes exactly the 321 occupation credits and four
interface credits, and checks all 14 power coefficients and bootstrap-rescaling
identities. Python independently reconstructs the Bernstein coefficients from
the hash-pinned source and compares them exactly with the original final
certificate. Its minimum coefficient is approximately 1.25943106569e-13;
no floating tolerance is used. Additional negative controls reject omitting
the final two credits, reversing the terminal sign and inflating the final
bound by 1e-12. The bootstrap controls are retained. This scoped replay does
not rerun all earlier matrix/PSD or upper interval checks.

The final module is in the default build and the transitive axiom allowlist.
`Pinned.lab_window` remains the base-window API; callers wanting the current
manuscript's lower endpoint should use `Strengthened.lab_window`.

### Allocated polynomial identity replay

`check_allocated_identities.py` now checks the allocated side of
`PinnedAllocation.NumericalChecks.tensor_identity`,
`PinnedRegion.NumericalChecks.tensor_identity`, and
`PinnedInterface.NumericalChecks.tensor_identity`. The recorded result is
`allocated-identities.json`: PASS for 1,078 replacement projections and 6,190
remaining-region projections, and all 536 interface blocks. These cover
1,024 replacement regions, 9,728 remaining regions and all 16,384 interface
boxes (including excluded boxes, since an identity needs no reachability).

The input is a fresh execution of the three Lean data decoders. Their hashes
match the previously archive-compared dumps, including the regional domination
input. The checker expands the **full** allocated Gram, including off-diagonal
entries, facial-column coefficients, conjugation, phases and localizers. It
reduces with exactly `u*u_bar=1`, `g1*g1_bar=1-r1*r1_bar` and
`g2*g2_bar=1-r2*r2_bar`, and compares all resulting rational coefficients with
the claimed population polynomial. The original source matrices are not used
by this allocated-side check.

The residual identity is checked in factored form, by linearity: for every
distinct interval, the power-to-Bernstein matrix from `affineCoefficient` is
multiplied by an independently expanded Bernstein-to-power matrix and must
give the identity matrix exactly. The constant column must be all ones and
the linear column must be `a+(b-a)*i/n`. This establishes partition of unity,
the degree-elevated cost `p1/2+p2/4`, and constant interface-credit subtraction.
Every profile also passes an exact coefficient round trip. The population
factor `(1-p)^g*p^r` is expanded coefficientwise, as in
`populationCoefficient`; tensor products and the decoded allocation weights
then establish the regional identities. This checks all basis coefficients,
not evaluations at selected physical points. There are 221 distinct data
basis changes, plus one asymmetric control interval.

Six negative controls distinguish a wrong phase sign, omitted localizer,
omitted normalization, omitted off-diagonal entries, a changed interior
Bernstein coefficient and a transposed conversion. Arithmetic uses
python-flint 0.9.0 exact rationals, with no floating tolerance.

```bash
lake env lean -M 12000 --run AllocationDataAudit.lean /tmp/identity-allocation.txt
lake env lean -M 12000 --run RegionalDataAudit.lean /tmp/identity-regional.txt
lake env lean -M 12000 --run InterfaceDataAudit.lean /tmp/identity-interface.txt
python check_allocated_identities.py \
  --allocation /tmp/identity-allocation.txt \
  --regional /tmp/identity-regional.txt \
  --interface /tmp/identity-interface.txt \
  --report allocated-identities.json
```

**Trust boundary and remaining work:** this is an external exact-algebra check
of the displayed Lean formulas, not a kernel proof term or exhaustive Lean
evaluation of `residual`. It does not discharge the separate `source_identity`
fields relating the original Grams to the physical drift/interface jump.
Those fields are checked by the separate source replay described below.
The separate sign checker's full coefficient correspondence is checked by the
compositional replay below; the final field-by-field manifest remains open. No new unconditional
`NumericalChecks` instance, physical definition, certificate datum or
manuscript change is introduced by this replay.

### Original source polynomial identity replay

`check_source_identities.py` directly checks the three fixed
`NumericalChecks.source_identity` contracts. It uses the original, unallocated
Grams from the Lean decoders, including every unused block, and all 776 basis
entries and 3,880 multiplier pairs exported by `SourceIdentityDataAudit.lean`.
It does not infer these identities from the earlier source auditor's PASS or
from any PSD assertion.

The two sides are constructed independently:

- For the physical side, decode `V=-sum lambda*Re(m)` with representatives used
  once, translate the eight real `fpoly` components and `cpoly` through
  `encodeCoordinate`, differentiate the unreduced potential, and form
  `c-cellOp(1/(U*width),V)`. For interfaces, form `V_j(1)-V_(j+1)(0)`.
- For the Gram side, expand all original matrices, including both halves of
  every off-diagonal entry, sparse signed facial columns, phases and all four
  localizers. Retain coefficients in `Q(sqrt(2),i)` as four exact rational
  components. Reduce both sides by the same three normalization relations
  used in Lean, then require their complete coefficient difference to vanish.

`source-identities.json` records PASS for five occupation cells (3,680 blocks)
and four interfaces (536 blocks). Each occupation polynomial has 5,871
nonzero normal-form rational components; each interface has 384. Every
residual is exactly zero. These component counts use the explicit mixed
representation and are not the archived auditor's reduced-basis count.
The replacement decoder's 736 source blocks are also compared entry by entry
with regional cell 2, including full matrices, bases, phases, facial rows and
localizers; this covers the separate 1,024-region replacement API rather than
assuming its copy is identical.

Seven controls detect reversed potential sign, omitted cell width, swapped
sector cost weights, doubled real representatives, reversed interface jump,
wrong interface endpoint, and omission of off-diagonal terms in a mixed-phase
Gram with a sqrt(2) entry. The real-to-complex vector field and embedded cost
also pass independent algebraic checks. No floating-point tolerance is used.

```bash
lake env lean -M 12000 --run SourceIdentityDataAudit.lean /tmp/source-potential.txt
# Produce the three Gram dumps with the DataAudit commands above.
python check_source_identities.py \
  --potential /tmp/source-potential.txt \
  --allocation /tmp/identity-allocation.txt \
  --regional /tmp/identity-regional.txt \
  --interface /tmp/identity-interface.txt \
  --report source-identities.json
```

This closes the external source-identity check for the three fixed allocation
APIs; it does not create Lean proof terms for those fields, select a generic
`GramBridge.Archive`, or replay matrix PSD. The checker, decoder and mathematical
definition hashes and all four decoded-input hashes are recorded. The remaining
coefficient correspondence is covered by the following replay. The final
field-by-field manifest, including the chosen base archive, remains open.
The physical definitions, original payloads and manuscript are unchanged.

### Complete residual coefficient correspondence

`ResidualFactorsAudit.lean` executes the actual `affineCoefficient`,
`populationCoefficient` and `costCoefficient` definitions used by the pinned
residuals. It exports all 321 exposure-profile transform tables, all 92
population-axis affine tables, all 1,008 required population-power factor
vectors, and all 295 distinct cost-box tables (231 regional and 64 replacement).
Repeated cost boxes share a table: the defining cost expression depends only
on the two population endpoints and indices, not exposure or profile.

`check_residual_correspondence.py` uses these Lean-produced values and the
fully decoded allocations/profiles to reconstruct every residual coefficient.
It regroups the finite weighted sum by population exponents using exact
distributivity. The independent side uses the pinned external checker's
`region_weights`, `tensor`, `affine` and `popmap`; in particular it expands
population powers before conversion, rather than using the exported Lean
`populationCoefficient`. All allocation groupings are independently compared.
The checker requires the pinned publication revision and unchanged verification
tree, and verifies the decoded-input and definition hashes from the source
identity audit before accepting them.

`residual-correspondence.json` records:

| Fixed family | Coefficients compared exactly | Required nonnegative coefficients |
|---|---:|---:|
| 1,024 replacement regions | 983,040 | 983,040 |
| 9,728 remaining regions | 9,338,880 | 9,338,880 |
| Four interfaces, 16,384 boxes | 1,048,576 | 615,296 |
| Total | 11,370,496 | 10,937,216 |

Every compared coefficient agrees and every required sign passes. All three
families have minimum required coefficient zero; strict positivity is neither
assumed nor required. Excluded interface boxes are still compared, but their
coefficients are not required to be nonnegative. Four negative controls reject
an interior perturbation of 1e-40, transposed axes, swapped sector cost weights,
and two equal but negative coefficients. Acceptance uses exact rationals only.

```bash
lake build
lake env lean -M 12000 --run ResidualFactorsAudit.lean /tmp/residual-factors.txt
# Use the three DataAudit dumps whose hashes the source replay recorded.
python check_residual_correspondence.py /path/to/pinned-publication \
  --allocation /tmp/identity-allocation.txt \
  --regional /tmp/identity-regional.txt \
  --interface /tmp/identity-interface.txt \
  --factors /tmp/residual-factors.txt \
  --report residual-correspondence.json
```

**Scope:** this removes the previous 9/4/36-coefficient sampling limitation by
complete **compositional** evaluation. It does not execute the enormous literal
Lean `residual` sum separately at every index and does not add a kernel theorem
proving the external regrouping algorithm. Finite-sum regrouping, decoder
execution, Python and FLINT remain in the declared first-tier external trust
boundary. No `NumericalChecks` proof instance is created. The subsequent
fixed-archive acceptance layer is documented in [Acceptance.md](Acceptance.md).

## Fixed archive and final first-tier evidence index

`FixedArchive.lab_window` uses a canonical archive, rather than taking an
arbitrary `GramBridge.Archive`. It consumes `FixedArchive.Acceptance`, which
collects all remaining finite external obligations without introducing axioms.
The archive reuses the original occupation/interface matrices and adds the
ten original terminal matrices. `FixedArchiveAudit.lean` and `bind_archive.py`
check all 4,216 nonterminal layouts, all 565 terminal entries, and 75 terminal
coefficient identities. The existing `RawBlock.polynomial_eq` supplies the
kernel-checked basis transport.

[Acceptance.md](Acceptance.md) lists the 65 leaf fields and their evidence.
`acceptance-manifest.json` expands every field and hashes the local proof and
checker sources. `python check_acceptance.py` checks that index and its hash
links, not the numerical calculations themselves. Replacement domination now
also has a reproducible, input-bound report in
`LowerBoundCZ/AllocationData/domination.json`, produced by
`check_allocation_domination.py`; it no longer relies on a temporary log alone.

This is first-tier evidence with an explicit external trust boundary, not a
kernel `Acceptance` instance. The physical definitions and manuscript remain
unchanged. Earlier sections describing the archive/manifest as outstanding
record the state before this final binding layer.

### Input-bound replay after independent audit

An independent review found that the old `--write` could bind unchanged
numerical reports to changed Lean data. It now requires a completed
`acceptance-replay.json` matching the current sources and reports. Produce that
receipt with `python check_acceptance.py --replay PUBLICATION --write`: it builds
the library, runs all eight decoder audits, compares six decoded-input hashes
against the historical numerical reports, and reruns the archive, coverage,
bootstrap and final-endpoint binding checks. A changed input or failed command
cannot produce a new receipt. Old reports are retained, not edited to claim a
new numerical run. `test_acceptance.py` exercises the real CLI on isolated
copies, including a negative terminal diagonal followed by `--write`.

The interface decoder additionally verifies every source's unit row weights,
which the independent source-polynomial checker assumes. Scaling the weights
preserves used-column indices but changes the Gram polynomial, so the audit
includes scaling and row-permutation rejection controls. Its decoded output
format is unchanged and must match the historical input hash before reuse.
