# Unified proof snapshot — 2026-11-11

**PASS under the agreed boundary: Lean reasoning plus external finite certificate
checks, with Appendix E's explicit external superposition hypothesis retained.**
The two requested tasks—saving the complete proof snapshot and validating that
same snapshot—are complete as a downloadable source-and-evidence bundle.
This delivery is not a Git commit or push.

## Snapshot and provenance

The snapshot includes the main `FixedArchive` proof chain, its fixed numerical
payloads and checkers, the NoGo corrections, the completed Appendix B/D physical
connections, and Appendix E's conditional final entries and supporting modules.
It is not merely the Appendix E branch.

The source thread `T-01a1be41-4342-776e-a050-3deca862188a` was accessed read-only.
Committed sources at `b8f993c947a31b1e3f94d9fe7cfae9207c7e3a44` were combined with
its captured working-tree proof/evidence files. `transfer-provenance.json`
records the input hashes. Local integration retains the B/D proofs developed
in this thread and moves their modules into the parent `LowerBoundCZ` library,
so Appendix E need not depend cyclically on its parent package. The public
theorem names and mathematical statements are unchanged by that move.

`unified-acceptance.json` records 366 source/configuration hashes and 67
successful command records. It was completed at **2026-11-11 12:55:14 UTC**.
`SNAPSHOT-SHA256.txt` additionally covers the packaged documentation, evidence
and receipts. These hashes, rather than the old Git HEAD alone, identify the
delivered uncommitted snapshot.

## Executed acceptance

| Check | Result |
|---|---|
| `lake build LowerBoundCZ RequestProject` | Success, 8,300 jobs; existing linter warnings remain |
| `check_acceptance.py --replay CHECKOUT --write` | Success: build, eight Lean decoders producing nine dumps, four external correspondence checks |
| Reuse of historical numerical inputs | All six expected decoded-input hashes match exactly |
| `check_acceptance.py` | 65 acceptance leaf fields mapped; 327 local file hashes match |
| `python -B -m unittest -v test_acceptance` | All five tests pass: unchanged positive case; changed terminal, interface weights, report, and missing receipt rejected |
| Main additional audits | NoGo, Appendix B/D, Appendix E bridge, certificate contracts: all four pass |
| Appendix E audit scripts | All 59 pass, including the final conditional entry and the four latest finite-approximation modules |
| End-of-run snapshot check | Source/configuration hashes identical before and after the complete run |

The 63 additional Lean audits are distinct from the eight decoder executions
inside the finite-certificate replay. The latter has its own 13-command receipt
in `acceptance-replay.json`. Logs are retained in `unified-evidence/` and
`acceptance-evidence/`; no historical success log substitutes for these runs.
The new runner also rejects a publication checkout at the wrong Git revision;
that rejection was exercised before the successful run.

## Accepted conclusions and retained hypotheses

| Scope | Final entries | Meaning and boundary |
|---|---|---|
| Main numerical bracket | `LowerBoundCZ.Certification.FixedArchive.lab_window` | `2.931287735220 ≤ labCstar < 2.935875225844105`, conditional on the 65 finite fields of `FixedArchive.Acceptance`; the reports provide external evidence, not a constructed Lean proof term of that structure |
| NoGo construction | `LowerBoundCZ.exists_chirp_loop`, `chirpExposure_eq_closed`, `theorem_free`, `theorem_relax'` | Actual trajectory, endpoint phase via complex exponentials, exposure and small-exposure construction; no project-axiom dependency at these audited entries |
| Appendix B | `CZExposure.Pulse.fiber_integrable_and_bound`, `appendixB_Cstar`, `Pulse.fiber_truncation_limit` | Physical-pulse lower bound, integrability of the original fiber density, infimum bound and convergence of finite truncations; no additional area-formula, endpoint or limiting hypothesis supplied by the caller |
| Appendix D | `CZExposure.PhysicalSegment.appendixD`, exercised on `Pulse.toPhysicalSegment` | Actual quotient dynamics and absolutely continuous phase lifts with the required derivatives almost everywhere; the interval must lie inside the pulse and both ground amplitudes must be nonzero there |
| Appendix E | The seven `CZExposure.ConditionalAcceptance` entries | Relaxed equality, smooth bounds, certificates and stationary/partitioned convergence, assuming `EuclideanCurrentSuperposition`; partitioned results also retain a successful pulse below the chosen exposure ceiling |

The B/D ten-entry dependency audit allows only `propext`, `Classical.choice`
and `Quot.sound`. Appendix E's conditional-entry audit checks 18 final/supporting
theorems against the same allowlist. The fixed main-bound entry and NoGo entries
also have executable axiom allowlist checks. Explicit theorem hypotheses are
not eliminated by passing such an audit.

Legacy declarations and old headline theorems remain in the repository; this
acceptance uses the entries above, not the legacy axiom-backed headline.
The package also preserves research modules aimed at eventually eliminating
E's external input. Completing that stronger project is **not** a remaining
task under the boundary accepted for this delivery.

## What was not rerun or claimed

The expensive historical PSD, matrix-domination, upper interval and full
residual numerical calculations were not all recomputed. Their reports are
reused only after exact decoded-input matching; current archive, coverage,
prefix and final-endpoint correspondences were rerun. See `Acceptance.md`
for the detailed finite-check trust boundary. No unconditional kernel proof
of every finite numerical field is claimed. Appendix B's quadrature label
approximately 2.4801 is not asserted by its Lean integral theorem.

There was no manuscript edit, PDF rebuild, message to the source thread,
commit, push, or deployment. Manuscript hashes before and after this work:

- `main.tex`: `2422672d783027c09268b52be0530c93a7a7bcc109b13f011b3dda7eced2202b`
- `main.pdf`: `2e8998477d26131a761a6579d633d01bf9a042351f825581344cfee35f7cb5d4`

## Reproduction

Use a fresh extracted source directory; the bundle intentionally excludes build
caches. Lean/mathlib versions and both Lake manifests are included. The tested
environment is Lean 4.28.0, mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, Python 3.13.5 and python-flint 0.9.0;
see `unified-environment.json`.

Obtain `https://github.com/wanda0929/Lowerbound_pub` at exactly
`139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2`, with a clean worktree. That external
raw-certificate repository and downloaded Lean/mathlib dependencies are not
vendored in this bundle. With Lake on PATH and python-flint installed, run from
the extracted `lean/` directory:

```sh
python -B check_unified.py /path/to/Lowerbound_pub
```

This re-executes the complete acceptance, stops on a failed command, and writes
the unified receipt only after all checks and the final snapshot comparison pass.
To check the packaged bytes without rebuilding, use `sha256sum -c
SNAPSHOT-SHA256.txt` from that same directory. The ordinary
`python -B check_acceptance.py` checks the retained finite-evidence receipt.
