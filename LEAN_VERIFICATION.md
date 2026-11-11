# Lean verification: scope, evidence, and reproduction

The main-bound reasoning, NoGo construction, and Appendix B/D connections have
Lean proofs. Appendix E has conditional Lean proofs with an explicit external
flow-decomposition input. The main numerical bracket additionally uses external
finite certificate checks. **This is not an unconditional Lean-kernel proof of
every statement and numerical calculation in the manuscript.**

All 469 files of the accepted `lean/` snapshot are included here, unchanged from
[the source commit](https://github.com/wanda0929/LowerBoundCZ/commit/7f9d30aa63e55d3b68f65a6e67b5ef64e2b0e6fb).
Readers do not need access to that development repository or to an agent
conversation: the proofs, data bindings, checkers, logs and dependency locks
are present in this public repository. Lean/mathlib dependencies are downloaded
at their pinned versions; compiled caches and virtual environments are excluded.

## Follow a conclusion to its theorem and evidence

| Conclusion | Lean entry and source | Retained conditions and audit |
|---|---|---|
| **2.931287735220 ≤ labCstar < 2.935875225844105** | `LowerBoundCZ.Certification.FixedArchive.lab_window` in [FixedArchive.lean](lean/LowerBoundCZ/FixedArchive.lean) | Explicit `FixedArchive.Acceptance` finite checks; [65-field map](lean/Acceptance.md), [machine-readable evidence](lean/acceptance-manifest.json), [fixed-archive audit](lean/FixedArchiveAudit.lean) |
| No positive single-block exposure floor under the stated phase/drive conditions | `LowerBoundCZ.theorem_free`, `theorem_relax'`, and the actual chirped-loop construction in [NoGo.lean](lean/LowerBoundCZ/NoGo.lean) | The theorem's stated coupling/target conditions; [NoGoAudit.lean](lean/NoGoAudit.lean) checks trajectory, exponential terminal phase, exposure scaling and axiom dependencies |
| Appendix B's analytical fiber-integral lower bound | `CZExposure.Pulse.fiber_integrable_and_bound`, `appendixB_Cstar`, `Pulse.fiber_truncation_limit` in [AppendixB.lean](lean/LowerBoundCZ/AppendixB.lean) | Physical pulse assumptions; integrability and finite-truncation convergence are proved, not supplied as additional inputs; [B/D audit](lean/AppendixBDAudit.lean). The decimal ≈2.4801 is a separate [numerical integral calculation](finite-source/verification/jan22_cz_exposure_fiber_bound.py) |
| Appendix D's physical quotient dynamics and actual phase derivatives | `CZExposure.PhysicalSegment.appendixD` in [AppendixD.lean](lean/LowerBoundCZ/AppendixD.lean) | A subinterval of the pulse with both ground amplitudes nonzero; absolutely continuous phase lifts and derivatives almost everywhere; [B/D audit](lean/AppendixBDAudit.lean) applies it to the successful-pulse model |
| Appendix E's relaxed equality, polynomial certificates and stationary/partitioned convergence | The seven `CZExposure.ConditionalAcceptance` entries in [ConditionalAcceptance.lean](lean/appendix-e/RequestProject/AppendixE/ConditionalAcceptance.lean) | Explicit `EuclideanCurrentSuperposition`; partitioned results also require a successful pulse below the chosen ceiling; [final audit](lean/appendix-e/ConditionalAcceptanceAudit.lean), [full input specification](lean/appendix-e/ConditionalAcceptance.md), [external literature justification](lean/appendix-e/ExternalSuperpositionJustification.md) |

The audits of accepted entries reject project axioms and `sorryAx`, allowing
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. This does
not discharge explicit hypotheses in their theorem statements. In particular,
E's flow decomposition remains an external mathematical input; its written
literature justification is not itself a Lean proof of that input.

Legacy axiom-backed headline declarations remain in the library for provenance.
Use the final entries above, not the old `Results` headline, to assess coverage.
Compiling a library that contains axioms is not, by itself, evidence that every
declaration is unconditional. The entry-specific dependency audits are included
for that reason.

## What the stored acceptance establishes

The unified run completed on 2026-11-11 at 12:55:14 UTC. The unchanged
[receipt](lean/unified-acceptance.json) binds 366 source/configuration hashes
and 67 successful command records:

- Both libraries built successfully: 8,300 build jobs.
- The finite-evidence replay ran a build, eight Lean decoders producing nine
  dumps, and four external correspondence checks. All six inputs needed to
  reuse the retained numerical reports matched their expected hashes exactly.
- The acceptance index mapped 65 finite leaf fields and checked 327 file hashes.
- All five CLI regressions passed, including rejection of a changed terminal
  matrix, changed interface weights, changed report, and missing replay receipt.
- All 63 additional Lean audit scripts passed: four parent-library audits and
  all 59 Appendix E audits.

The [source-and-log receipt](lean/unified-acceptance.json),
[finite replay receipt](lean/acceptance-replay.json),
[audit logs](lean/unified-evidence/), and
[decoder/correspondence logs](lean/acceptance-evidence/) are inspectable locally.
The 2026-11-11 publication transfer checks are in
[validation/lean-publication-check.json](validation/lean-publication-check.json).
They check the copied bytes and receipt integrity; they are not a claim that
the entire long unified run was repeated merely to move unchanged files.

**External numerical boundary.** The unified run did not recompute every
expensive historical PSD, matrix-domination, upper interval and residual
calculation. It reused their reports after exact-input matching. The 65 fields
are not a constructed Lean proof term of `FixedArchive.Acceptance`. To rerun
the independent numerical headline proofs, follow sections 1 and 2 of
[REPRODUCE.md](REPRODUCE.md), in their separate Python environments. Optimizer
discovery runs, illustrative waveforms, and empirical scans are not proofs of
global optimality.

## Quick integrity check — no theorem recompilation

From a fresh clone of this repository, before regenerating any logs:

```bash
sha256sum -c SHA256SUMS
(
  cd lean
  sha256sum -c SNAPSHOT-SHA256.txt
  python3 -B check_acceptance.py
)
```

Expected final checker output includes `65 acceptance leaf fields mapped` and
`327 local file hashes match`. This verifies the retained package and receipts;
it does not re-execute Lean or the numerical computations.

## Rebuild and rerun the unified acceptance

The tested environment is Lean 4.28.0, Python 3.13.5 and python-flint 0.9.0;
exact versions are in [unified-environment.json](lean/unified-environment.json).
Install [elan](https://github.com/leanprover/elan#installation) and put its
`lake`/`lean` commands on PATH. The supplied toolchain and Lake manifests pin
Lean and mathlib. The run was tested on a 16 GiB Linux machine; allow several
GB for dependency caches and tens of minutes for building and auditing.
No MOSEK license is needed for this verification path.

The checkers deliberately pin the original numerical-data revision
`139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2`. Adding Lean files changes HEAD, so
**do not pass the current checkout as the checker's data input**. Obtain that
exact data revision from this same public repository in a detached worktree:

```bash
# Start at the root of a full clone of this repository.
ROOT="$PWD"
git fetch origin 139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2
mkdir -p reproduced
git worktree add --detach "$ROOT/reproduced/lean-inputs" \
  139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2
python3 -m venv .venv-lean
.venv-lean/bin/pip install python-flint==0.9.0
(
  cd lean
  lake exe cache get
  "$ROOT/.venv-lean/bin/python" -B check_unified.py \
    "$ROOT/reproduced/lean-inputs"
)
```

On a repeated run, reuse the existing clean `reproduced/lean-inputs` worktree
instead of adding it again. The driver checks its revision and cleanliness.
It stops on a failed command or source drift and publishes a unified receipt
only after all checks pass. Dependency downloads require network access; none
requires private repository access.

A rerun regenerates logs and receipts, including machine-specific paths and
timestamps. This intentionally changes their original package hashes. Verify
the shipped hashes **before** rerunning; keep the fresh outputs separately if
you need both historical and new evidence. Do not edit the pinned revision
constants or old reports merely to make a check pass.

## Manuscript version and historical metadata

This addition preserves this repository's original `main.tex` and `main.pdf`.
They are not byte-identical to the later development manuscript whose hashes
appear in `lean/UnifiedAcceptance.md`. The table above identifies the actual
formalized conclusions; no whole-manuscript version-equivalence audit is
asserted by the file transfer. Paper text, figure readability, literature
positioning and submission metadata are outside Lean's mathematical checks.

The copied acceptance report describes its pre-commit execution state, and
some provenance/logs retain development paths and thread identifiers. Those
are historical metadata, not required online inputs. The accepted snapshot is
now committed here, and all reviewer-facing commands above use only this
repository and its pinned public dependencies.
