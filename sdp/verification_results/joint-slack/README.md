# Certified lower bound 2.931272845583

The combined certificate proves, in the unrestricted-duration ideal-blockade
stationary-torus model,

    2.931272845583 <= C* < 2.935875225844105.

Exact lower endpoint: `2931272845583/1000000000000`.
Previous lower endpoint: `2.931225938506`.
Exact increase: `0.000046907077`.
Remaining certified bracket width: strictly less than `0.004602380261105`.
This closes about 1.00891% of the previous gap. It does not prove 2.935.

## What changed

Two disjoint slack contributions were strengthened in the unchanged original
global certificate:

- Mandatory cost crossings: simultaneous original-matrix inequalities Q-D>=0
  replace scalar convex budgets and use all selected degree-seven population
  monomials. The independent verifier checks the original matrices directly.
- Trajectory occupation: degree-fourteen cost-dependent slack profiles replace
  worst-case constants on 320 cost intervals. The profiles are integrated exactly;
  4,915,200 rational tensor-coefficient inequalities cover the full state-population
  domain and the entire cost interval, not a sampled trajectory.

The new occupation penalty replaces the old occupation penalty; the new crossing
penalty replaces the old crossing penalty. The two improvements are combined at
the level of the exact terminal polynomial, not by adding rounded bound increases.

See `PROOF.md` for the argument. `RESULT.json` records exact result arithmetic,
workflow provenance, hashes, and verification counts. `certified/` retains both
component certificates and their combined endpoint certificate. All earlier
source-dependent certificates remain in the sibling `population-refinement/`.

## Reproduce from the repository

Check out the research branch `research/terminal-slack-bootstrap-20260905`.
From the repository root:

```bash
python3 -m pip install python-flint
bash verification_results/joint-slack/reproduce.sh "$PWD"
```

The script reruns the preceding interface, projection and subdivision proofs,
then independently verifies the new crossing and cost-profile inequalities,
and finally checks their combined endpoint. It uses no optimization solver.

To rerun the original large native exact source audit as well:

```bash
bash verification_results/joint-slack/reproduce.sh "$PWD" --full-source-audit
```

The optional audit requires Rust and the research branch's
`audit_terminal_bootstrap_source` example. Without this option, the original
source certificate's complete successful audit is an inherited explicit
proof dependency, not something the smaller extension checker pretends to redo.

## Reproduce from the downloaded package

Preserve the sibling directory layout under `verification_results/` in the ZIP.
The package contains the new proof and all the preceding extension data and
verifiers. The two large original source chunks are read from a local checkout
of this repository and are not duplicated in the ZIP.

From the extracted package's root:

```bash
python3 -m pip install python-flint
bash verification_results/joint-slack/reproduce.sh /absolute/path/to/min-exposure-sdp
```

An optional root `reproduce.sh` wrapper in the ZIP invokes the same command.
The exact source chunks are pinned by SHA-256; passing a different source fails.
The repository's original certificate and its `bound_target` are unchanged.

## Completed scientific checks

Joint crossing verification (run 34015889424): 530 original-matrix inequalities,
8,146 matrix coordinates, 1,047 selected state monomials, four mandatory crossings,
1,024 exact population inequalities, 14 exact endpoint identities, 14 positive
endpoint coefficients, and 11 verifier/self-test cases.

Cost-profile verification (run 34016034047): all 320 intervals use a polynomial
profile; 4,915,200 exact coefficient inequalities, 14 exact endpoint identities,
14 positive endpoint coefficients, and eight verifier/self-test cases.

Combined endpoint (run 34016235747): 14 exact interpolation identities, 14 positive
Bernstein coefficients, and five acceptance/rejection cases. Both synthesis and
replay passed. Final retention runs the end-to-end reproducer again before any
scientific result is committed.

The source audit and prior proofs are not replaced by these counts. Mathematical
certification depends on the full chain described in `PROOF.md` and the checked
source-to-trajectory identity.

## Discovery versus acceptance

Crossing discovery uses LP and eigenvector cuts, followed by rigorous repair.
Its feasibility tolerances and floating eigenvalues are not accepted as evidence.
The independent crossing checker uses 384-bit rigorous interval LDL on the
original exact matrices. The polynomial and combined endpoint checks use exact
rational arithmetic. The cost-profile producer uses no new optimizer.

A simultaneous-occupation-matrix-budget experiment produced only a floating
potential gain and is retained as exploratory evidence, not as a certificate.
The certified result above does not include that diagnostic value.
