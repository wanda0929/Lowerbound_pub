# Regional allocation and mandatory-prefix lower bound

Latest result: `C* >= 2.931286076089` in the all-duration ideal-blockade stationary-torus model.
The preceding endpoint was `2.931272845583`. The exact improvement is
`0.000013230506`; the inherited strict upper endpoint remains
`2.935875225844105`, so the remaining rigorous gap is less than
`0.004589149755105`. This closes about 0.287471% of the preceding gap.
It does not establish 2.935 or equality with the construction.

## Two verified changes

The regional stage allows a different nonnegative rational allocation of the
original Gram contributions on each of sixteen population rectangles. Every
allocation separately respects the original matrix budgets. Exact degree
(14,7,7) polynomial inequalities cover every rectangle, including the zero-cost
corner. This certifies `2.931285651554`.

The prefix stage then uses that independently proved result to integrate a
previously uncounted, disjoint accumulated-cost interval. Its endpoint is the
already proved regional bound, not the final bound being proved. This certifies
`2.931286076089` without a circular argument.

The new allocation proof replaces the old occupation penalty. Only the new
mandatory prefix is added; it has disjoint cost support. Interface and terminal
certificates are unchanged. No pulse is discretized, no time cap is introduced,
and no optimal-pulse existence assumption is used.

## Reproduction

Use Python with python-flint (the tested version is 0.8.0). Optimization packages
are not needed for verification. From a checkout of the research branch:

```bash
python3 -m pip install python-flint==0.8.0
bash verification_results/adaptive-slack/reproduce.sh "$PWD"
```

Append `--full-source-audit` to rerun the large original native exact audit too.
Otherwise that exact audit is inherited, while the complete predecessor
extension chain and both new proof stages are replayed. The source Rust example
used by this optional audit must be present in the repository checkout.

The download preserves the sibling `verification_results` layout. Its root
`reproduce.sh` takes the absolute path to a repository checkout containing the
original large certificate chunks. Those chunks are not duplicated in the
small supplemental proof bundle.

## Discovery versus acceptance

`produce.py` uses SciPy/HiGHS to propose allocation weights. It converts them to
exact rationals and repairs every budget before constructing a certificate.
Reported optimizer objectives and solver feasibility tolerances are not proofs.

`verify.py` imports no optimizer and no producer. It independently reconstructs
the signed power polynomial and applies rational affine maps. The only allowed
projection IDs are ones checked by the unchanged degree-seven predecessor.
The regional stage checked 4,899,840 exact tensor inequalities, 3,200,013 exact
matrix budgets, and 6,232 such projection IDs; 319 intervals improve and one
retains its stronger inherited profile.

`tail.py --check` separately verifies the additional interval by signed-power
reconstruction and exact endpoint interpolation. It adds 15,360 exact tensor
inequalities. Each stage checks fourteen exact endpoint identities and fourteen
strictly positive Bernstein coefficients. `test_mutations.py` rejects ten
corruptions of the actual regional certificate; the tail checker rejects six
additional corruptions, including overlaps and unproved future prefixes.

See `PROOF.md` for the mathematical argument, `RESULT.json` for the retained
verification status, and `certified/` for exact witnesses and checker outputs.
Source hashes are bindings to required proofs, not replacements for verification.
All earlier source certificate bytes and `bound_target` remain unchanged.
