# Provenance

## Source repository

- Repository: `https://github.com/wanda0929/Finite_blockade_pulse`
- Source revision used for this package:
  `ab9054174e83b6e2b78ce32417ab4fba533726f4`
- Commit that introduced the 12,672-segment strict upper-bound proof:
  `4816d6859f64c1c45a4dab899ec49dfffff94005`
- The later source revision records a fresh successful rerun of the same upper
  certificate with `python-flint==0.9.0`.

The three proof inputs below are copied byte-for-byte from the source revision:

| Packaged path | Git blob ID |
|---|---|
| `verification/jan22_cz_exposure_candidate.py` | `42e1d1dc68608438e1c2714d5e1ee230974c6673` |
| `verification/jan22_cz_exposure_interval_upper.py` | `bb861a464c4dd8128c87637813f2145b1141d51c` |
| `verification/reference_data/jan22_cz_exposure_candidate_12672.json` | `ca1670992aea11fa0adba617f609088747586d74` |

The package-level wrapper, documentation, result summary, reference outputs,
and checksum manifest were added only to make the proof self-contained and
auditable. They do not alter the authoritative verifier.

## Dependency provenance

The rigorous verifier uses `python-flint==0.9.0`, which exposes FLINT/Arb ball
arithmetic. The included reference run used CPython 3.11.6,
`python-flint==0.9.0`, and FLINT 3.6.0 on Linux x86-64. The source repository
also records a successful rerun under Python 3.12.13 with the same
`python-flint` release.

## Scope of reuse

The source repository did not contain a license file at the revision above.
This document records technical provenance but does not grant a license. The
repository owner should select an explicit license before publishing this
package as supplemental material or depositing it in a public archive.
