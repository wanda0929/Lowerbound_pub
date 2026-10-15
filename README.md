# Lowerbound_pub

Code, data, and exact certificates supporting the accompanying manuscript
`main.tex`: exposure bounds for an ideal-blockade CZ gate under one global
drive, with unrestricted finite duration.

The headline interval is

**2.931287735220 ≤ C* < 2.935875225844105.**

This is a curated snapshot, not a merge of development histories. It includes
the lower-proof dependency chain, not just its final checker. The original
manuscript is copied unchanged; its old companion-repository paths are mapped
below. At the owner's direction, this repository remains private until public
release is separately authorized at publication. See `RELEASE_CHECKLIST.md`.

## Contents

| Location | Purpose |
| --- | --- |
| `main.tex`, `main.pdf` | Manuscript snapshot, not an edited availability statement |
| `sdp/` | Native exact auditor, pinned source certificate, predecessor proof chain, final slack checker |
| `certificates/` | Order-6 exact archives and audit records; standalone interval upper proof |
| `finite-source/` | Pinned Python stationary-torus SDP source, order-6–11 numerical outputs, analytical fiber integral |
| `proof/` | Archived 192-segment waveform, duration scan, propagation, optimization and stationarity diagnostics |
| `figures/` | The manuscript's three figures and available figure sources |
| `historical-source/` | Historical auditor source snapshots named by the manuscript |
| `validation/` | Fresh verification evidence from this packaging run |

See `PROVENANCE.md` for exact source revisions and `REPRODUCE.md` for commands.
`SHA256SUMS` covers retained package files, excluding Git metadata and build
caches. From the repository root, run `sha256sum -c SHA256SUMS`.

## Verification versus numerical discovery

The rigorous lower proof and upper proof require **no SDP optimizer or MOSEK
license**. The lower proof uses exact rational arithmetic and a Rust core-only
source audit. The upper proof uses Arb ball arithmetic and a Krawczyk inclusion.
Use separate Python environments: lower proof `python-flint==0.8.0`; upper proof
`python-flint==0.9.0`.

Rerunning the original stationary-torus optimization requires MOSEK and an
appropriate license; the retained floating objectives are **not certificates**.
Waveform searches and stationarity diagnostics are also numerical, not proofs
of global optimality.

## Known coverage limits

- The headline lower proof and its original global source certificate are
  included. The original attachment is reconstructed as the six sibling proof
  directories inside `sdp/verification_results/`; use `--bundle "$PWD"` from
  `sdp/`, not the manuscript's now-absent attachment directory.
- The weaker three-cell O7 comparison value **2.9250** has retained audit
  reports, but its exact certificate was intentionally not committed upstream.
  That row is not independently replayable from this snapshot. It is not a
  prerequisite for the stronger headline proof.
- Duration-scan aggregate data are retained. Individual controls for each
  duration were not retained upstream here. The provided search code enables
  rerunning the numerical procedure and generating new pulse candidates and
  aggregates, as documented in `REPRODUCE.md`. This is not a replay of the
  missing original controls; identical pointwise results are not guaranteed.
- The 192-segment illustrative pulse is not the 12,672-segment rigorous upper
  witness. Both are included and labeled separately.
- Optional Lean material and unrelated finite-blockade/local-addressing
  investigations are excluded; they do not establish the current headline.
- Software is MIT licensed; scientific data are CC BY 4.0. Manuscript and
  figure reuse rights are not newly granted. See `LICENSING.md` for scope and
  attribution, and preserve existing third-party notices.
