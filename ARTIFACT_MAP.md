# Manuscript-to-artifact map

Paths below are relative to this publication snapshot, not the development
repositories. "Retained report" does not mean a fresh audit was executed here.

| Manuscript item | Retained supporting artifacts | Status |
| --- | --- | --- |
| Headline lower bound 2.931287735220 | `sdp/verification_results/slack-campaign-2935/dark/`, its parent campaign, six predecessor directories, original O7 certificate chunks, Rust core auditor | Fresh exact global audit, predecessor replay, final checker and mutation checks; logs in `validation/` |
| Direct O7 five-cell 2.9305 | `sdp/verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis/` | Fresh core audit matches retained source-audit report exactly |
| Direct O6 five/six-cell 2.930 | `certificates/order-6-exact-split-dual-2930-v1.tar.gz`, paired audit directory, historical source tarball | Exact payloads and retained independent audit reports; not re-audited in this run |
| Unsplit O8 exact 2.8825 | `sdp/certificates/jan22-cz-exposure-order8-exact-dual.json`, `sdp/generated/exact-audits/` | Payload and retained exact audit; not re-audited in this run |
| Three-cell O7 exact 2.925 | `sdp/verification_results/split-o7-above-2915/` | Audit evidence only; exact payload missing upstream; recovery lead in `PROVENANCE.md` |
| Unsplit O6–O11 numerical hierarchy and dimensions | `finite-source/verification_results/jan22_cz_exposure_stationary_torus_o*_mosek*` and the two solver source modules | Six objective values and all tabulated dimensions checked against manuscript; no new MOSEK solve |
| Strict upper bound 2.935875225844105 | `certificates/cz-upper-bound-2.935875225844105-v1/` | Fresh 500-bit Arb/Krawczyk proof; five strict inclusions |
| 192-segment pulse and dynamics | `proof/data/best_pulse_192.npy`, `proof/scripts/model.py` | Fresh propagation: exposure 2.93595559544107; squared closure residual 4.39e-27 |
| Duration–exposure scan | `proof/data/landscape.json`, `landscape_extra.json`; `proof/scripts/landscape.py`, `grape_fast.py` | Aggregate observations retained; original individual controls not available here |
| First-order stationarity diagnostics | `proof/scripts/certificate.py`, `pmp_dense.py`, `proof/data/cz_multipliers.npy` | Fresh diagnostic execution; not a global-optimality proof |
| Analytical fiber integral ≈2.4801 | `finite-source/verification/jan22_cz_exposure_fiber_bound.py`, its derivation in `finite-source/docs/explanation/` | Fresh numerical estimate and 160-bit Arb lower sum |
| Occupation schematic | `figures/fig_occupation.tex`, `.pdf` | Diagram source and manuscript asset retained |
| Symmetry schematic | `figures/fig_symmetry.tex`, `.pdf` | Diagram source and manuscript asset retained; block dimensions checked against solver outputs |
| Pulse figure | `proof/scripts/make_fig_pulse.py`, `publication.mplstyle`, archived pulse, `figures/fig_pulse.pdf`, `.png` | Original plotting path and assets retained |
| No-go theorems, active-time reduction, nonlocal-phase identity | `main.tex` analytical arguments | No external numerical artifact required |
| Discussion percentage and noise-threshold comparisons | Main bound endpoints and retained pulse/scan values | Derived arithmetic, not additional experiments |

Excluded: development histories, review ledgers, private agent configuration,
stale gap plots using the old 2.930 headline, unrelated finite-blockade and
local-addressing searches, and the optional older conditional Lean window.
