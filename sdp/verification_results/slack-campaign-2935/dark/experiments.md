# Further 2.935 searches: evidence and recovery state

These are numerical discovery results, not certificate inputs.

## New dark localizers improve a small SDP, but do not reach the target

A scratch Rust prototype adds scalar occupation localizers
`c(C²-2|D|²)` and `c((U-C)²-2|D|²)` in each cell, where U=2.935887.
Its schema is intentionally exploratory and is not accepted by the original
certificate exporter/checker. The same inequality yields the exact population
extension documented separately in README.md.

With five cells and knots 0,1/32,1/3,2/3,31/32,1:

- Order-four original Clarabel objective: 2.893884628 (approximately).
- With localizers: primal 2.8958829676353344, dual 2.895882966269558.
- Status AlmostSolved; residuals 2.7154374664705275e-7 and
  1.4778529214234415e-7; wall time 43.06 seconds.
- These floating values are not exact lower bounds.
- Exact localizer coefficient tests passed, including 20 independent rational
  sphere-point evaluations with rational and sqrt(2) components separated.
- The order-five composed attempt was killed by the memory limit; kernel
  evidence was retained. MOSEK could not run because no license was available.

## Phase-dependent potential search still has counterexamples

The search retains five physical coordinates after only two gauge reductions.
Shared cost-Bernstein endpoints impose exact continuity by construction;
ground-ray cuts probe small-excitation limits missed by ordinary random starts.
The dark basis includes J=|D|²; two redundant columns were removed using
`1-|Z|²=p1²+(1-p1)J`.

The latest fixed-target run used cost degree four, 903 coefficients, HiGHS warm
bases, a coefficient box of radius one, and 16 adversarial starts. Its target
gain was 0.004349549472381, exceeding the necessary 0.004299549472381 only
at sampled constraints. At iteration 16 it had 9,147 constraints and sampled
margin 0.0003744258077982859, but a newly found point had residual
**-0.33819010740707134**. Therefore this candidate is rejected. Iteration 17
ended at a HiGHS time limit after 771.40 seconds. This is not an impossibility
result for 2.935 or for larger potential families.

The recovery archive contains the floating checkpoint, warm basis, progress,
ground-ray cuts, Python discovery modules, and the modified Rust source files.
It excludes binaries, build caches, and solver credentials. Scratch modules
still reference their original `/tmp` locations: they are recovery material,
not a turnkey portable workflow. Dependencies used for discovery were
numpy 2.4.6, scipy 1.17.1, highspy 1.15.1, and python-flint 0.8.0.

The completed searches leave no running optimization jobs. No paid compute was
provisioned. A stronger high-order SDP with the new phase-sensitive localizers
remains an uncompleted route; the current 31 GiB orb and missing commercial
solver license are practical limits, not mathematical ceilings.
