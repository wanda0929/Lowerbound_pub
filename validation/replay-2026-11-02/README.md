# Full lower-bound replay, 2026-11-02

Both lower bounds were independently replayed from the proof materials in
repository revision `3e6146bc9c873ea84e19548cc5c14d5796ac6036`, without the
external attachment or files from the development machine. The combined run
exited successfully (exit code 0). No certificate, verifier, or acceptance
condition was changed. This was certificate verification, not a new SDP solve.

## Commands

With Python 3.11 and python-flint 0.8.0 installed, from `sdp/`:

```bash
export PYTHON=/absolute/path/to/.venv-lower/bin/python
bash verification_results/reachability-slack/reproduce.sh "$PWD" --full-source-audit
"$PYTHON" verification_results/slack-campaign-2935/dark/verify.py --bundle "$PWD" --self-test
```

The original reproduction scripts were used unchanged. A shell wrapper around
Cargo copied its standard output to `global-source-audit.json` before the
upstream script removed its temporary directory; pipeline failures remained
fatal (`set -euo pipefail`).

## Results and evidence

- `global-source-audit.json`: fresh Rust audit of the original O7 certificate
  reconstructed from the repository's two compressed chunks. All 18,739
  coefficient checks passed with zero exact residuals, all Gram matrices were
  certified positive semidefinite, and the bound was `5861/2000 = 2.9305`.
  This report matches both `validation/global-source-audit.json` and
  `sdp/verification_results/population-refinement/certified/source-audit.json`
  byte for byte.
- `predecessor-replay.log`: fresh compilation and complete predecessor replay,
  including projection, population subdivision, interface, cost-profile,
  joint-slack, adaptive-slack, and reachability checks and their self-tests.
  The final predecessor bound was `1465643801663/500000000000 = 2.931287603326`.
- `headline-lower.log` and `final-independent.json`: fresh parent-campaign and
  dark-population acceptance. The final bound was
  `146564386761/50000000000 = 2.931287735220`. The last stage checked 3,751,680
  coefficient inequalities and 243,421 Gram budgets; overlap, inflated-profile,
  and wrong-prefix mutations were rejected.
- `environment.txt`: start time (UTC), Python, python-flint, Rust and Cargo
  versions, and the checked repository revision.

The final checker's report retains its standard dependency text, "source audit
not rerun." That checker does not invoke the native audit itself; this run did
rerun it first through `--full-source-audit`, as recorded above.

All 256 entries of the original root `SHA256SUMS` passed before and after the
run, and tracked repository files remained unchanged. These dated evidence
files are additional records; they do not replace the original validation logs.
