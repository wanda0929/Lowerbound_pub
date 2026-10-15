# Reproduction

Run from this repository's root unless a step says otherwise. Do not use
`python -O` or `PYTHONOPTIMIZE`: some inherited proof obligations are assertions.
The scripts below are existing upstream tools; no acceptance gate was relaxed.

## 1. Exact lower bound, including the original global audit

Requirements: Python 3.11, `python-flint==0.8.0`, a current stable Rust toolchain,
Cargo, C build tools, Bash, gzip and sha256sum. No MOSEK license is needed for
the core-only audit. The first Cargo build downloads locked dependencies.

```bash
python3 -m venv .venv-lower
.venv-lower/bin/pip install python-flint==0.8.0
export PYTHON="$PWD/.venv-lower/bin/python"
(
  cd sdp
  B=verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis
  sha256sum -c "$B/certificate.parts.sha256"
  bash verification_results/reachability-slack/reproduce.sh \
    "$PWD" --full-source-audit
  "$PYTHON" verification_results/slack-campaign-2935/dark/verify.py \
    --bundle "$PWD" --self-test
)
```

The predecessor command recompiles the core-only Rust example, reconstructs the
486,619,332-byte original certificate in a temporary directory, audits it, and
replays the complete extension chain. The final command first checks its parent
extension, then certifies the endpoint **146564386761/50000000000**. It writes
fresh `independent.json` files next to the two final checkers; root checksums
may need regeneration if their deterministic content changes on another stack.

The packaged fresh global audit is in `validation/global-source-audit.json`:
18,739 exact identities, zero residuals, all Grams PSD, bound 5861/2000. It
matches the chain's inherited source-audit input byte for byte. The separate
fresh full predecessor replay and final extension logs are retained alongside
it. This fresh source audit is an additional packaging check: the unmodified
final checker still describes its own source-audit dependency as inherited.

## 2. Strict interval upper bound

Use a different environment; this wrapper intentionally pins python-flint 0.9.0.

```bash
python3 -m venv .venv-upper
.venv-upper/bin/pip install python-flint==0.9.0
PYTHON="$PWD/.venv-upper/bin/python" \
  sh certificates/cz-upper-bound-2.935875225844105-v1/verify.sh
```

Expected: `package_verification: true`, five strict Krawczyk inclusions, and
`unique_exact_terminal_root: true`, proving C* < 2.935875225844105.

## 3. Analytical fiber integral and illustrative waveform

```bash
.venv-lower/bin/pip install numpy==2.4.6 scipy==1.17.1 matplotlib==3.11.2
.venv-lower/bin/python finite-source/verification/jan22_cz_exposure_fiber_bound.py
.venv-lower/bin/python -c "import sys; sys.path.insert(0,'proof/scripts'); \
import numpy as np; from model import gate_report; \
x=np.load('proof/data/best_pulse_192.npy'); \
print(gate_report(x,np.full(len(x),7.725/len(x))))"
.venv-lower/bin/python proof/scripts/make_fig_pulse.py
```

Expected fiber estimate: approximately 2.4800793677, with certified strict
lower sum > 2.48007. Expected illustrative pulse: exposure 2.93595559544107
and squared Rydberg closure residual approximately 4.39e-27. This floating
closure diagnostic is not the interval existence proof in step 2.

For stationarity diagnostics, run `certificate.py` from `proof/data/`, adding
the corresponding absolute script path to the Python invocation. Its
transitive dependencies and `cz_multipliers.npy` are included.

## 4. Numerical table and waveform discovery (optional)

The original MOSEK environments and objectives for orders 6–11 are in
`finite-source/verification_results/`. Re-solving is expensive and separate
from verification. With CVXPY, NumPy, SciPy, MOSEK and a valid license installed:

```bash
mkdir -p reproduced
(
  cd finite-source
  python -m verification.jan22_cz_exposure_stationary_torus_sdp \
    --order 6 --solver MOSEK --verbose --output ../reproduced/order6.json
)
```

The recorded discovery stack was Python 3.14.0, CVXPY 1.9.2, NumPy 2.4.6,
SciPy 1.17.1 and MOSEK 11.2.3. It was not re-solved during packaging. Repeat
with `--order` 7 through 11 only if those searches are needed.

`proof/scripts/landscape.py` generates new 96-segment multistart scans. Run it
from a scratch directory with requested durations as positional arguments;
it writes `landscape.json` and pulse files. The retained aggregate scan is in
`proof/data/`; exact original per-duration controls are not included.

## 5. Historical order-6 and unsplit order-8 certificates

The exact order-6 payloads are compressed because their raw JSON files exceed
GitHub's ordinary file limit. Extract
`certificates/order-6-exact-split-dual-2930-v1.tar.gz` in a scratch directory,
then use `audit-exact-split` in the historical Rust CLI source archive.
The unsplit O8 certificate is `sdp/certificates/jan22-cz-exposure-order8-exact-dual.json`
and uses the CLI's `audit-exact` command. Historical successful audit records
are retained. These older CLI builds have solver/linker dependencies, unlike
the optimizer-free core-only source audit for the headline proof.

## 6. Manuscript and schematic figures

Use a TeX installation with REVTeX 4.2, AMS packages, booktabs, hyperref, Latin
Modern, standalone and TikZ. Compile the two schematic figure `.tex` files
inside `figures/` if changing them, then compile `main.tex` twice from the root.
The three manuscript PDF figures are already included. No manuscript text was
rewritten as part of packaging.
