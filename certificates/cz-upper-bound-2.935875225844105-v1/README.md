# Certified strict upper bound for the ideal-blockade CZ exposure

This package independently verifies the computer-assisted statement

\[
C_* < 2.935875225844105,
\]

where \(C_*\) is the infimum of the dimensionless Rydberg exposure
\(\Omega_{\max}T_R\) over exact two-qubit CZ pulses in the ideal global-drive,
perfect-blockade model.

The package contains the final witness and its verification dependencies. It
does **not** contain or invoke the optimizer that discovered the witness.

## Quick verification

Requirements:

- CPython 3.10 or newer;
- `python-flint==0.9.0` (FLINT/Arb ball arithmetic);
- a POSIX shell and `sha256sum` for `verify.sh`.

From the package root:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
./verify.sh
```

`verify.sh` first checks every supplied payload file against `SHA256SUMS`, then
runs a floating-point witness sanity check and the 500-bit Arb/Krawczyk proof.
It exits nonzero if a hash, dependency version, sanity check, or proof assertion
fails. On an ordinary x86-64 machine the proof takes about 12 seconds.

To use an existing environment, set `PYTHON`, for example:

```bash
PYTHON=/path/to/python ./verify.sh
```

Do not run Python with `-O` or set `PYTHONOPTIMIZE`: the preserved upstream
verifiers express their proof obligations as Python assertions, and the
wrapper rejects optimized mode.

## What is proved

The pulse has 12,672 equal-duration, unit-amplitude, piecewise-constant phase
segments. In normalized time, the one- and two-excitation blockade sectors
have angular rates \(1/2\) and \(\sqrt{2}/2\). If \((g_k,r_k)\) denotes the
terminal ground/Rydberg amplitudes in sector \(k\), the verifier solves the five
real terminal equations

\[
F=(\operatorname{Re}r_1,\operatorname{Im}r_1,
   \operatorname{Re}r_2,\operatorname{Im}r_2,
   \operatorname{Im}\{g_2\overline{g_1^2}\})=0.
\]

All phases except indices 731, 6676, 8661, and 11922 are fixed by the supplied
witness. The duration and those four phases form five variables. Around the
high-precision center, the program evaluates \(F\), its interval Jacobian, the
sector propagators, and the exposure over a radius-\(10^{-80}\) box using
500-bit Arb balls.

For an approximate inverse \(C\) of the center Jacobian and center \(v_0\), it
forms the interval Krawczyk map

\[
K(X)=v_0-CF(v_0)+(I-C[DF(X)])(X-v_0).
\]

The run checks all of the following:

1. the preconditioner \(C\) is nonsingular;
2. every component of \(K(X)\) lies strictly inside \(X\);
3. the induced defect row sums are all below one;
4. the resulting unique local root lies on the CZ branch,
   \(\operatorname{Re}\{g_2\overline{g_1^2}\}<0\);
5. its outward-rounded exposure interval is strictly below the exact decimal
   `2.935875225844105`.

The Krawczyk inclusion establishes an exact feasible CZ pulse near the listed
witness. Since \(C_*\) is an infimum over all feasible exact pulses, existence
of this one pulse proves the strict upper bound. The uniqueness statement is
only uniqueness of the root inside this tiny five-dimensional box.

## What is not proved

- This is not a lower-bound certificate.
- It does not prove local or global optimality of the pulse.
- It does not establish that \(C_*\) equals the displayed exposure.
- The floating-point candidate check alone is not a proof. The theorem-grade
  step is `verification/jan22_cz_exposure_interval_upper.py` using Arb balls.
- The claim applies only to the normalized ideal global-drive,
  perfect-blockade model encoded by the verifier; it is not a finite-blockade
  or experimental-hardware error guarantee.

## Package contents

| Path | Purpose |
|---|---|
| `verification/reference_data/jan22_cz_exposure_candidate_12672.json` | 12,672-segment numerical witness and fixed phases |
| `verification/jan22_cz_exposure_candidate.py` | standard-library floating-point propagation sanity check |
| `verification/jan22_cz_exposure_interval_upper.py` | authoritative 500-bit Arb/Krawczyk proof |
| `verify.py` | dependency/version checks, runs both preserved verifiers, and validates their reported semantics |
| `verify.sh` | payload hash audit plus one-command verification entry point |
| `results.json` | machine-readable statement of the claimed result and proof parameters |
| `reference_run/` | captured successful output and environment information; reference only |
| `PROVENANCE.md` | exact source revisions, paths, and Git blob identifiers |
| `SHA256SUMS` | hashes of all payload files except the checksum file itself |

The files in `reference_run/` are not trusted inputs. A fresh invocation
recomputes the result from the witness and source code.

## Publication and licensing

No license file was present in the source repository at the recorded source
revision, so this package does not invent one. Before public distribution or
archival deposit, the repository owner should add an explicit license and the
paper's citation metadata. See `PROVENANCE.md` for source attribution.
