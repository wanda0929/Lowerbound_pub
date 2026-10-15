# Fresh exact lower-certificate audit — 2026-09-07

Both certificates passed a new execution of the exact auditor built from the
archive's pinned source, not merely a checksum check or reading archived reports.

| Grid | Exit | Wall time | Exact coefficients | Nonzero residuals | Zero / residual-certified Grams |
|---|---:|---:|---:|---:|---:|
| Five-cell shoulder | 0 | 35.383 s | 9,180 | 0 | 332 / 2,333 |
| Six-cell | 0 | 44.518 s | 11,048 | 0 | 403 / 2,815 |

Both reports certify endpoint **293/100**, with all Grams exactly PSD and no
exact-LDL fallback. `strictly_exceeds_target: false` is expected: the certificate
equals 2.930, not a strict improvement over 2.930. The positive-definite count
overlaps the residual-certified count and must not be added to it.

## Retained evidence

- `shoulder.fresh-audit.json` and `six-cell.fresh-audit.json`: actual fresh stdout.
- `runs.json`: successful commands, exit codes, wall time, memory, hashes and
  comparisons against both archived reports. Recorded absolute paths describe
  this particular execution, not portable installation locations.
- `provenance.json`: source/tree, build command, tools and libraries, binary hash,
  and preservation of the user's original checkout.

The parent orb checked these fresh-report hashes and compared their bytes directly
to native and independent reports in the retained original tar archive:

```text
eda531f9fe1d49096880831cf632e92d5e1cc916a392d6dca14be40e7dea8238  shoulder.fresh-audit.json
08d55cd8a764db38ae5c3558146b2c878c8a5d805fab3bdc6eb483b4316f987c  six-cell.fresh-audit.json
```

## Source and reproduction

Source origin: <https://ampcode.com/@wz-s-space/min-exposure-sdp>.
Pinned revision: `45d45bf11abbacd0be693bf0068f78de77d91997`.
Tree: `4e7eef926222544273e2bd20dcabd92091a9fa40`.
The existing Mac checkout was at a different revision; the pinned source was
exported with `git archive` into an isolated temporary directory. All 1,118
exported tracked files matched the pinned tree. No user source files were edited
or checked out, and no code was pushed.

The successful build used Rust/Cargo 1.98.0 on macOS arm64 with cached locked
dependencies, Apple clang 17.0.0, Apple Accelerate and the MOSEK 11.2.3 runtime:

```sh
# Run in the isolated export of the pinned source, with Rust on PATH.
cargo build --offline --locked --release --bin minexposure

# After extracting the certificate archive, run for EACH certificate JSON:
target/release/minexposure audit-exact-split CERTIFICATE --audit-jobs 8
```

`CERTIFICATE` is either `split-o6-shoulder-1-26-target-293-exact-certificate.json`
or `split-o6-six-cell-1-26-target-293-exact-certificate.json` in the extracted
archive. Offline build assumes dependencies are already cached; the command above
records the verified environment rather than promising a clean-machine offline
installation. Source access and build prerequisites must be provided to reviewers.

**Mac loader detail:** this binary dynamically links `libmosek64.11.2.dylib` but
had no resolving `LC_RPATH`. Initial launches failed before audit execution.
Successful launches set process-local `DYLD_LIBRARY_PATH` to the build-produced
MOSEK runtime directory under `target/release/build/mosek-*/out/mosek/11.2/tools/platform/osxaarch64/bin`.
Use the actual directory produced by the build; do not copy a stale temporary
path. Full successful `/usr/bin/time -l … /usr/bin/env DYLD_LIBRARY_PATH=…`
commands are in `runs.json`. No source/binary patch, MOSEK optimization, license
setup or package installation was used to overcome this loader issue.

Mac binary SHA-256:
`dbc21ce7e7fe277e4422dd62f48e15a2ca362cf9412a50f86a95c20fb1e2608c`.
It is not expected to equal the archive's Linux binary hash. Equality of exact
audit reports across the two builds was verified.
