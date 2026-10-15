# Certified lower bound 2.931225938506

For the all-duration ideal-blockade stationary-torus CZ problem,

```
1465612969253/500000000000 = 2.931225938506 <= C* < 2.935875225844105.
```

The previous certified lower endpoint was 2.931201368260. The exact increase is
0.000024570246. This closes about 0.526% of the previous bracket width, not the
whole gap. The upper endpoint is unchanged. See RESULT.json for exact arithmetic
and PROOF.md for the complete additional argument.

## What was done

The degree-seven trajectory certificate extends the previous degree-five
population-factor search and certifies 2.931224886868. Its original Gram
matrices are unchanged; LP discovers allocation weights which are then
converted to rationals and independently checked.

A second exact-rational step subdivides the population square into 16 boxes
on each of 320 accumulated-cost intervals, without changing the verified
projections or their allocation weights. This certifies 2.931225938506.
It is a positivity proof over the whole square, not a pulse simulation or
sampled-state bound. No duration cap or epsilon-times-duration error is used.

## Reproduce all extension checks

Requires Python >=3.11 and python-flint. The verification path does not require
an SDP or LP optimizer. From this directory (or the extracted proof package):

```bash
python3 -m pip install python-flint
bash reproduce.sh /absolute/path/to/min-exposure-sdp
```

This verifies original-source hashes, replays the exact interface dependency,
rechecks every used degree-seven matrix projection and polynomial inequality,
then independently checks the subdivision extension and its tests.

The original global certificate is an explicit dependency and is not duplicated
in this supplemental package. Its two compressed parts remain in the repository
under verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis.
The default command uses the retained successful exact audit of those source
bytes. To rerun the complete native source audit as well:

```bash
bash reproduce.sh /absolute/path/to/min-exposure-sdp --full-source-audit
```

The full-audit option requires Rust and the research branch's existing
crates/minexposure-core/examples/audit_terminal_bootstrap_source.rs.
The base certificate identity has 18,739 exact coefficient checks and all Gram
matrices are checked for exact positive semidefiniteness. It is not replaced by
trusting the hash of an audit JSON; that JSON records a reproducible dependency.

## Retained evidence

- certified/population-certificate.json.gz: complete degree-seven certificate.
- certified/population-independent.json: independent degree-seven audit.
- certified/subdivision-certificate.json: exact population subdivision extension.
- certified/subdivision-independent.json: independent exact-rational audit.
- certified/trajectory-metadata.json.gz: native physical Gram coordinates.
- certified/source-audit.json: successful full source audit dependency.
- certified/normalized-interface-certificate.json.gz and interface-bases.json:
  earlier exact interface proof inputs.
- SHA256.json: retained file hashes.

The degree-seven proof uses rigorous 384-bit Arb matrix enclosures. Its scalar
polynomial, population and budget checks use exact rationals. The subdivision
extension uses exact rational arithmetic throughout; its independent verifier
uses blossom restriction rather than the producer's de Casteljau subdivision.

Completed scientific runs: 34008303741 (degree seven and independent replay),
34008997701 (subdivision and independent replay). The retention workflow replays
the packaged end-to-end command before saving the new scientific evidence.

## Exploratory attempts are separate

The higher floating dual near 2.933253918843281 was also tested using full
residual repair, cost-safe coordinate restriction, and physical zero-cost-face
projection. None produced a stronger certified bound. Their summaries are
retained under exploratory/ as failed or inconclusive diagnostics, not as
certificates. In particular, small nonzero residuals on the zero-cost face
cannot be accepted merely because they are small in floating arithmetic.

The original source certificate and its bound_target remain unchanged. Earlier
certificates are retained as historical evidence, not overwritten or relabeled.
The research PR remains separate from main.
