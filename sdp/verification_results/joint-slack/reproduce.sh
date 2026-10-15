#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "Usage: bash reproduce.sh /path/to/min-exposure-sdp [--full-source-audit]" >&2
  exit 2
fi
if [[ $# == 2 && $2 != --full-source-audit ]]; then
  echo "Unknown option: $2" >&2
  exit 2
fi
REPO=$(cd -- "$1" && pwd)
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
VERIFICATION=$(cd -- "$HERE/.." && pwd)
SOURCE="$REPO/verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis"
PYTHON=${PYTHON:-python3}
"$PYTHON" -c 'import flint'
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
# Replay pinned source-dependent projection and population inequalities.
# Only --full-source-audit reruns the large original Rust exact audit;
# otherwise its unchanged, pinned successful audit remains a dependency.
bash "$VERIFICATION/population-refinement/reproduce.sh" "$REPO" "${@:2}"
"$PYTHON" "$VERIFICATION/interface-population/verify.py" \
  --parts-dir "$SOURCE" \
  --certificate "$HERE/certified/crossing-certificate.json" \
  --output "$TMP/crossing-independent.json" --self-test
"$PYTHON" "$VERIFICATION/cost-profile/verify.py" \
  --certificate "$HERE/certified/profile-certificate.json" \
  --output "$TMP/profile-independent.json" --self-test
# Fresh reports are required. Their hashes are themselves pinned by the
# retained endpoint certificate, so silently substituting stale reports fails.
"$PYTHON" "$HERE/combine.py" \
  --crossing "$HERE/certified/crossing-certificate.json" \
  --crossing-report "$TMP/crossing-independent.json" \
  --profile "$HERE/certified/profile-certificate.json" \
  --profile-report "$TMP/profile-independent.json" \
  --check "$HERE/certified/certificate.json" --output "$TMP/combined"
"$PYTHON" - "$TMP/combined/independent.json" <<'PY'
import json,sys
from fractions import Fraction
r=json.load(open(sys.argv[1]));assert r['status']=='PASS'
assert Fraction(r['certified_lower_bound'])==Fraction('2931272845583/1000000000000')
print('VERIFIED: C* >= 2931272845583/1000000000000 = 2.931272845583')
PY
