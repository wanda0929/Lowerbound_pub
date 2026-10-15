#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo 'Usage: bash reproduce.sh /path/to/min-exposure-sdp [--full-source-audit]' >&2
  exit 2
fi
if [[ $# == 2 && $2 != --full-source-audit ]]; then
  echo "Unknown option: $2" >&2
  exit 2
fi
REPO=$(cd -- "$1" && pwd)
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
PYTHON=${PYTHON:-python3}
"$PYTHON" -c 'import flint'
# Hashes are provenance, not substitutes for the predecessor proofs.
bash "$HERE/../adaptive-slack/reproduce.sh" "$REPO" "${@:2}"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
"$PYTHON" "$HERE/verify.py" \
  --certificate "$HERE/certified/occupation-certificate.json" \
  --output "$TMP/occupation-independent.json" --self-test
cmp "$TMP/occupation-independent.json" "$HERE/certified/occupation-independent.json"
"$PYTHON" "$HERE/crossings.py" \
  --occupation "$HERE/certified/occupation-certificate.json" \
  --occupation-report "$TMP/occupation-independent.json" \
  --check "$HERE/certified/certificate.json" \
  --output "$TMP/final" --self-test
"$PYTHON" - "$TMP/final/independent.json" <<'PY'
import json,sys
from fractions import Fraction
r=json.load(open(sys.argv[1]))
assert r['status']=='PASS'
assert Fraction(r['certified_lower_bound'])==Fraction('1465643801663/500000000000')
print('VERIFIED: C* >= 1465643801663/500000000000 = 2.931287603326')
PY
