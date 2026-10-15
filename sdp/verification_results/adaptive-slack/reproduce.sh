#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo 'Usage: bash reproduce.sh /path/to/min-exposure-sdp [--full-source-audit]' >&2
  exit 2
fi
REPO=$(cd -- "$1" && pwd)
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
PYTHON=${PYTHON:-python3}
"$PYTHON" -c 'import flint'
# This replays every preceding extension, not just the hashes of its reports.
bash "$HERE/../joint-slack/reproduce.sh" "$REPO" "${@:2}"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
gzip -dc "$HERE/certified/certificate.json.gz" > "$TMP/regional.json"
"$PYTHON" "$HERE/verify.py" --certificate "$TMP/regional.json" --output "$TMP/regional-independent.json" --self-test
"$PYTHON" "$HERE/test_mutations.py" --certificate "$TMP/regional.json" --output "$TMP/mutation-tests.json"
"$PYTHON" "$HERE/tail.py" --regional-certificate "$TMP/regional.json" --regional-report "$TMP/regional-independent.json" --check "$HERE/certified/tail-certificate.json" --output "$TMP/tail" --self-test
"$PYTHON" - "$TMP/tail/independent.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]));assert r['status']=='PASS'
print('VERIFIED: C* >=',r['certified_lower_bound'],'=',r['bound_decimal'])
PY
