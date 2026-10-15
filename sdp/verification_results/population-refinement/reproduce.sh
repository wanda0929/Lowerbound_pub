#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "Usage: bash reproduce.sh /path/to/min-exposure-sdp [--full-source-audit]" >&2
  exit 2
fi
REPO=$(cd -- "$1" && pwd)
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
SOURCE="$REPO/verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis"
PYTHON=${PYTHON:-python3}
"$PYTHON" -c 'import flint'
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
SOURCE_AUDIT="$HERE/certified/source-audit.json"
if [[ ${2:-} == --full-source-audit ]]; then
  cat "$SOURCE/certificate.json.gz.part-00" "$SOURCE/certificate.json.gz.part-01" | gzip -dc > "$TMP/source-certificate.json"
  (cd "$REPO" && cargo run --locked --release -p minexposure-core --example audit_terminal_bootstrap_source -- "$TMP/source-certificate.json") > "$TMP/source-audit.json"
  SOURCE_AUDIT="$TMP/source-audit.json"
elif [[ $# == 2 ]]; then
  echo "Unknown option: $2" >&2
  exit 2
fi
gzip -dc "$HERE/certified/normalized-interface-certificate.json.gz" > "$TMP/interface.json"
gzip -dc "$HERE/certified/population-certificate.json.gz" > "$TMP/base.json"
gzip -dc "$HERE/certified/trajectory-metadata.json.gz" > "$TMP/metadata.json"
"$PYTHON" "$HERE/verify_normalized_interface_slack.py" \
  --certificate "$TMP/interface.json" --parts-dir "$SOURCE" \
  --bases "$HERE/certified/interface-bases.json" --source-audit "$SOURCE_AUDIT" \
  --output "$TMP/interface-independent.json" --self-test
"$PYTHON" "$HERE/verify_population_slack.py" \
  --certificate "$TMP/base.json" --parts-dir "$SOURCE" \
  --metadata "$TMP/metadata.json" --source-audit "$SOURCE_AUDIT" \
  --interface-report "$TMP/interface-independent.json" --output "$TMP/base-independent.json"
cmp "$TMP/base-independent.json" "$HERE/certified/population-independent.json"
"$PYTHON" "$HERE/verify_population_subdivision.py" \
  --base-certificate "$TMP/base.json" --base-report "$TMP/base-independent.json" \
  --certificate "$HERE/certified/subdivision-certificate.json" \
  --output "$TMP/subdivision-independent.json" --self-test
"$PYTHON" "$HERE/test_verifier.py"
echo 'VERIFIED: C* >= 1465612969253/500000000000 = 2.931225938506'
