#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"

sha256sum --check SHA256SUMS

if [ -n "${PYTHON:-}" ]; then
    python=$PYTHON
elif [ -x .venv/bin/python ]; then
    python=.venv/bin/python
else
    python=python3
fi

"$python" verify.py
