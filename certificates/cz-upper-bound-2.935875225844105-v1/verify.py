#!/usr/bin/env python3
"""Run and semantically check the standalone upper-bound certificate."""

from __future__ import annotations

import json
import platform
import subprocess
import sys
from pathlib import Path

EXPECTED_PYTHON_FLINT = "0.9.0"
EXPECTED_BOUND = "2.935875225844105"
EXPECTED_SEGMENTS = 12_672
ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"verification failed: {message}")


def run_json(relative_path: str) -> dict:
    completed = subprocess.run(
        [sys.executable, str(ROOT / relative_path)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise SystemExit(
            f"verification failed: {relative_path} did not emit JSON: {error}"
        ) from error


def main() -> None:
    require(__debug__, "Python optimized mode disables upstream proof assertions")

    try:
        import flint
    except ImportError as error:
        raise SystemExit(
            "verification failed: install python-flint==0.9.0 from requirements.txt"
        ) from error

    require(
        flint.__version__ == EXPECTED_PYTHON_FLINT,
        f"expected python-flint {EXPECTED_PYTHON_FLINT}, got {flint.__version__}",
    )

    candidate = run_json("verification/jan22_cz_exposure_candidate.py")
    require(candidate.get("segment_count") == EXPECTED_SEGMENTS, "wrong segment count")
    require(candidate.get("one_atom_rydberg_residual", 1.0) < 2e-14, "one-atom closure failed")
    require(candidate.get("two_atom_rydberg_residual", 1.0) < 2e-14, "two-atom closure failed")
    require(abs(candidate.get("cz_relative_phase_real", 0.0) + 1.0) < 1e-12, "CZ real phase failed")
    require(abs(candidate.get("cz_relative_phase_imag", 1.0)) < 2e-14, "CZ imaginary phase failed")

    interval = run_json("verification/jan22_cz_exposure_interval_upper.py")
    require(
        interval.get("krawczyk_strict_inclusions") == [True] * 5,
        "not all five Krawczyk inclusions are strict",
    )
    require(interval.get("unique_exact_terminal_root") is True, "exact-root proof failed")

    # The authoritative verifier compares its Arb upper endpoint with an Arb
    # constructed from this exact decimal. Import the preserved source constant
    # to keep the package summary from passing through a binary float.
    sys.path.insert(0, str(ROOT))
    from verification.jan22_cz_exposure_interval_upper import CERTIFIED_UPPER_BOUND

    require(CERTIFIED_UPPER_BOUND == EXPECTED_BOUND, "unexpected exact upper-bound decimal")

    print(
        json.dumps(
            {
                "package_verification": True,
                "claim": f"C_* < {EXPECTED_BOUND}",
                "certified_upper_bound_decimal": EXPECTED_BOUND,
                "python": platform.python_version(),
                "python_flint": flint.__version__,
                "flint": getattr(flint, "__FLINT_VERSION__", "unknown"),
                "candidate_check": candidate,
                "interval_certificate": interval,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
