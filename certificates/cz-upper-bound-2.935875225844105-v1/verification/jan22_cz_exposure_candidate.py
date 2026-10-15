"""Independently propagate the certified 12672-segment JAN22 CZ candidate.

The candidate is a numerical upper witness, not a lower-bound proof.  This
verifier uses only Python's standard library and exact constant-Hamiltonian
segment formulas; the pulse was found with a separate CasADi/IPOPT model.

Run from the repository root with::

    python verification/jan22_cz_exposure_candidate.py
"""

from __future__ import annotations

import cmath
import json
import math
from pathlib import Path

DATA = Path(__file__).with_name("reference_data") / "jan22_cz_exposure_candidate_12672.json"


def propagate(phases: list[float], duration: float, sector: int):
    """Return ``(g, r, integral |r|^2 ds)`` for one JAN22 sector."""
    segment_duration = duration / len(phases)
    angular_rate = math.sqrt(sector) / 2.0
    angle = angular_rate * segment_duration
    cosine, sine = math.cos(angle), math.sin(angle)

    integral_cosine_squared = (
        segment_duration / 2.0 + math.sin(2.0 * angle) / (4.0 * angular_rate)
    )
    integral_sine_squared = (
        segment_duration / 2.0 - math.sin(2.0 * angle) / (4.0 * angular_rate)
    )
    integral_cross_term = (1.0 - math.cos(2.0 * angle)) / (2.0 * angular_rate)

    ground, rydberg = 1.0 + 0.0j, 0.0j
    population_integral = 0.0
    for phase in phases:
        control = cmath.exp(1j * phase)
        quadrature = -1j * control.conjugate() * ground
        population_integral += (
            integral_cosine_squared * abs(rydberg) ** 2
            + integral_sine_squared * abs(quadrature) ** 2
            + integral_cross_term * (rydberg.conjugate() * quadrature).real
        )
        ground, rydberg = (
            cosine * ground - 1j * sine * control * rydberg,
            cosine * rydberg - 1j * sine * control.conjugate() * ground,
        )
    return ground, rydberg, population_integral


def main() -> None:
    candidate = json.loads(DATA.read_text(encoding="utf-8"))
    phases = candidate["phases"]
    duration = candidate["duration"]
    assert len(phases) == candidate["segment_count"]
    assert candidate["amplitude"] == 1.0

    g1, r1, integral1 = propagate(phases, duration, 1)
    g2, r2, integral2 = propagate(phases, duration, 2)
    relative_phase = g2 / g1**2
    exposure = (2.0 * integral1 + integral2) / 4.0

    midpoint_phases = phases[: len(phases) // 2]
    midpoint_g1, midpoint_r1, _ = propagate(midpoint_phases, duration / 2.0, 1)
    midpoint_g2, midpoint_r2, _ = propagate(midpoint_phases, duration / 2.0, 2)
    midpoint_x, midpoint_y = abs(midpoint_r1) ** 2, abs(midpoint_r2) ** 2
    midpoint_z = (
        midpoint_g2.conjugate() * midpoint_g1**2
        + math.sqrt(2.0)
        * midpoint_r2.conjugate()
        * midpoint_g1
        * midpoint_r1
    )
    midpoint_ratio = (
        (2.0 * midpoint_x + midpoint_y)
        / 4.0
        / (midpoint_x * math.sqrt(midpoint_y) / math.sqrt(2.0))
    )
    same_overlap_x = (1.0 + math.sqrt(1.0 - 2.0 * abs(midpoint_z) ** 2)) / 2.0
    cheaper_fiber_ratio = math.sqrt(2.0) * (2.0 + 1.0 / same_overlap_x) / 4.0
    result = {
        "segment_count": len(phases),
        "duration": duration,
        "exposure": exposure,
        "expected_exposure_error": exposure - candidate["exposure"],
        "one_atom_rydberg_residual": abs(r1),
        "two_atom_rydberg_residual": abs(r2),
        "cz_relative_phase_real": relative_phase.real,
        "cz_relative_phase_imag": relative_phase.imag,
        "one_atom_population_integral": integral1,
        "two_atom_population_integral": integral2,
        "midpoint_overlap_re_im": [midpoint_z.real, midpoint_z.imag],
        "midpoint_populations": [midpoint_x, midpoint_y],
        "midpoint_cost_per_overlap_speed": midpoint_ratio,
        "same_overlap_cheaper_fiber_ratio": cheaper_fiber_ratio,
    }

    assert result["one_atom_rydberg_residual"] < 2e-14
    assert result["two_atom_rydberg_residual"] < 2e-14
    assert abs(result["cz_relative_phase_real"] + 1.0) < 1e-12
    assert abs(result["cz_relative_phase_imag"]) < 2e-14
    assert abs(result["expected_exposure_error"]) < 2e-13
    assert 2.0 * abs(midpoint_z) ** 2 < 1.0
    assert result["same_overlap_cheaper_fiber_ratio"] < result["midpoint_cost_per_overlap_speed"]
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
