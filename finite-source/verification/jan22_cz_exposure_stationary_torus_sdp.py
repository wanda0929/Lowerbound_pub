"""Solve the unrestricted JAN22 exposure hierarchy with both exact U(1)s.

The perfect-blockade CZ problem has two commuting continuous symmetries:

1. laser phase:
   ``u -> exp(i theta) u`` and ``r_k -> exp(-i theta) r_k``;
2. the removable one-qubit phase:
   ``(g1, r1) -> exp(i alpha) (g1, r1)`` and
   ``(g2, r2) -> exp(2 i alpha) (g2, r2)``.

The remaining exact reflection ``u -> -conj(u)``, with both state spinors
conjugated, makes every invariant moment real or purely imaginary according
to a known parity.  Rephasing odd monomials by ``i`` therefore turns every
Hermitian moment block into a real symmetric block.

The second action preserves both the identity relation ``g2 = g1**2`` and the
CZ relation ``g2 = -g1**2``.  Averaging a physical trajectory over this gauge
orbit preserves its cost and Liouville equations.  Full real-SOS Gram bases
therefore split exactly by a pair of integer charges.  This torus reduction is
a block diagonalization, not a relaxation of the physical problem.

There is no time coordinate, so an exactified dual certificate applies to all
finite pulse durations.  Floating solver objectives remain discovery data and
are not rigorous numerical lower bounds until their dual SOS identities are
verified in exact arithmetic.

Run from the repository root with::

    .venv/bin/python -m verification.jan22_cz_exposure_stationary_torus_sdp \
        --order 3 --solver CLARABEL
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy import sparse

from verification.jan22_cz_exposure_complex_moment_sdp import (
    BULK_VARIABLE_COUNT,
    G2,
    R1,
    R2,
    STATE_VARIABLE_COUNT,
    Exponent,
    MomentKey,
    Polynomial,
    conjugate_key,
    initial_value,
    liouville_derivative,
    modulus_squared,
    moment_expression,
    monomials,
    shift_key,
    unit_polynomial,
)

Charge = tuple[int, int]

# Variable orders are (u, g1, r1, g2, r2) and (g1, r1, g2, r2).
BULK_TORUS_CHARGES = (
    (1, 0),
    (0, 1),
    (-1, 1),
    (0, 2),
    (-1, 2),
)
STATE_TORUS_CHARGES = ((0, 1), (-1, 1), (0, 2), (-1, 2))


def torus_charge(exponent: Exponent, charges: tuple[Charge, ...]) -> Charge:
    return tuple(
        sum(power * weight[axis] for power, weight in zip(exponent, charges))
        for axis in range(2)
    )


def invariant_monomials(
    variable_count: int, maximum_degree: int, charges: tuple[Charge, ...]
) -> list[MomentKey]:
    """Return all time-independent mixed monomials neutral under both U(1)s."""
    through_degree = [
        monomials(variable_count, degree) for degree in range(maximum_degree + 1)
    ]
    result: list[MomentKey] = []
    for anti in through_degree[maximum_degree]:
        remaining = maximum_degree - sum(anti)
        anti_charge = torus_charge(anti, charges)
        for holo in through_degree[remaining]:
            if torus_charge(holo, charges) == anti_charge:
                result.append((0, anti, holo))
    return result


def mixed_basis(
    variable_count: int, maximum_degree: int, charges: tuple[Charge, ...]
) -> dict[Charge, list[MomentKey]]:
    """Group the full real-SOS mixed basis by its pair of torus charges."""
    through_degree = [
        monomials(variable_count, degree) for degree in range(maximum_degree + 1)
    ]
    blocks: dict[Charge, list[MomentKey]] = defaultdict(list)
    for anti in through_degree[maximum_degree]:
        remaining = maximum_degree - sum(anti)
        anti_charge = torus_charge(anti, charges)
        for holo in through_degree[remaining]:
            holo_charge = torus_charge(holo, charges)
            net = tuple(right - left for left, right in zip(anti_charge, holo_charge))
            blocks[net].append((0, anti, holo))
    return dict(blocks)


def normal_form(key: MomentKey, variable_count: int) -> Polynomial:
    """Reduce a monomial by the unit-control and two sphere equalities."""
    time_power, anti_tuple, holo_tuple = key
    anti = list(anti_tuple)
    holo = list(holo_tuple)
    if variable_count == BULK_VARIABLE_COUNT:
        control_pairs = min(anti[0], holo[0])
        anti[0] -= control_pairs
        holo[0] -= control_pairs
        sphere_pairs = ((1, 2), (3, 4))
    elif variable_count == STATE_VARIABLE_COUNT:
        sphere_pairs = ((0, 1), (2, 3))
    else:
        raise ValueError(f"No quotient relations configured for {variable_count} variables")

    paired_powers: list[tuple[int, int]] = []
    for ground, rydberg in sphere_pairs:
        pairs = min(anti[ground], holo[ground])
        anti[ground] -= pairs
        holo[ground] -= pairs
        paired_powers.append((rydberg, pairs))

    result: Polynomial = {(time_power, tuple(anti), tuple(holo)): 1.0}
    for rydberg, pairs in paired_powers:
        expanded: Polynomial = {}
        for reduced_key, coefficient in result.items():
            for power in range(pairs + 1):
                next_anti = list(reduced_key[1])
                next_holo = list(reduced_key[2])
                next_anti[rydberg] += power
                next_holo[rydberg] += power
                next_key = (reduced_key[0], tuple(next_anti), tuple(next_holo))
                expanded[next_key] = expanded.get(next_key, 0.0) + (
                    coefficient * ((-1.0) ** power) * math.comb(pairs, power)
                )
        result = expanded
    return result


def reduce_polynomial(polynomial: Polynomial, variable_count: int) -> Polynomial:
    result: Polynomial = {}
    for key, coefficient in polynomial.items():
        for reduced_key, reduced_coefficient in normal_form(key, variable_count).items():
            value = result.get(reduced_key, 0.0) + coefficient * reduced_coefficient
            if value == 0.0j:
                result.pop(reduced_key, None)
            else:
                result[reduced_key] = value
    return result


def is_normal_monomial(key: MomentKey, variable_count: int) -> bool:
    _, anti, holo = key
    paired_variables = (
        (0, 1, 3)
        if variable_count == BULK_VARIABLE_COUNT
        else (0, 2)
    )
    return all(not (anti[variable] and holo[variable]) for variable in paired_variables)


def normal_invariant_monomials(
    variable_count: int, maximum_degree: int, charges: tuple[Charge, ...]
) -> list[MomentKey]:
    return [
        key
        for key in invariant_monomials(variable_count, maximum_degree, charges)
        if is_normal_monomial(key, variable_count)
    ]


def normal_mixed_basis(
    variable_count: int, maximum_degree: int, charges: tuple[Charge, ...]
) -> dict[Charge, list[MomentKey]]:
    result: dict[Charge, list[MomentKey]] = {}
    for block_charge, basis in mixed_basis(
        variable_count, maximum_degree, charges
    ).items():
        normal_basis = [
            key for key in basis if is_normal_monomial(key, variable_count)
        ]
        if normal_basis:
            result[block_charge] = normal_basis
    return result


def independent_charge_blocks(
    blocks: dict[Charge, list[MomentKey]],
) -> dict[Charge, list[MomentKey]]:
    """Drop charge blocks whose complex-conjugate PSD block is already kept."""
    return {
        block_charge: basis
        for block_charge, basis in blocks.items()
        if block_charge <= tuple(-value for value in block_charge)
    }


def reflection_phase(key: MomentKey, variable_count: int) -> complex:
    """Return 1 or i so a real scalar obeys reflection invariance."""
    if variable_count == STATE_VARIABLE_COUNT:
        return 1.0 + 0.0j
    _, anti, holo = key
    return 1.0j if (anti[0] + holo[0]) % 2 else 1.0 + 0.0j


@dataclass
class ReflectionMoments:
    variable: cp.Variable
    index: dict[MomentKey, int]
    phases: list[complex]

    def get(self, key: MomentKey) -> cp.Expression:
        conjugate = conjugate_key(key)
        canonical = min(key, conjugate)
        position = self.index[canonical]
        value = self.phases[position] * self.variable[position]
        return value if key == canonical else cp.conj(value)


def create_moments(
    name: str,
    variable_count: int,
    maximum_degree: int,
    charges: tuple[Charge, ...],
) -> ReflectionMoments:
    keys = normal_invariant_monomials(variable_count, maximum_degree, charges)
    canonical = sorted({min(key, conjugate_key(key)) for key in keys})
    index = {key: position for position, key in enumerate(canonical)}
    return ReflectionMoments(
        cp.Variable(len(canonical), name=name),
        index,
        [reflection_phase(key, variable_count) for key in canonical],
    )


def gram_entry(left: MomentKey, right: MomentKey) -> MomentKey:
    return (
        0,
        tuple(a + b for a, b in zip(left[2], right[1])),
        tuple(a + b for a, b in zip(left[1], right[2])),
    )


@dataclass
class PositiveConstraint:
    label: str
    support: Polynomial
    basis: list[MomentKey]
    face_transform: sparse.csr_matrix
    constraint: cp.constraints.psd.PSD


@dataclass
class LiouvilleConstraint:
    test: MomentKey
    derivative: Polynomial
    initial: complex
    target: complex
    constraint: cp.constraints.zero.Equality


def zero_cost_face_transform(basis: list[MomentKey]) -> sparse.csr_matrix:
    """Project an SOS block onto polynomials vanishing where the cost is zero.

    On ``r1 = r2 = 0``, every surviving basis monomial restricts to a Laurent
    character of the three unit phases ``(u, g1, g2)``.  A polynomial vanishes
    on that torus exactly when the coefficients of each equal character sum to
    zero.  The returned sparse columns span this exact kernel: Rydberg-
    containing monomials themselves, followed by an orthonormal Helmert basis
    for each group of monomials with the same nonzero restriction.
    """
    character_groups: dict[tuple[int, int, int], list[int]] = defaultdict(list)
    vanishing_indices: list[int] = []
    for index, (_, anti, holo) in enumerate(basis):
        if anti[R1] or holo[R1] or anti[R2] or holo[R2]:
            vanishing_indices.append(index)
            continue
        character_groups[
            (holo[0] - anti[0], holo[1] - anti[1], holo[3] - anti[3])
        ].append(index)

    rows: list[int] = []
    columns: list[int] = []
    data: list[float] = []
    column = 0
    for index in vanishing_indices:
        rows.append(index)
        columns.append(column)
        data.append(1.0)
        column += 1
    for indices in character_groups.values():
        for offset in range(1, len(indices)):
            normalization = math.sqrt(offset * (offset + 1))
            rows.extend(indices[:offset])
            columns.extend([column] * offset)
            data.extend([1.0 / normalization] * offset)
            rows.append(indices[offset])
            columns.append(column)
            data.append(-offset / normalization)
            column += 1
    return sparse.coo_matrix(
        (data, (rows, columns)), shape=(len(basis), column)
    ).tocsr()


def positive_blocks(
    moments: ReflectionMoments,
    basis_blocks: dict[Charge, list[MomentKey]],
    support: Polynomial,
    *,
    label: str,
    records: list[PositiveConstraint],
) -> list[cp.Constraint]:
    """Build torus-charge localizers through sparse moment selectors."""
    constraints: list[cp.Constraint] = []
    variable_size = moments.variable.size
    for basis in basis_blocks.values():
        size = len(basis)
        face_transform = zero_cost_face_transform(basis)
        if face_transform.shape[1] == 0:
            continue
        rows: list[int] = []
        columns: list[int] = []
        data: list[complex] = []
        for row, left in enumerate(basis):
            for column, right in enumerate(basis):
                matrix_entry = row + column * size
                base = gram_entry(left, right)
                for support_key, coefficient in support.items():
                    shifted = shift_key(base, support_key)
                    for key, normal_coefficient in normal_form(
                        shifted, variable_count=len(shifted[1])
                    ).items():
                        value = coefficient * normal_coefficient
                        conjugate = conjugate_key(key)
                        canonical = min(key, conjugate)
                        moment_column = moments.index[canonical]
                        phase = moments.phases[moment_column]
                        rows.append(matrix_entry)
                        columns.append(moment_column)
                        data.append(
                            value * (phase if key == canonical else phase.conjugate())
                        )
        shape = (size * size, variable_size)
        selector = sparse.coo_matrix((data, (rows, columns)), shape=shape).tocsr()
        vector = selector @ moments.variable
        matrix = cp.reshape(vector, (size, size), order="F")
        basis_phases = np.asarray(
            [reflection_phase(key, len(key[1])) for key in basis], dtype=complex
        )
        diagonal = sparse.diags(basis_phases)
        transformed = diagonal.conjugate() @ matrix @ diagonal
        real_matrix = cp.real(0.5 * (transformed + transformed.H))
        face_matrix = face_transform.T @ real_matrix @ face_transform
        constraint = face_matrix >> 0
        constraints.append(constraint)
        records.append(
            PositiveConstraint(label, support, basis, face_transform, constraint)
        )
    return constraints


def target_value(test: MomentKey) -> complex:
    """Evaluate an invariant test on the CZ orbit ``(1, 0, -1, 0)``."""
    _, anti, holo = test
    if anti[R1 - 1] or anti[R2 - 1] or holo[R1 - 1] or holo[R2 - 1]:
        return 0.0j
    g2_power = anti[G2 - 1] + holo[G2 - 1]
    return complex((-1) ** g2_power)


@dataclass
class Relaxation:
    order: int
    problem: cp.Problem
    occupation: ReflectionMoments
    liouville_constraint_count: int
    occupation_psd_block_sizes: list[int]
    occupation_positive: list[PositiveConstraint]
    liouville: list[LiouvilleConstraint]


def build_relaxation(order: int) -> Relaxation:
    if order < 2:
        raise ValueError("The torus relaxation order must be at least two")

    maximum_degree = 2 * order
    occupation = create_moments(
        "occupation_moments",
        BULK_VARIABLE_COUNT,
        maximum_degree,
        BULK_TORUS_CHARGES,
    )
    constraints: list[cp.Constraint] = []
    occupation_positive: list[PositiveConstraint] = []
    liouville: list[LiouvilleConstraint] = []

    occupation_blocks = independent_charge_blocks(
        normal_mixed_basis(BULK_VARIABLE_COUNT, order, BULK_TORUS_CHARGES)
    )
    constraints.extend(
        positive_blocks(
            occupation,
            occupation_blocks,
            unit_polynomial(BULK_VARIABLE_COUNT),
            label="occupation_moment_matrix",
            records=occupation_positive,
        )
    )

    tests = normal_invariant_monomials(
        STATE_VARIABLE_COUNT, maximum_degree - 1, STATE_TORUS_CHARGES
    )
    tests = [test for test in tests if test <= conjugate_key(test)]
    for test in tests:
        derivative = reduce_polynomial(
            liouville_derivative(test, 1.0), BULK_VARIABLE_COUNT
        )
        initial = initial_value(test)
        target = target_value(test)
        constraint = (
            cp.real(moment_expression(occupation, derivative))
            - target
            + initial
            == 0
        )
        constraints.append(constraint)
        liouville.append(
            LiouvilleConstraint(test, derivative, initial, target, constraint)
        )

    running_cost = {
        modulus_squared(BULK_VARIABLE_COUNT, R1): 0.5,
        modulus_squared(BULK_VARIABLE_COUNT, R2): 0.25,
    }
    objective = cp.real(moment_expression(occupation, running_cost))
    problem = cp.Problem(cp.Minimize(objective), constraints)
    return Relaxation(
        order,
        problem,
        occupation,
        len(tests),
        [record.face_transform.shape[1] for record in occupation_positive],
        occupation_positive,
        liouville,
    )


def solve_relaxation(
    relaxation: Relaxation, solver: str, verbose: bool
) -> dict[str, object]:
    solver = solver.upper()
    if solver not in cp.installed_solvers():
        raise SystemExit(
            f"Solver {solver} is unavailable; installed solvers: {cp.installed_solvers()}"
        )
    options: dict[str, object] = {"solver": solver, "verbose": verbose}
    if solver == "SCS":
        options.update(eps=2e-6, max_iters=200_000)
    elif solver == "CLARABEL":
        options.update(
            tol_gap_abs=1e-8,
            tol_gap_rel=1e-8,
            tol_feas=1e-8,
            max_iter=500,
        )
    relaxation.problem.solve(**options)
    if relaxation.problem.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE):
        raise RuntimeError(f"SDP solve failed with status {relaxation.problem.status}")
    return {
        "model": "JAN22 ideal-blockade two-qubit CZ exposure",
        "interpretation": (
            "Floating-point unrestricted-duration U(1)xU(1)-blocked full real "
            "moment/SOS discovery result; exactification is required."
        ),
        "order": relaxation.order,
        "maximum_moment_degree": 2 * relaxation.order,
        "duration_scope": "unrestricted finite duration",
        "symmetry": "laser-phase U(1) x one-qubit-phase U(1)",
        "target": "exact torus-quotient point represented by (g1,r1,g2,r2)=(1,0,-1,0)",
        "sos_basis": "all time-independent mixed monomials (full real SOS)",
        "control_support": "|u| = 1 by exact active-time reparameterization",
        "solver": solver,
        "status": relaxation.problem.status,
        "objective": float(relaxation.problem.value),
        "solver_statistics": {
            "iterations": relaxation.problem.solver_stats.num_iters,
            "setup_time_seconds": relaxation.problem.solver_stats.setup_time,
            "solve_time_seconds": relaxation.problem.solver_stats.solve_time,
        },
        "occupation_complex_moment_variable_count": relaxation.occupation.variable.size,
        "liouville_constraint_count": relaxation.liouville_constraint_count,
        "occupation_psd_block_sizes": sorted(
            relaxation.occupation_psd_block_sizes, reverse=True
        ),
    }


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=3)
    parser.add_argument(
        "--solver", default="CLARABEL", choices=("CLARABEL", "MOSEK", "SCS")
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    arguments = parse_arguments()
    relaxation = build_relaxation(arguments.order)
    result = solve_relaxation(relaxation, arguments.solver, arguments.verbose)
    encoded = json.dumps(result, indent=2)
    if arguments.output is not None:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)


if __name__ == "__main__":
    main()
