"""Solve a U(1)-reduced complex moment relaxation for JAN22 CZ exposure.

The ideal-blockade dynamics are polynomial in the complex amplitudes and their
conjugates.  They are equivariant under the continuous symmetry

    u -> exp(i theta) u,    r_k -> exp(-i theta) r_k,

with the ground amplitudes unchanged.  Averaging any feasible occupation
measure over this symmetry preserves its cost, initial point, and CZ target.
In a holomorphic complex moment hierarchy, the moment and localizing matrices
therefore split exactly into U(1)-charge blocks.  This is a much stronger size
reduction than retaining only the order-two subgroup (parity).

Every finite relaxation remains a lower bound; a floating solver result is
still only certificate-discovery data until its dual Hermitian Gram matrices
are rationalized or interval-enclosed.  Run a regression level with::

    .venv/bin/python -m verification.jan22_cz_exposure_complex_moment_sdp \
        --order 2 --horizon 30 --solver CLARABEL

The complex hierarchy follows the Hermitian moment/SOS construction of Josz
and Molzahn (SIAM J. Optim. 28, 1017-1048, 2018).  Holomorphic monomials index
the PSD matrices; their entries are mixed monomials ``conj(z)**alpha *
z**beta``.  Time is a separate real variable.

The relaxation also uses the exact bang-or-wait reduction.  Reparameterizing
any interval with ``0 < abs(u) < 1`` to unit amplitude follows the same state
path faster and never increases exposure.  The saved duration can be padded
at the zero-cost closed target with ``u = 0``.  Hence the optimum over pulses
of duration at most the horizon is unchanged after imposing the polynomial
support ``abs(u)**2 * (1 - abs(u)**2) = 0``.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

try:
    import cvxpy as cp
except ImportError as error:  # pragma: no cover - dependency guidance
    raise SystemExit("Install the verifier dependency: pip install cvxpy") from error


Exponent = tuple[int, ...]
MomentKey = tuple[int, Exponent, Exponent]
Polynomial = dict[MomentKey, complex]
BasisMonomial = tuple[int, Exponent]

# Bulk holomorphic variables are (u, g1, r1, g2, r2).  Under the laser-phase
# symmetry they have charges (+1, 0, -1, 0, -1).
U, G1, R1, G2, R2 = range(5)
BULK_VARIABLE_COUNT = 5
BULK_CHARGES = (1, 0, -1, 0, -1)

# Terminal variables omit the control: (g1, r1, g2, r2).
TG1, TR1, TG2, TR2 = range(4)
TERMINAL_VARIABLE_COUNT = 4
TERMINAL_CHARGES = (0, -1, 0, -1)

# Liouville tests use the same four state variables as the terminal measure.
STATE_VARIABLE_COUNT = TERMINAL_VARIABLE_COUNT
STATE_CHARGES = TERMINAL_CHARGES


def monomials(variable_count: int, maximum_degree: int) -> list[Exponent]:
    """Return all exponent tuples of total degree at most ``maximum_degree``."""
    if maximum_degree < 0:
        return []
    result: list[Exponent] = []

    def append_degree(prefix: list[int], variables_left: int, degree_left: int) -> None:
        if variables_left == 1:
            result.append(tuple(prefix + [degree_left]))
            return
        for exponent in range(degree_left + 1):
            append_degree(
                prefix + [exponent], variables_left - 1, degree_left - exponent
            )

    for total_degree in range(maximum_degree + 1):
        append_degree([], variable_count, total_degree)
    return result


def zero_exponent(variable_count: int) -> Exponent:
    return (0,) * variable_count


def add_exponents(left: Exponent, right: Exponent) -> Exponent:
    return tuple(a + b for a, b in zip(left, right))


def exponent_with(variable_count: int, variable: int, power: int = 1) -> Exponent:
    exponent = [0] * variable_count
    exponent[variable] = power
    return tuple(exponent)


def charge(exponent: Exponent, charges: tuple[int, ...]) -> int:
    return sum(power * weight for power, weight in zip(exponent, charges))


def conjugate_key(key: MomentKey) -> MomentKey:
    time_power, anti, holo = key
    return time_power, holo, anti


def invariant_mixed_monomials(
    variable_count: int, maximum_degree: int, charges: tuple[int, ...]
) -> list[MomentKey]:
    """Return ``t^p conj(z)^a z^b`` monomials with total U(1) charge zero."""
    through_degree = [monomials(variable_count, degree) for degree in range(maximum_degree + 1)]
    result: list[MomentKey] = []
    for time_power in range(maximum_degree + 1):
        remaining_after_time = maximum_degree - time_power
        for anti in through_degree[remaining_after_time]:
            remaining = remaining_after_time - sum(anti)
            anti_charge = charge(anti, charges)
            for holo in through_degree[remaining]:
                if charge(holo, charges) == anti_charge:
                    result.append((time_power, anti, holo))
    return result


def holomorphic_basis(
    variable_count: int, maximum_degree: int, charges: tuple[int, ...]
) -> dict[int, list[BasisMonomial]]:
    """Group ``t^p z^alpha`` by U(1) charge."""
    blocks: dict[int, list[BasisMonomial]] = defaultdict(list)
    for time_power in range(maximum_degree + 1):
        for exponent in monomials(variable_count, maximum_degree - time_power):
            blocks[charge(exponent, charges)].append((time_power, exponent))
    return dict(blocks)


@dataclass
class HermitianMoments:
    variable: cp.Variable
    index: dict[MomentKey, int]
    self_conjugate_indices: list[int]

    @classmethod
    def create(
        cls,
        name: str,
        variable_count: int,
        maximum_degree: int,
        charges: tuple[int, ...],
    ) -> HermitianMoments:
        keys = invariant_mixed_monomials(variable_count, maximum_degree, charges)
        canonical_keys = sorted({min(key, conjugate_key(key)) for key in keys})
        index = {key: position for position, key in enumerate(canonical_keys)}
        self_conjugate = [
            position
            for key, position in index.items()
            if key == conjugate_key(key)
        ]
        return cls(cp.Variable(len(canonical_keys), complex=True, name=name), index, self_conjugate)

    def get(self, key: MomentKey) -> cp.Expression:
        conjugate = conjugate_key(key)
        canonical = min(key, conjugate)
        value = self.variable[self.index[canonical]]
        return value if key == canonical else cp.conj(value)

    def hermitian_constraints(self) -> list[cp.Constraint]:
        if not self.self_conjugate_indices:
            return []
        return [cp.imag(self.variable[self.self_conjugate_indices]) == 0]


def add_polynomial_term(
    polynomial: Polynomial, key: MomentKey, coefficient: complex
) -> None:
    value = polynomial.get(key, 0.0j) + complex(coefficient)
    if value == 0.0j:
        polynomial.pop(key, None)
    else:
        polynomial[key] = value


def moment_expression(
    moments: HermitianMoments, polynomial: Polynomial
) -> cp.Expression:
    return sum(
        (coefficient * moments.get(key) for key, coefficient in polynomial.items()),
        cp.Constant(0.0j),
    )


def shift_key(key: MomentKey, shift: MomentKey) -> MomentKey:
    return (
        key[0] + shift[0],
        add_exponents(key[1], shift[1]),
        add_exponents(key[2], shift[2]),
    )


def shifted_polynomial(polynomial: Polynomial, multiplier: MomentKey) -> Polynomial:
    return {shift_key(key, multiplier): coefficient for key, coefficient in polynomial.items()}


def positive_blocks(
    moments: HermitianMoments,
    variable_count: int,
    charges: tuple[int, ...],
    basis_degree: int,
    support: Polynomial,
) -> list[cp.Constraint]:
    constraints: list[cp.Constraint] = []
    for basis in holomorphic_basis(variable_count, basis_degree, charges).values():
        rows: list[list[cp.Expression]] = []
        for left_time, left_exponent in basis:
            row: list[cp.Expression] = []
            for right_time, right_exponent in basis:
                base = (left_time + right_time, left_exponent, right_exponent)
                entry = sum(
                    (
                        coefficient * moments.get(shift_key(base, support_key))
                        for support_key, coefficient in support.items()
                    ),
                    cp.Constant(0.0j),
                )
                row.append(entry)
            rows.append(row)
        matrix = cp.bmat(rows)
        constraints.append(0.5 * (matrix + matrix.H) >> 0)
    return constraints


def unit_polynomial(variable_count: int) -> Polynomial:
    zero = zero_exponent(variable_count)
    return {(0, zero, zero): 1.0}


def time_support(variable_count: int) -> Polynomial:
    zero = zero_exponent(variable_count)
    return {(1, zero, zero): 1.0, (2, zero, zero): -1.0}


def modulus_squared(variable_count: int, variable: int) -> MomentKey:
    exponent = exponent_with(variable_count, variable)
    return 0, exponent, exponent


def control_disk_support() -> Polynomial:
    zero = zero_exponent(BULK_VARIABLE_COUNT)
    return {
        (0, zero, zero): 1.0,
        modulus_squared(BULK_VARIABLE_COUNT, U): -1.0,
    }


def bang_or_wait_polynomial() -> Polynomial:
    """Return ``|u|^2 (1-|u|^2)``, vanishing at amplitudes zero and one."""
    control_squared = exponent_with(BULK_VARIABLE_COUNT, U)
    control_fourth = exponent_with(BULK_VARIABLE_COUNT, U, 2)
    return {
        (0, control_squared, control_squared): 1.0,
        (0, control_fourth, control_fourth): -1.0,
    }


def sphere_polynomial(
    variable_count: int, ground: int, rydberg: int
) -> Polynomial:
    zero = zero_exponent(variable_count)
    return {
        (0, zero, zero): 1.0,
        modulus_squared(variable_count, ground): -1.0,
        modulus_squared(variable_count, rydberg): -1.0,
    }


def terminal_closure_polynomial(variable: int) -> Polynomial:
    return {modulus_squared(TERMINAL_VARIABLE_COUNT, variable): 1.0}


def terminal_cz_polynomial() -> Polynomial:
    """Return the neutral complex target equality ``g2 + g1**2 = 0``."""
    zero = zero_exponent(TERMINAL_VARIABLE_COUNT)
    g2 = exponent_with(TERMINAL_VARIABLE_COUNT, TG2)
    g1_squared = exponent_with(TERMINAL_VARIABLE_COUNT, TG1, 2)
    return {
        (0, zero, g2): 1.0,
        (0, zero, g1_squared): 1.0,
    }


def add_ideal_constraints(
    constraints: list[cp.Constraint],
    moments: HermitianMoments,
    polynomial: Polynomial,
    variable_count: int,
    charges: tuple[int, ...],
    maximum_degree: int,
    *,
    hermitian: bool,
) -> int:
    polynomial_degree = max(
        time + sum(anti) + sum(holo) for time, anti, holo in polynomial
    )
    multipliers = invariant_mixed_monomials(
        variable_count, maximum_degree - polynomial_degree, charges
    )
    if hermitian:
        multipliers = [
            multiplier
            for multiplier in multipliers
            if multiplier <= conjugate_key(multiplier)
        ]
    for multiplier in multipliers:
        constraints.append(
            moment_expression(moments, shifted_polynomial(polynomial, multiplier)) == 0
        )
    return len(multipliers)


def embed_state_key(key: MomentKey) -> MomentKey:
    time_power, anti_state, holo_state = key
    anti_bulk = (0, *anti_state)
    holo_bulk = (0, *holo_state)
    return time_power, anti_bulk, holo_bulk


def liouville_derivative(test: MomentKey, horizon: float) -> Polynomial:
    """Differentiate an invariant mixed state monomial along the exact ODE."""
    time_power, anti, holo = test
    derivative: Polynomial = {}
    if time_power:
        reduced = (time_power - 1, anti, holo)
        add_polynomial_term(derivative, embed_state_key(reduced), time_power)

    # State order is (g1, r1, g2, r2); bulk order inserts control first.
    for ground, rydberg, kappa in (
        (TG1, TR1, 0.5),
        (TG2, TR2, 1.0 / math.sqrt(2.0)),
    ):
        # d g / ds = -i kappa u r
        if holo[ground]:
            reduced_holo = list(holo)
            reduced_holo[ground] -= 1
            base = embed_state_key((time_power, anti, tuple(reduced_holo)))
            shift_holo = [0] * BULK_VARIABLE_COUNT
            shift_holo[U] = 1
            shift_holo[1 + rydberg] = 1
            shift = (0, zero_exponent(BULK_VARIABLE_COUNT), tuple(shift_holo))
            add_polynomial_term(
                derivative,
                shift_key(base, shift),
                -1j * horizon * kappa * holo[ground],
            )

        # d r / ds = -i kappa conj(u) g
        if holo[rydberg]:
            reduced_holo = list(holo)
            reduced_holo[rydberg] -= 1
            base = embed_state_key((time_power, anti, tuple(reduced_holo)))
            shift_anti = exponent_with(BULK_VARIABLE_COUNT, U)
            shift_holo = exponent_with(BULK_VARIABLE_COUNT, 1 + ground)
            add_polynomial_term(
                derivative,
                shift_key(base, (0, shift_anti, shift_holo)),
                -1j * horizon * kappa * holo[rydberg],
            )

        # Conjugate equations.
        if anti[ground]:
            reduced_anti = list(anti)
            reduced_anti[ground] -= 1
            base = embed_state_key((time_power, tuple(reduced_anti), holo))
            shift_anti = [0] * BULK_VARIABLE_COUNT
            shift_anti[U] = 1
            shift_anti[1 + rydberg] = 1
            add_polynomial_term(
                derivative,
                shift_key(
                    base,
                    (
                        0,
                        tuple(shift_anti),
                        zero_exponent(BULK_VARIABLE_COUNT),
                    ),
                ),
                1j * horizon * kappa * anti[ground],
            )

        if anti[rydberg]:
            reduced_anti = list(anti)
            reduced_anti[rydberg] -= 1
            base = embed_state_key((time_power, tuple(reduced_anti), holo))
            shift_anti = exponent_with(BULK_VARIABLE_COUNT, 1 + ground)
            shift_holo = exponent_with(BULK_VARIABLE_COUNT, U)
            add_polynomial_term(
                derivative,
                shift_key(base, (0, shift_anti, shift_holo)),
                1j * horizon * kappa * anti[rydberg],
            )
    return derivative


def initial_value(test: MomentKey) -> complex:
    time_power, anti, holo = test
    if time_power or anti[TR1] or anti[TR2] or holo[TR1] or holo[TR2]:
        return 0.0j
    return 1.0 + 0.0j


@dataclass
class Relaxation:
    order: int
    horizon: float
    problem: cp.Problem
    occupation: HermitianMoments
    terminal: HermitianMoments
    liouville_constraint_count: int
    occupation_ideal_constraint_count: int
    terminal_ideal_constraint_count: int
    occupation_psd_block_sizes: list[int]
    terminal_psd_block_sizes: list[int]


def build_relaxation(order: int, horizon: float) -> Relaxation:
    if order < 1:
        raise ValueError("The relaxation order must be at least one")
    if horizon <= 0.0:
        raise ValueError("The horizon must be positive")

    maximum_degree = 2 * order
    occupation = HermitianMoments.create(
        "occupation_moments",
        BULK_VARIABLE_COUNT,
        maximum_degree,
        BULK_CHARGES,
    )
    terminal = HermitianMoments.create(
        "terminal_moments",
        TERMINAL_VARIABLE_COUNT,
        maximum_degree,
        TERMINAL_CHARGES,
    )
    constraints = [
        *occupation.hermitian_constraints(),
        *terminal.hermitian_constraints(),
    ]

    occupation_blocks = holomorphic_basis(
        BULK_VARIABLE_COUNT, order, BULK_CHARGES
    )
    terminal_blocks = holomorphic_basis(
        TERMINAL_VARIABLE_COUNT, order, TERMINAL_CHARGES
    )
    constraints.extend(
        positive_blocks(
            occupation,
            BULK_VARIABLE_COUNT,
            BULK_CHARGES,
            order,
            unit_polynomial(BULK_VARIABLE_COUNT),
        )
    )
    constraints.extend(
        positive_blocks(
            terminal,
            TERMINAL_VARIABLE_COUNT,
            TERMINAL_CHARGES,
            order,
            unit_polynomial(TERMINAL_VARIABLE_COUNT),
        )
    )
    constraints.extend(
        positive_blocks(
            occupation,
            BULK_VARIABLE_COUNT,
            BULK_CHARGES,
            order - 1,
            time_support(BULK_VARIABLE_COUNT),
        )
    )
    constraints.extend(
        positive_blocks(
            occupation,
            BULK_VARIABLE_COUNT,
            BULK_CHARGES,
            order - 1,
            control_disk_support(),
        )
    )

    occupation_ideal_count = 0
    for ground, rydberg in ((G1, R1), (G2, R2)):
        occupation_ideal_count += add_ideal_constraints(
            constraints,
            occupation,
            sphere_polynomial(BULK_VARIABLE_COUNT, ground, rydberg),
            BULK_VARIABLE_COUNT,
            BULK_CHARGES,
            maximum_degree,
            hermitian=True,
        )
    if order >= 2:
        occupation_ideal_count += add_ideal_constraints(
            constraints,
            occupation,
            bang_or_wait_polynomial(),
            BULK_VARIABLE_COUNT,
            BULK_CHARGES,
            maximum_degree,
            hermitian=True,
        )

    terminal_ideal_count = 0
    for ground, rydberg in ((TG1, TR1), (TG2, TR2)):
        terminal_ideal_count += add_ideal_constraints(
            constraints,
            terminal,
            sphere_polynomial(TERMINAL_VARIABLE_COUNT, ground, rydberg),
            TERMINAL_VARIABLE_COUNT,
            TERMINAL_CHARGES,
            maximum_degree,
            hermitian=True,
        )
    for rydberg in (TR1, TR2):
        terminal_ideal_count += add_ideal_constraints(
            constraints,
            terminal,
            terminal_closure_polynomial(rydberg),
            TERMINAL_VARIABLE_COUNT,
            TERMINAL_CHARGES,
            maximum_degree,
            hermitian=True,
        )
    terminal_ideal_count += add_ideal_constraints(
        constraints,
        terminal,
        terminal_cz_polynomial(),
        TERMINAL_VARIABLE_COUNT,
        TERMINAL_CHARGES,
        maximum_degree,
        hermitian=False,
    )

    liouville_count = 0
    tests = invariant_mixed_monomials(
        STATE_VARIABLE_COUNT, maximum_degree - 1, STATE_CHARGES
    )
    tests = [test for test in tests if test <= conjugate_key(test)]
    for test in tests:
        terminal_key = (0, test[1], test[2])
        constraints.append(
            moment_expression(occupation, liouville_derivative(test, horizon))
            - terminal.get(terminal_key)
            + initial_value(test)
            == 0
        )
        liouville_count += 1

    running_cost = {
        modulus_squared(BULK_VARIABLE_COUNT, R1): 0.5 * horizon,
        modulus_squared(BULK_VARIABLE_COUNT, R2): 0.25 * horizon,
    }
    objective = cp.real(moment_expression(occupation, running_cost))
    problem = cp.Problem(cp.Minimize(objective), constraints)
    return Relaxation(
        order,
        horizon,
        problem,
        occupation,
        terminal,
        liouville_count,
        occupation_ideal_count,
        terminal_ideal_count,
        [len(block) for block in occupation_blocks.values()],
        [len(block) for block in terminal_blocks.values()],
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
            "Floating-point U(1)-reduced complex moment/SOS discovery result; "
            "dual exactification is required before this is a theorem."
        ),
        "order": relaxation.order,
        "maximum_moment_degree": 2 * relaxation.order,
        "horizon": relaxation.horizon,
        "symmetry": "continuous U(1) laser-phase symmetry",
        "control_support": "|u| in {0, 1} by exact bang-or-wait reduction",
        "solver": solver,
        "status": relaxation.problem.status,
        "objective": float(relaxation.problem.value),
        "solver_statistics": {
            "iterations": relaxation.problem.solver_stats.num_iters,
            "setup_time_seconds": relaxation.problem.solver_stats.setup_time,
            "solve_time_seconds": relaxation.problem.solver_stats.solve_time,
        },
        "occupation_complex_moment_variable_count": relaxation.occupation.variable.size,
        "terminal_complex_moment_variable_count": relaxation.terminal.variable.size,
        "liouville_constraint_count": relaxation.liouville_constraint_count,
        "occupation_ideal_constraint_count": relaxation.occupation_ideal_constraint_count,
        "terminal_ideal_constraint_count": relaxation.terminal_ideal_constraint_count,
        "occupation_psd_block_sizes": sorted(
            relaxation.occupation_psd_block_sizes, reverse=True
        ),
        "terminal_psd_block_sizes": sorted(
            relaxation.terminal_psd_block_sizes, reverse=True
        ),
    }


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=2)
    parser.add_argument("--horizon", type=float, default=30.0)
    parser.add_argument("--solver", default="CLARABEL", choices=("CLARABEL", "SCS"))
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    arguments = parse_arguments()
    relaxation = build_relaxation(arguments.order, arguments.horizon)
    result = solve_relaxation(relaxation, arguments.solver, arguments.verbose)
    encoded = json.dumps(result, indent=2)
    if arguments.output is not None:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)


if __name__ == "__main__":
    main()
