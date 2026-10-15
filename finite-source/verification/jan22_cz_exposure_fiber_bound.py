"""Audit and enclose the exact-fiber JAN22 CZ exposure lower bound.

The analytical proof is in ``docs/explanation/13-jan22-cz-exposure-bound.md``.
In the ideal-blockade model it sharpens the companion-overlap constraint by
retaining both instantaneous Rydberg populations.  The resulting exact
constant is a one-dimensional integral whose numerical value is about
2.480079367707.

This script performs two independent calculations:

1. adaptive floating-point quadrature estimates the constant; and
2. Arb ball arithmetic constructs a lower Riemann sum proving that the
   constant is strictly greater than 2.48007.

The second calculation uses only monotonicity proved in the accompanying
derivation; GRAPE data and pulse candidates do not enter.  Run from the
repository root with python-flint available, for example::

    PYTHONPATH=/tmp/jan22-tight-deps \
        python verification/jan22_cz_exposure_fiber_bound.py
"""

from __future__ import annotations

import heapq
import json
import math
import time

from flint import arb, ctx


SQRT2 = math.sqrt(2.0)
T_MAX = 1.0e3
RIEMANN_ERROR_TARGET = 1.0e-5


def floating_fiber_point(t: float) -> tuple[float, float]:
    """Return overlap radius and cost weight on the minimizing branch."""
    k = 1.0 + t**4
    a = 4.0 * k**4 - 2.0 * k**2 - 2.0 * k
    q = 8.0 * k**4 - 12.0 * k**3 + 4.0 * k**2 + 4.0 * k - 4.0
    b = (a + math.sqrt(a * a + 4.0 * k**3 * q)) / (2.0 * k**3)
    root = math.sqrt(1.0 + k**2 * b)
    radius = 2.0 * (1.0 + k * b) / ((b + 2.0) * root)
    weight = SQRT2 / 4.0 * (
        2.0 * root / (k * math.sqrt(b))
        + k * math.sqrt(b) * (b + 2.0) / (b * root)
    )
    return radius, weight


def transformed_integrand(t: float) -> float:
    """Return ``-2*c(k)*dq/dk*dk/dt`` for ``k=1+t**4``."""
    if t < 1.0e-4:
        # The integrand is 6.72717...*t^2+O(t^3); this branch avoids loss of
        # significance when 1+t^4 rounds to 1 in binary64.
        return 6.72717132203 * t * t

    k = 1.0 + t**4
    a = 4.0 * k**4 - 2.0 * k**2 - 2.0 * k
    a_prime = 16.0 * k**3 - 4.0 * k - 2.0
    q = 8.0 * k**4 - 12.0 * k**3 + 4.0 * k**2 + 4.0 * k - 4.0
    q_prime = 32.0 * k**3 - 36.0 * k**2 + 8.0 * k + 4.0
    discriminant = a * a + 4.0 * k**3 * q
    root_discriminant = math.sqrt(discriminant)
    discriminant_prime = (
        2.0 * a * a_prime + 12.0 * k**2 * q + 4.0 * k**3 * q_prime
    )
    b = (a + root_discriminant) / (2.0 * k**3)
    b_prime = (
        (a_prime + discriminant_prime / (2.0 * root_discriminant))
        / (2.0 * k**3)
        - 3.0 * b / k
    )

    numerator = 1.0 + k * b
    denominator = b + 2.0
    square = 1.0 + k**2 * b
    radius = 2.0 * numerator / (denominator * math.sqrt(square))
    radius_prime = radius * (
        (b + k * b_prime) / numerator
        - b_prime / denominator
        - (2.0 * k * b + k**2 * b_prime) / (2.0 * square)
    )
    weight = SQRT2 / 4.0 * (
        2.0 * math.sqrt(square) / (k * math.sqrt(b))
        + k
        * math.sqrt(b)
        * denominator
        / (b * math.sqrt(square))
    )
    return -8.0 * t**3 * weight * radius_prime


def adaptive_simpson(
    left: float, right: float, tolerance: float = 1.0e-12, depth: int = 30
) -> float:
    def simpson(a: float, b: float, fa: float, fm: float, fb: float) -> float:
        return (b - a) * (fa + 4.0 * fm + fb) / 6.0

    midpoint = (left + right) / 2.0
    f_left = transformed_integrand(left)
    f_mid = transformed_integrand(midpoint)
    f_right = transformed_integrand(right)
    whole = simpson(left, right, f_left, f_mid, f_right)

    def recurse(
        a: float,
        b: float,
        fa: float,
        fm: float,
        fb: float,
        estimate: float,
        tol: float,
        remaining: int,
    ) -> float:
        m = (a + b) / 2.0
        left_midpoint = (a + m) / 2.0
        right_midpoint = (m + b) / 2.0
        f_left_midpoint = transformed_integrand(left_midpoint)
        f_right_midpoint = transformed_integrand(right_midpoint)
        left_estimate = simpson(a, m, fa, f_left_midpoint, fm)
        right_estimate = simpson(m, b, fm, f_right_midpoint, fb)
        correction = left_estimate + right_estimate - estimate
        if remaining == 0 or abs(correction) <= 15.0 * tol:
            return left_estimate + right_estimate + correction / 15.0
        return recurse(
            a,
            m,
            fa,
            f_left_midpoint,
            fm,
            left_estimate,
            tol / 2.0,
            remaining - 1,
        ) + recurse(
            m,
            b,
            fm,
            f_right_midpoint,
            fb,
            right_estimate,
            tol / 2.0,
            remaining - 1,
        )

    return recurse(
        left,
        right,
        f_left,
        f_mid,
        f_right,
        whole,
        tolerance,
        depth,
    )


def estimate_constant() -> float:
    split_points = (
        0.0,
        0.001,
        0.01,
        0.1,
        0.3,
        1.0,
        3.0,
        10.0,
        30.0,
        100.0,
        300.0,
        T_MAX,
    )
    finite_part = sum(
        adaptive_simpson(left, right)
        for left, right in zip(split_points[:-1], split_points[1:])
    )
    # The transformed tail is 3*sqrt(2)/t^3+O(t^-7).
    leading_tail = 3.0 * SQRT2 / (2.0 * T_MAX**2)
    return finite_part + leading_tail


def arb_fiber_point(t_value: float) -> tuple[arb, arb]:
    """Outward-rounded version of ``floating_fiber_point``."""
    t = arb(repr(t_value))
    k = 1 + t**4
    a = 4 * k**4 - 2 * k**2 - 2 * k
    q = 8 * k**4 - 12 * k**3 + 4 * k**2 + 4 * k - 4
    b = (a + (a**2 + 4 * k**3 * q).sqrt()) / (2 * k**3)
    root = (1 + k**2 * b).sqrt()
    radius = 2 * (1 + k * b) / ((b + 2) * root)
    weight = arb(2).sqrt() / 4 * (
        2 * root / (k * b.sqrt())
        + k * b.sqrt() * (b + 2) / (b * root)
    )
    return radius, weight


def adaptive_partition() -> tuple[list[tuple[float, float]], float]:
    """Choose a partition whose monotone upper/lower-sum gap is small."""
    initial_points = [10.0 ** (-3.0 + index * 6.0 / 20.0) for index in range(21)]
    heap: list[tuple[float, int, float, float]] = []
    total_error = 0.0
    serial = 0

    def push(left: float, right: float) -> None:
        nonlocal serial, total_error
        radius_left, weight_left = floating_fiber_point(left)
        radius_right, weight_right = floating_fiber_point(right)
        error = 2.0 * (weight_left - weight_right) * (
            radius_left - radius_right
        )
        serial += 1
        heapq.heappush(heap, (-error, serial, left, right))
        total_error += error

    for left, right in zip(initial_points[:-1], initial_points[1:]):
        push(left, right)

    while total_error > RIEMANN_ERROR_TARGET:
        negative_error, _, left, right = heapq.heappop(heap)
        total_error += negative_error
        midpoint = math.sqrt(left * right)
        push(left, midpoint)
        push(midpoint, right)

    return sorted((left, right) for _, _, left, right in heap), total_error


def certified_lower_sum() -> tuple[arb, int, float]:
    segments, floating_error = adaptive_partition()
    points = [segments[0][0], *(right for _, right in segments)]
    values = [arb_fiber_point(point) for point in points]

    total = arb(0)
    for (radius_left, _), (radius_right, weight_right) in zip(
        values[:-1], values[1:]
    ):
        width_lower = radius_left.lower() - radius_right.upper()
        assert float(width_lower) > 0.0
        total += 2 * weight_right.lower() * width_lower

    # The omitted interval 0 <= radius <= radius(T_MAX) is bounded below by
    # c_fib(0)=3*sqrt(2)/4.  Omitting the tiny positive k->1 endpoint interval
    # is also conservative.
    radius_tail = values[-1][0]
    minimum_weight = 3 * arb(2).sqrt() / 4
    total += 2 * minimum_weight.lower() * radius_tail.lower()
    return total, len(segments), floating_error


def main() -> None:
    estimate = estimate_constant()
    ctx.prec = 160
    started = time.time()
    lower_ball, segment_count, partition_error = certified_lower_sum()
    elapsed = time.time() - started

    assert abs(estimate - 2.480079367706997) < 3.0e-12
    assert lower_ball > arb("2.48007")
    result = {
        "analytical_constant_estimate": estimate,
        "certified_strict_lower_bound": "2.48007",
        "arb_lower_riemann_sum": str(lower_ball),
        "partition_segments": segment_count,
        "floating_partition_gap_target": RIEMANN_ERROR_TARGET,
        "floating_partition_gap": partition_error,
        "arb_seconds": elapsed,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
