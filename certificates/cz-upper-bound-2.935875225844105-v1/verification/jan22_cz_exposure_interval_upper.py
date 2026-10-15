"""Certify existence of an exact CZ pulse with exposure below 2.935875225844105.

This is a computer-assisted *upper*-bound proof, not a lower-bound proof.  It
fixes 12668 phases from ``jan22_cz_exposure_candidate_12672.json`` and treats four
phases plus the duration as variables.  A Krawczyk interval test proves that
the five exact terminal equations have a unique zero in the stated box.  The
same interval evaluation proves that this zero is on the CZ branch and has
exposure below 2.935875225844105.

The verifier needs python-flint's Arb ball arithmetic::

    python -m pip install python-flint
    python verification/jan22_cz_exposure_interval_upper.py
"""

from __future__ import annotations

import json
from pathlib import Path

try:
    from flint import arb, arb_mat, ctx
except ImportError as error:  # pragma: no cover - dependency guidance
    raise SystemExit("Install the optional verifier dependency: pip install python-flint") from error


ctx.prec = 500
DATA = Path(__file__).with_name("reference_data") / "jan22_cz_exposure_candidate_12672.json"
VARIABLE_PHASE_INDICES = (731, 6676, 8661, 11922)
BOX_RADIUS = "1e-80"
CERTIFIED_UPPER_BOUND = "2.935875225844105"
CENTERS = (
    "7.73911618791310642696251620521391327817111195210418750857966561746578970214927226032602390107753046704116504811379080553931655917487641",
    "-0.80928220506326028680913028875727472056044340184098708521850764158055654985261319550735265998071492418375666626738408800786426811149149",
    "-0.883750491057239166079521597996801876458055301555720246358775332335440669507855169685686362797738619872508518683937529825852908005918129",
    "-0.374570893842111021637229698327083799068788308556135385552953843306907625692668588206227784935104443877131385140258011449732383305195693",
    "-1.26804935800289181501180021686093112979596254394026587150459738347654822235904987198131173186300950502594183122250279623015525794549197",
)

# A numerical inverse of the terminal Jacobian at CENTERS.  It need not be
# exact: every occurrence below is enclosed by Arb, and the Krawczyk inclusion
# itself is the proof.
APPROXIMATE_INVERSE = (
    (
        "-1.55151947725549553107938173192120774876343005431415953448365301224283464832832042625417069",
        "0.975423678562738440693400912360962410830497295868794925367184405287502649647471541444892736",
        "1.61108455866370647562744093911139164820650674706281750740106955607014981273185040707415323",
        "-0.932532353800425379238821047805430475080529662907951140211936619910060743170345298301134403",
        "-0.475377754211951791820886689452331894787936598146125974676173484621939604308935321915774749",
    ),
    (
        "1961.19666935727026733663914941190582577800026911453341055627201519516265712629847670000371",
        "1358.72845237175918114106509045182462182952964692795775169137171944935258794067052216870152",
        "69.5190548910504715714601594264768933147565695788211063498989424014896801895724230285101439",
        "-1569.37464290710553481951161616721061506617759849472962623037208269111248818207438119940195",
        "-659.56127168207674287486223221709480288251553408384675149667940539440819497506614892544272",
    ),
    (
        "-1105.17311658843809869425018451778710840137654733905494322069861013474121426615844841762215",
        "-1965.93951032720284862470173177767421693460970943215761873026696924197565355902825747264173",
        "-399.217799804069430430644823995604358591210182311026972851220842149585041795410650132192731",
        "-597.833487958739967005425823547350535411217096396602583554503774184887263365386372264807106",
        "375.92692917347280688892972619551678473995783930843545720913212154853628062904583003132973",
    ),
    (
        "567.913733734545104636647953582588072304322408802066048691092598744357302323054488013250882",
        "410.123463408033372321540047586570120063469207465695805065752161198757508618475964017927099",
        "-76.3110334552757508837028817454224303259560813468857878981544383057428534978866665171367133",
        "285.855857983448230537487235696380919209059695259042905085424207907892756777107508004011943",
        "2297.34747399255928339272617854618984378100963887021629896462338377469371480129522842579012",
    ),
    (
        "324.279449012539323850043331209574074741451579871830193077649465527985883929802424812239915",
        "2233.83225783402546298633245325981793255008373915198186142365216636100263773300793426449112",
        "-1522.35037516564885077608068140456168289320134785456712003210297524821364415964582334101421",
        "-664.500981503414138024987234975645414748796675469126119375090693416859609843806342196505252",
        "2086.13118818372612927446471622456869472225050556596986723491200444134888740796041776402166",
    ),
)


class Dual:
    """Real Arb ball carrying derivatives with respect to five variables."""

    def __init__(self, value, derivatives=None):
        self.value = value if isinstance(value, arb) else arb(value)
        self.derivatives = derivatives or [arb(0) for _ in range(5)]

    def __add__(self, other):
        other = other if isinstance(other, Dual) else Dual(other)
        return Dual(
            self.value + other.value,
            [left + right for left, right in zip(self.derivatives, other.derivatives)],
        )

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.value, [-entry for entry in self.derivatives])

    def __sub__(self, other):
        return self + (-other if isinstance(other, Dual) else Dual(-other))

    def __rsub__(self, other):
        return Dual(other) - self

    def __mul__(self, other):
        other = other if isinstance(other, Dual) else Dual(other)
        return Dual(
            self.value * other.value,
            [
                left * other.value + self.value * right
                for left, right in zip(self.derivatives, other.derivatives)
            ],
        )

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, Dual) else Dual(other)
        denominator = other.value * other.value
        return Dual(
            self.value / other.value,
            [
                (left * other.value - self.value * right) / denominator
                for left, right in zip(self.derivatives, other.derivatives)
            ],
        )

    def sin(self):
        return Dual(self.value.sin(), [self.value.cos() * entry for entry in self.derivatives])

    def cos(self):
        return Dual(self.value.cos(), [-self.value.sin() * entry for entry in self.derivatives])


class ComplexDual:
    """Complex number represented by two real interval dual numbers."""

    def __init__(self, real=0, imaginary=0):
        self.real = real if isinstance(real, Dual) else Dual(real)
        self.imaginary = imaginary if isinstance(imaginary, Dual) else Dual(imaginary)

    def __add__(self, other):
        other = other if isinstance(other, ComplexDual) else ComplexDual(other)
        return ComplexDual(self.real + other.real, self.imaginary + other.imaginary)

    __radd__ = __add__

    def __neg__(self):
        return ComplexDual(-self.real, -self.imaginary)

    def __mul__(self, other):
        other = other if isinstance(other, ComplexDual) else ComplexDual(other)
        return ComplexDual(
            self.real * other.real - self.imaginary * other.imaginary,
            self.real * other.imaginary + self.imaginary * other.real,
        )

    __rmul__ = __mul__

    def conjugate(self):
        return ComplexDual(self.real, -self.imaginary)


def variable(value: arb, index: int) -> Dual:
    derivatives = [arb(0) for _ in range(5)]
    derivatives[index] = arb(1)
    return Dual(value, derivatives)


def propagate(phases: list[Dual], duration: Dual, sector: int):
    """Interval-propagate one sector and its exact population integral."""
    rate = arb(sector).sqrt() / 2
    segment_duration = duration / len(phases)
    angle = segment_duration * rate
    cosine, sine = angle.cos(), angle.sin()
    integral_cosine_squared = segment_duration / 2 + (2 * angle).sin() / (4 * rate)
    integral_sine_squared = segment_duration / 2 - (2 * angle).sin() / (4 * rate)
    integral_cross_term = (1 - (2 * angle).cos()) / (2 * rate)

    ground, rydberg = ComplexDual(1), ComplexDual()
    population_integral = Dual(0)
    minus_i = ComplexDual(0, -1)
    for phase in phases:
        control = ComplexDual(phase.cos(), phase.sin())
        quadrature = minus_i * control.conjugate() * ground
        population_integral += (
            integral_cosine_squared
            * (rydberg.real * rydberg.real + rydberg.imaginary * rydberg.imaginary)
            + integral_sine_squared
            * (quadrature.real * quadrature.real + quadrature.imaginary * quadrature.imaginary)
            + integral_cross_term
            * (rydberg.real * quadrature.real + rydberg.imaginary * quadrature.imaginary)
        )
        ground, rydberg = (
            ground * cosine + minus_i * control * rydberg * sine,
            rydberg * cosine + minus_i * control.conjugate() * ground * sine,
        )
    return ground, rydberg, population_integral


def evaluate(values: list[Dual], fixed_phases: list[str]):
    phases = [Dual(arb(phase)) for phase in fixed_phases]
    for variable_index, phase_index in enumerate(VARIABLE_PHASE_INDICES, start=1):
        phases[phase_index] = values[variable_index]
    g1, r1, integral1 = propagate(phases, values[0], 1)
    g2, r2, integral2 = propagate(phases, values[0], 2)
    phase_cross = g2 * (g1 * g1).conjugate()
    terminal = (r1.real, r1.imaginary, r2.real, r2.imaginary, phase_cross.imaginary)
    exposure = (2 * integral1 + integral2) / 4
    return terminal, exposure, phase_cross.real


def matrix_vector(matrix, vector):
    return [
        sum((matrix[row][column] * vector[column] for column in range(5)), arb(0))
        for row in range(5)
    ]


def main() -> None:
    candidate = json.loads(DATA.read_text(encoding="utf-8"), parse_float=str)
    fixed_phases = candidate["phases"]
    boxes = [arb(f"{center} +/- {BOX_RADIUS}") for center in CENTERS]
    interval_values = [variable(box, index) for index, box in enumerate(boxes)]
    terminal, exposure, phase_cross_real = evaluate(interval_values, fixed_phases)
    interval_jacobian = [entry.derivatives for entry in terminal]

    point_values = [variable(arb(center), index) for index, center in enumerate(CENTERS)]
    point_terminal, _, _ = evaluate(point_values, fixed_phases)
    point_residual = [entry.value for entry in point_terminal]
    inverse = [[arb(entry) for entry in row] for row in APPROXIMATE_INVERSE]
    inverse_determinant = arb_mat(inverse).det()

    correction = matrix_vector(inverse, point_residual)
    corrected_center = [arb(center) - correction[index] for index, center in enumerate(CENTERS)]
    defect = [
        [
            arb(1 if row == column else 0)
            - sum(
                (inverse[row][inner] * interval_jacobian[inner][column] for inner in range(5)),
                arb(0),
            )
            for column in range(5)
        ]
        for row in range(5)
    ]
    centered_boxes = [box - arb(center) for box, center in zip(boxes, CENTERS)]
    krawczyk_image = [
        corrected_center[row]
        + sum((defect[row][column] * centered_boxes[column] for column in range(5)), arb(0))
        for row in range(5)
    ]
    inclusions = [box.contains_interior(image) for box, image in zip(boxes, krawczyk_image)]
    defect_row_sums = [
        sum((entry.abs_upper() for entry in row), arb(0)) for row in defect
    ]

    assert not inverse_determinant.contains(0), "Krawczyk preconditioner may be singular"
    assert all(inclusions), "Krawczyk image is not strictly inside its domain box"
    assert all(row_sum < 1 for row_sum in defect_row_sums), "Krawczyk map is not contractive"
    assert phase_cross_real.value.upper() < 0, "certified root is not on the CZ branch"
    assert exposure.value.upper() < arb(CERTIFIED_UPPER_BOUND), (
        "certified exposure target was not met"
    )

    print(
        json.dumps(
            {
                "preconditioner_determinant": str(inverse_determinant),
                "krawczyk_strict_inclusions": inclusions,
                "defect_infinity_norm_row_bounds": [str(value) for value in defect_row_sums],
                "unique_exact_terminal_root": True,
                "cz_branch_cross_real": str(phase_cross_real.value),
                "exposure_interval": str(exposure.value),
                "certified_upper_bound": float(CERTIFIED_UPPER_BOUND),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
