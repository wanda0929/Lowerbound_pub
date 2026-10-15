"""Strong-blockade CZ exposure model.

Units: Omega_max = 1. s = accumulated drive angle (s = Omega_max * t under amplitude bang).

Two independent two-level systems share one drive phase phi(s):
  sphere 1: |01> <-> |0r>   (and |10> <-> |r0>), coupling sqrt(1) = 1
  sphere 2: |11> <-> |W>,    coupling sqrt(2)

H_k = sqrt(k)/2 * [[0, e^{-i phi}], [e^{i phi}, 0]]   in basis (ground, Rydberg).

CZ condition: loop closure b_1 = b_2 = 0 and Phi_2 - 2*Phi_1 = pi (mod 2 pi),
where Phi_k = arg(a_k) is the ground-amplitude phase.

Exposure (Jandura-Pupillo definition, Omega_max = 1):
  T_R * Omega_max = (2 E_1 + E_2) / 4,   E_k = int |b_k|^2 ds.

Targets from the literature:
  JP time-optimal CZ:        T_R = 2.957
  Locher T_R-optimal CZ:     T_R = 2.936  (T = 7.72506187, phase ansatz below)
"""

import numpy as np

PI = np.pi


def propagate(phis, durs, k):
    """Propagate sphere k through a piecewise-constant-phase pulse.

    phis, durs: arrays of segment phases and durations (dimensionless s units).
    Returns (a, b, E): final ground amplitude, final Rydberg amplitude,
    and exact integrated Rydberg population E = int |b|^2 ds.
    """
    om = np.sqrt(k) / 2.0
    a = 1.0 + 0.0j
    b = 0.0 + 0.0j
    E = 0.0
    for phi, tau in zip(phis, durs):
        th = om * tau
        c, sn = np.cos(th), np.sin(th)
        # exact exposure over the segment:
        # b(s') = -i e^{i phi} sin(om s') a + cos(om s') b
        # |b|^2   = sin^2 |a|^2 + cos^2 |b|^2 + 2 sin cos * Im(e^{i phi} a conj(b))
        A2 = abs(a) ** 2
        B2 = abs(b) ** 2
        Q = np.imag(np.exp(1j * phi) * a * np.conj(b))
        I_s2 = tau / 2 - np.sin(2 * th) / (4 * om)
        I_c2 = tau / 2 + np.sin(2 * th) / (4 * om)
        I_2sc = (1 - np.cos(2 * th)) / (2 * om)
        E += A2 * I_s2 + B2 * I_c2 + Q * I_2sc
        a1 = c * a - 1j * np.exp(-1j * phi) * sn * b
        b1 = -1j * np.exp(1j * phi) * sn * a + c * b
        a, b = a1, b1
    return a, b, E


def trajectory(phis, durs, k, nsub=16):
    """Dense trajectory of (s, a, b, u=|a|^2, alpha=arg a) for sphere k."""
    om = np.sqrt(k) / 2.0
    a = 1.0 + 0.0j
    b = 0.0 + 0.0j
    s0 = 0.0
    out = []
    for phi, tau in zip(phis, durs):
        for j in range(nsub):
            ds = tau * j / nsub
            th = om * ds
            c, sn = np.cos(th), np.sin(th)
            aj = c * a - 1j * np.exp(-1j * phi) * sn * b
            bj = -1j * np.exp(1j * phi) * sn * a + c * b
            out.append((s0 + ds, aj, bj))
        th = om * tau
        c, sn = np.cos(th), np.sin(th)
        a1 = c * a - 1j * np.exp(-1j * phi) * sn * b
        b1 = -1j * np.exp(1j * phi) * sn * a + c * b
        a, b = a1, b1
        s0 += tau
    out.append((s0, a, b))
    ss = np.array([r[0] for r in out])
    aa = np.array([r[1] for r in out])
    bb = np.array([r[2] for r in out])
    uu = np.abs(aa) ** 2
    # continuous phase of a
    al = np.unwrap(np.angle(aa))
    return ss, aa, bb, uu, al


def gate_report(phis, durs):
    """Full report: exposures, closures, phases, CZ residual."""
    a1, b1, E1 = propagate(phis, durs, 1)
    a2, b2, E2 = propagate(phis, durs, 2)
    Phi1 = np.angle(a1)
    Phi2 = np.angle(a2)
    resid = (Phi2 - 2 * Phi1 - PI + PI) % (2 * PI) - PI
    TR = (2 * E1 + E2) / 4.0
    return {
        "a1": a1, "b1": b1, "E1": E1,
        "a2": a2, "b2": b2, "E2": E2,
        "Phi1": Phi1, "Phi2": Phi2,
        "phase_resid": resid,
        "closure": abs(b1) ** 2 + abs(b2) ** 2,
        "TR": TR,
        "S": float(np.sum(durs)),
    }


def locher_tr_opt_pulse(nseg=400):
    """Locher et al. T_R-optimal CZ pulse (arXiv:2512.00843), their CRAB ansatz.

    xi(s) = sum_n alpha_n sin[ (2 pi n / T)(1 + 0.5 tanh A_n)(s - T/2) ]
    drive phase phi(s) = xi(s) - Delta0 * s + C,  C chosen so phi(0) = 0.
    """
    S = 7.72506187
    Delta0 = -0.92491109
    A1, al1 = -0.89119131, -2.91001616
    A2, al2 = 0.63210387, -0.08132401

    def xi(s):
        v = 0.0
        for n, (A, al) in enumerate([(A1, al1), (A2, al2)], start=1):
            v += al * np.sin((2 * PI * n / S) * (1 + 0.5 * np.tanh(A)) * (s - S / 2))
        return v

    C = -xi(0.0)
    ss = np.linspace(0, S, nseg + 1)
    phi = np.array([xi(s) - Delta0 * s + C for s in ss])
    # piecewise-constant segments: midpoint sampling
    phis = 0.5 * (phi[:-1] + phi[1:])
    durs = np.full(nseg, S / nseg)
    return phis, durs


def locher_to_pulse(nseg=400):
    """Locher time-optimal CZ pulse (one-sine ansatz + detuning)."""
    S = 7.61140652
    Delta0 = 0.07842706
    A1, al1 = 1.80300902, -0.61792703

    def xi(s):
        return al1 * np.sin((2 * PI / S) * (1 + 0.5 * np.tanh(A1)) * (s - S / 2))

    C = -xi(0.0)
    ss = np.linspace(0, S, nseg + 1)
    phi = np.array([xi(s) - Delta0 * s + C for s in ss])
    phis = 0.5 * (phi[:-1] + phi[1:])
    durs = np.full(nseg, S / nseg)
    return phis, durs
