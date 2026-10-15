"""Fast GRAPE with exact analytic gradients for the strong-blockade CZ exposure problem.

Objective per fixed duration S (n uniform segments):
  J = (2E1+E2)/4 + Wc*(|b1|^2+|b2|^2) + Wp*(1+cos(Phi2-2*Phi1))

All gradients analytic: segment-level closed forms + adjoint recursion.
"""

import numpy as np
from scipy.optimize import minimize

PI = np.pi


def seg_mats(phi, tau, k):
    om = np.sqrt(k) / 2.0
    th = om * tau
    c, sn = np.cos(th), np.sin(th)
    ep, em = np.exp(1j * phi), np.exp(-1j * phi)
    U = np.array([[c, -1j * em * sn], [-1j * ep * sn, c]])
    dU = np.array([[0.0, -sn * em], [sn * ep, 0.0]])
    # exposure integrals
    I_s2 = tau / 2 - np.sin(2 * th) / (4 * om)
    I_c2 = tau / 2 + np.sin(2 * th) / (4 * om)
    I_2sc = (1 - np.cos(2 * th)) / (2 * om)
    return U, dU, I_s2, I_c2, I_2sc, ep, em


def seg_exposure(a, b, I_s2, I_c2, I_2sc, ep):
    Q = np.imag(ep * a * np.conj(b))
    E = abs(a) ** 2 * I_s2 + abs(b) ** 2 * I_c2 + Q * I_2sc
    dE_dphi = np.real(ep * a * np.conj(b)) * I_2sc
    # gradient (g_a, g_b) with delta E = 2 Re[g_a* da + g_b* db]
    em = np.conj(ep)
    g_a = a * I_s2 + 0.5j * em * b * I_2sc
    g_b = b * I_c2 - 0.5j * ep * a * I_2sc
    return E, dE_dphi, g_a, g_b


def value_and_grad(phis, S, Wc, Wp):
    n = len(phis)
    tau = S / n
    # forward pass, store entry states
    psi = {1: np.array([1 + 0j, 0 + 0j]), 2: np.array([1 + 0j, 0 + 0j])}
    entries = {1: [], 2: []}
    segdata = []
    E = {1: 0.0, 2: 0.0}
    for j in range(n):
        row = []
        for k in (1, 2):
            U, dU, I_s2, I_c2, I_2sc, ep, em = seg_mats(phis[j], tau, k)
            a, b = psi[k]
            Ek, dEk, ga, gb = seg_exposure(a, b, I_s2, I_c2, I_2sc, ep)
            E[k] += Ek
            entries[k].append(psi[k].copy())
            row.append((U, dU, dEk, np.array([ga, gb])))
            psi[k] = U @ psi[k]
        segdata.append(row)
    # terminal
    a1, b1 = psi[1]
    a2, b2 = psi[2]
    Phi1, Phi2 = np.angle(a1), np.angle(a2)
    X = Phi2 - 2 * Phi1
    J = (2 * E[1] + E[2]) / 4 + Wc * (abs(b1) ** 2 + abs(b2) ** 2) + Wp * (1 + np.cos(X))
    # terminal gradients (w = (2,1) exposure weights already folded below)
    G = {}
    # exposure terminal gradient is zero (E accumulated); closure + phase:
    sinX = np.sin(X)
    G[1] = np.array([1j * Wp * sinX / np.conj(a1), Wc * b1])
    G[2] = np.array([-0.5j * Wp * sinX / np.conj(a2), Wc * b2])
    # backward pass
    grad = np.zeros(n)
    Gnext = {1: G[1], 2: G[2]}
    for j in range(n - 1, -1, -1):
        for k in (1, 2):
            U, dU, dEk, gdir = segdata[j][k - 1]
            wk = 2.0 if k == 1 else 1.0
            # objective gradient contribution from segment j:
            # dJ = (wk/4) dE_k^{(j)} + 2 Re <Gnext|dU psi>
            psij = entries[k][j]
            grad[j] += (wk / 4.0) * dEk + 2 * np.real(np.vdot(Gnext[k], dU @ psij))
            # recurse: G_j = (wk/4) gdir + U^dagger Gnext   ... but careful:
            # the total gradient wrt entry state psi_j is (wk/4)*g_seg + U^d G_{j+1}
            Gnext[k] = (wk / 4.0) * gdir + U.conj().T @ Gnext[k]
    return J, grad


def cons_report(phis, S):
    from model import gate_report
    return gate_report(phis, np.full(len(phis), S / len(phis)))


def optimize_S(S, n=96, starts=8, seed=0, locher_init=None):
    rng = np.random.default_rng(seed)
    grid_mid = (np.arange(n) + 0.5) * S / n

    def fg(x, Wc, Wp):
        return value_and_grad(x, S, Wc, Wp)

    inits = []
    if locher_init is not None:
        inits.append(locher_init(grid_mid))
    for j in range(starts - len(inits)):
        prof = np.zeros(n)
        for _ in range(4):
            m = rng.integers(1, 5)
            amp = rng.uniform(-2, 2)
            ph0 = rng.uniform(-PI, PI)
            prof += amp * np.sin(2 * PI * m * grid_mid / S + ph0)
        inits.append(prof)

    # exact equality constraints for the SLSQP polish
    def c_b1r(x):
        from model import propagate
        _, b, _ = propagate(x, np.full(n, S / n), 1)
        return np.real(b)
    def c_b1i(x):
        from model import propagate
        _, b, _ = propagate(x, np.full(n, S / n), 1)
        return np.imag(b)
    def c_b2r(x):
        from model import propagate
        _, b, _ = propagate(x, np.full(n, S / n), 2)
        return np.real(b)
    def c_b2i(x):
        from model import propagate
        _, b, _ = propagate(x, np.full(n, S / n), 2)
        return np.imag(b)
    def c_phase(x):
        from model import propagate
        a1, _, _ = propagate(x, np.full(n, S / n), 1)
        a2, _, _ = propagate(x, np.full(n, S / n), 2)
        return np.angle(a2) - 2 * np.angle(a1) - PI
    cons = [{"type": "eq", "fun": f} for f in (c_b1r, c_b1i, c_b2r, c_b2i, c_phase)]

    best = None
    for i, p0 in enumerate(inits):
        res = minimize(fg, p0, args=(3e3, 3e2), jac=True, method="L-BFGS-B",
                       options={"maxiter": 1200, "ftol": 1e-15, "gtol": 1e-11})
        res = minimize(fg, res.x, args=(1e5, 1e4), jac=True, method="L-BFGS-B",
                       options={"maxiter": 400, "ftol": 1e-15, "gtol": 1e-12})
        # exact-constraint polish: minimize TR directly subject to closure+phase
        def TR_only(x):
            return value_and_grad(x, S, 0.0, 0.0)
        res = minimize(TR_only, res.x, jac=True, method="SLSQP",
                       constraints=cons, options={"maxiter": 300, "ftol": 1e-15})
        rep = cons_report(res.x, S)
        ok = rep["closure"] < 1e-10 and abs(rep["phase_resid"]) < 1e-7
        if ok and (best is None or rep["TR"] < best[0]["TR"]):
            best = (rep, res.x.copy())
    return best


if __name__ == "__main__":
    # gradient check
    rng = np.random.default_rng(0)
    phis = rng.uniform(-1, 1, 16)
    S = 8.0
    J0, g = value_and_grad(phis, S, 3e3, 3e2)
    eps = 1e-7
    gfd = np.zeros(16)
    for j in range(16):
        dp = phis.copy(); dp[j] += eps
        Jp, _ = value_and_grad(dp, S, 3e3, 3e2)
        dm = phis.copy(); dm[j] -= eps
        Jm, _ = value_and_grad(dm, S, 3e3, 3e2)
        gfd[j] = (Jp - Jm) / (2 * eps)
    print("grad: max |analytic - FD| =", np.abs(g - gfd).max())
    print("relative:", np.abs(g - gfd).max() / (np.abs(gfd).max() + 1e-12))
