"""GRAPE-style optimization of T_R for the strong-blockade CZ.

Objective: J = T_R + Wc*(|b1|^2+|b2|^2) + Wp*(1 + cos(Phi2 - 2 Phi1))
Variables: phase profile phi_1..phi_N on a uniform grid over [0, S], S fixed per run.

Multi-start: Locher profile + smooth random inits.
"""

import numpy as np
from scipy.optimize import minimize
from model import gate_report, locher_tr_opt_pulse, locher_to_pulse

PI = np.pi
WC = 3e3
WP = 3e2


def unpack(x, n):
    return x[:n]


def objective(x, n):
    phis = x[:n]
    durs = np.full(n, x[n] / n) if len(x) > n else np.full(n, S_FIXED / n)
    rep = gate_report(phis, durs)
    J = rep["TR"] + WC * rep["closure"] + WP * (1 + np.cos(rep["Phi2"] - 2 * rep["Phi1"]))
    return J


def optimize_at_S(S, n=64, starts=8, seed=0, verbose=True):
    global S_FIXED
    S_FIXED = S
    rng = np.random.default_rng(seed)
    durs = np.full(n, S / n)

    def obj(phis):
        rep = gate_report(phis, durs)
        return rep["TR"] + WC * rep["closure"] + WP * (1 + np.cos(rep["Phi2"] - 2 * rep["Phi1"]))

    inits = []
    # init 1: resampled Locher T_R-opt profile
    ph_l, du_l = locher_tr_opt_pulse(400)
    ss_l = np.linspace(0, du_l.sum(), 401)
    grid = np.linspace(0, S, n + 1)
    mid = 0.5 * (grid[:-1] + grid[1:])
    s_mid_l = 0.5 * (ss_l[:-1] + ss_l[1:])
    inits.append(np.interp(mid, s_mid_l * S / du_l.sum(), np.unwrap(ph_l)))
    # random smooth inits: sums of a few sinusoids
    for j in range(starts - 1):
        prof = np.zeros(n)
        for _ in range(3):
            m = rng.integers(1, 4)
            amp = rng.uniform(-1.5, 1.5)
            ph0 = rng.uniform(-PI, PI)
            prof += amp * np.sin(2 * PI * m * mid / S + ph0)
        inits.append(prof)

    best = None
    for i, p0 in enumerate(inits):
        res = minimize(obj, p0, method="L-BFGS-B",
                       options={"maxiter": 2000, "ftol": 1e-14, "gtol": 1e-10})
        rep = gate_report(res.x, durs)
        ok = rep["closure"] < 1e-8 and abs(rep["phase_resid"]) < 1e-4
        if verbose:
            print(f"  start {i}: J={res.fun:.5f}  TR={rep['TR']:.5f}  clos={rep['closure']:.1e} "
                  f"resid={rep['phase_resid']:.1e}  Phi1={rep['Phi1']:.3f}  ok={ok}")
        if ok and (best is None or rep["TR"] < best[0]["TR"]):
            best = (rep, res.x)
    return best


if __name__ == "__main__":
    for S in [7.612, 7.725, 9.0, 12.0, 20.0, 30.0]:
        print(f"=== S = {S} ===")
        best = optimize_at_S(S, n=64, starts=6, seed=int(S * 10))
        if best:
            print(f"  BEST: TR = {best[0]['TR']:.5f}\n")
