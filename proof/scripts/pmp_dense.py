"""High-precision PMP stationarity check (clean version).

Approach: store segment-entry states exactly; for dense output, propagate the
entry state by the partial segment time.  Adjoint integrated backward with
solve_ivp at rtol=1e-11 using linear interpolation of the forcing.
"""

import numpy as np
from scipy.integrate import solve_ivp

PI = np.pi
SQ = {1: 1.0, 2: np.sqrt(2.0)}
W = {1: 2.0, 2: 1.0}


def Amat(k, chi):
    c, s = np.cos(chi), np.sin(chi)
    g = SQ[k] / 2
    return g * np.array([
        [0, 0, -s, c],
        [0, 0, -c, -s],
        [s, c, 0, 0],
        [-c, s, 0, 0],
    ])


def dAmat(k, chi):
    c, s = np.cos(chi), np.sin(chi)
    g = SQ[k] / 2
    return g * np.array([
        [0, 0, -c, -s],
        [0, 0, s, -c],
        [c, -s, 0, 0],
        [s, c, 0, 0],
    ])


def seg_step(state, phi, tau, k):
    a, b = state
    om = SQ[k] / 2
    th = om * tau
    c, sn = np.cos(th), np.sin(th)
    ep, em = np.exp(1j * phi), np.exp(-1j * phi)
    return (c * a - 1j * em * sn * b, -1j * ep * sn * a + c * b)


def run_check(phis, durs, npts=2000, label=""):
    N = len(durs)
    S = float(np.sum(durs))
    bounds = np.concatenate([[0.0], np.cumsum(durs)])
    # entry states per segment (complex pairs)
    entries = {1: [(1 + 0j, 0 + 0j)], 2: [(1 + 0j, 0 + 0j)]}
    for j in range(N):
        for k in (1, 2):
            entries[k].append(seg_step(entries[k][-1], phis[j], durs[j], k))
    s_dense = np.linspace(0, S, npts)
    seg_idx = np.minimum(np.searchsorted(bounds, s_dense, side="right") - 1, N - 1)
    x_dense = {1: np.zeros((npts, 4)), 2: np.zeros((npts, 4))}
    chi_dense = phis[seg_idx]
    for i, s in enumerate(s_dense):
        j = seg_idx[i]
        tin = s - bounds[j]
        for k in (1, 2):
            a, b = seg_step(entries[k][j], phis[j], tin, k)
            x_dense[k][i] = [a.real, a.imag, b.real, b.imag]

    def forcing(k, i):
        bR, bI = x_dense[k][i, 2], x_dense[k][i, 3]
        return np.array([0.0, 0.0, 0.5 * W[k] * bR, 0.5 * W[k] * bI])

    # terminal phases
    Phi = {}
    for k in (1, 2):
        a = entries[k][N][0]
        Phi[k] = np.angle(a)
    tvec = np.zeros(8)
    tvec[0] = -np.sin(Phi[1]); tvec[1] = np.cos(Phi[1])
    tvec[4] = -2 * np.sin(Phi[2]); tvec[5] = 2 * np.cos(Phi[2])

    # integrate adjoint backward for 8 terminal basis vectors
    s_rev = s_dense[::-1]
    Rcols = []
    for m in range(8):
        lamF = np.zeros(8); lamF[m] = 1.0
        def rhs(s, lam):
            i = np.searchsorted(s_dense, s)
            i = min(max(i, 1), npts - 1)
            out = np.zeros(8)
            for k in (1, 2):
                sl = slice(0, 4) if k == 1 else slice(4, 8)
                A = Amat(k, float(np.interp(s, s_dense, chi_dense)))
                g = forcing(k, i)
                out[sl] = A @ lam[sl] + g
            return out
        sol = solve_ivp(rhs, [S, 0.0], lamF, t_eval=s_rev, rtol=1e-11, atol=1e-13)
        lam_dense = sol.y[:, ::-1]  # forward-time order
        # stationarity residual on dense grid
        res = np.zeros(npts)
        for i in range(npts):
            dA = np.zeros((8, 8))
            dA[:4, :4] = dAmat(1, chi_dense[i])
            dA[4:, 4:] = dAmat(2, chi_dense[i])
            xm = np.concatenate([x_dense[1][i], x_dense[2][i]])
            res[i] = lam_dense[:, i] @ (dA @ xm)
        Rcols.append(res)
    R = np.array(Rcols).T  # npts x 8
    trow = tvec[None, :] * (np.abs(R).max() or 1.0)
    M = np.vstack([R, trow])
    _, Sv, Vt = np.linalg.svd(M, full_matrices=False)
    c = Vt[-1]
    resid = R @ c
    # also H along solution: H = sum lam . A x - L
    i0 = npts // 2
    print(f"[{label}] n={N}: singular values {np.round(Sv, 5)}")
    print(f"[{label}] max|resid| = {np.abs(resid).max():.3e}, rms = {np.sqrt((resid**2).mean()):.3e}")
    return np.abs(resid).max()


if __name__ == "__main__":
    import sys
    sys.path.insert(0, ".")
    x = np.load("best_pulse_192.npy")
    n = len(x)
    durs = np.full(n, 7.725 / n)
    run_check(x, durs, label="best192")
