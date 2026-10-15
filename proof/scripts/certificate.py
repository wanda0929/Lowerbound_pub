"""Definitive PMP certificate for the optimal CZ exposure pulse.

1. Discrete KKT stationarity of the n=192 SLSQP optimum (Lagrangian gradient ~0).
2. Continuous PMP stationarity along the pulse (lambda = 2(Re G, Im G) from the
   validated backward recursion; midpoint evaluation).
3. Endpoint identity:  T_R = (1/2) sum_k [lambda_k . x_k]_0^S.
4. First-integral probes along the extremal.
"""

import numpy as np
from model import propagate
from grape_fast import value_and_grad

x = np.load('best_pulse_192.npy'); n = len(x); S = 7.725
durs = np.full(n, S/n)
nu = np.load('cz_multipliers.npy')

def segU(phi, tau, k):
    om = np.sqrt(k)/2; th = om*tau; c, sn = np.cos(th), np.sin(th)
    ep, em = np.exp(1j*phi), np.exp(-1j*phi)
    U = np.array([[c, -1j*em*sn],[-1j*ep*sn, c]])
    dU = np.array([[0., -sn*em],[sn*ep, 0.]])
    return U, dU

def seg_exposure_grad(phi, tau, k, a, b):
    om = np.sqrt(k)/2; th = om*tau
    ep, em = np.exp(1j*phi), np.exp(-1j*phi)
    I_s2 = tau/2 - np.sin(2*th)/(4*om); I_c2 = tau/2 + np.sin(2*th)/(4*om)
    I_2sc = (1-np.cos(2*th))/(2*om)
    g_a = a*I_s2 + 0.5j*em*b*I_2sc
    g_b = b*I_c2 - 0.5j*ep*a*I_2sc
    dE_dphi = np.real(ep*a*np.conj(b))*I_2sc
    return np.array([g_a, g_b]), dE_dphi

entries = {1: [(1+0j,0+0j)], 2: [(1+0j,0+0j)]}
for j in range(n):
    for k in (1,2):
        a,b = entries[k][-1]
        U,_ = segU(x[j], durs[j], k)
        entries[k].append(U @ np.array([a,b]))
a1S, b1S = entries[1][n]; a2S, b2S = entries[2][n]

# terminal costates from multipliers (validated path)
# phase constraint c5 = Phi2 - 2 Phi1 - pi:  d c5 / d a1 = -2 * i/(2 conj(a1)),
#   d c5 / d a2 = + i/(2 conj(a2))   [note the factor 1/2 -- arg-gradient]
GT = {1: np.array([-1j*nu[4]/np.conj(a1S), (nu[0]+1j*nu[1])/2]),
      2: np.array([1j*nu[4]/(2*np.conj(a2S)), (nu[2]+1j*nu[3])/2])}
W2 = {1: 2.0, 2: 1.0}
Gs = {1: [None]*(n+1), 2: [None]*(n+1)}
Gs[1][n] = GT[1]; Gs[2][n] = GT[2]
for j in range(n-1, -1, -1):
    for k in (1,2):
        a,b = entries[k][j]
        U,_ = segU(x[j], durs[j], k)
        gseg, _ = seg_exposure_grad(x[j], durs[j], k, a, b)
        Gs[k][j] = (W2[k]/4)*gseg + U.conj().T @ Gs[k][j+1]

# 1. discrete KKT stationarity of the Lagrangian (per segment):
#    dLagr/dphi_j = sum_k [ (w_k/4) dE_j/dphi_j + 2 Re<Gs[k][j+1], dU_j psi_j> ]
disc = np.zeros(n)
for j in range(n):
    for k in (1,2):
        a,b = entries[k][j]
        U, dU = segU(x[j], durs[j], k)
        _, dE_dphi = seg_exposure_grad(x[j], durs[j], k, a, b)
        disc[j] += (W2[k]/4)*dE_dphi + 2*np.real(np.vdot(Gs[k][j+1], dU @ np.array([a,b])))
print('1. discrete KKT stationarity: max %.3e rms %.3e' % (np.abs(disc).max(), np.sqrt((disc**2).mean())))

# 2. continuous stationarity: sum_k lambda_k . dA_k/dchi x_k  (midpoint)
from pmp_dense import dAmat
lam = lambda Gv: 2*np.array([Gv[0].real, Gv[0].imag, Gv[1].real, Gv[1].imag])
resid = np.zeros(n)
for j in range(n):
    r = 0.0
    for k in (1,2):
        a,b = entries[k][j]
        om = np.sqrt(k)/2; th = om*durs[j]/2; c, sn = np.cos(th), np.sin(th)
        ep, em = np.exp(1j*x[j]), np.exp(-1j*x[j])
        am = c*a - 1j*em*sn*b; bm = -1j*ep*sn*a + c*b
        xm = np.array([am.real, am.imag, bm.real, bm.imag])
        Gm = 0.5*(Gs[k][j]+Gs[k][j+1])
        r += lam(Gm) @ (dAmat(k, x[j]) @ xm)
    resid[j] = r
print('2. continuous PMP stationarity (midpoint): max %.3e rms %.3e' % (np.abs(resid).max(), np.sqrt((resid**2).mean())))

# 3. endpoint identity: T_R = -(1/2) sum_k [lambda_k . x_k]_0^S
lx0 = sum(lam(Gs[k][0])[0] for k in (1,2))   # x(0)=(1,0,0,0): pair = lam_aR(0)
axS = {k: np.array([entries[k][n][0].real, entries[k][n][0].imag, entries[k][n][1].real, entries[k][n][1].imag]) for k in (1,2)}
lxS = sum(lam(Gs[k][n]) @ axS[k] for k in (1,2))
print('3. (lam.x)(S) = %.3e ; T_R = -0.5*((lam.x)(S)-(lam.x)(0)) = %.7f  vs direct 2.9359556' % (lxS, -0.5*(lxS-lx0)))

# 4. transversality: lambda(S) must annihilate the CZ terminal-manifold tangent
P1, P2 = np.angle(a1S), np.angle(a2S)
tvec = np.concatenate([[-np.sin(P1), np.cos(P1), 0,0],[-2*np.sin(P2), 2*np.cos(P2),0,0]])
lamS = np.concatenate([lam(Gs[1][n]), lam(Gs[2][n])])
print('4. transversality lam(S).tangent = %.3e' % (lamS @ tvec))
print('   phase-constraint multiplier nu5 = %.5f; alpha-momentum endpoints: %.6f (sphere 1), %.6f (sphere 2 = nu5)'
      % (nu[4], -2*nu[4], nu[4]))
