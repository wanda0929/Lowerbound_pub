"""Regenerate figures/fig_pulse.{pdf,png} without modifying trajectory data from the
archived low-exposure pulse proof/data/best_pulse_192.npy (S = 7.725 exactly).

This makes figure, dense-trajectory artifact, and manuscript numbers
(TR = 2.9359556, closure 4.4e-27, Phi1 = -2.046993, Phi2 = -0.952394)
mutually consistent: one source pulse, one generator.

Run from the LowerBoundCZ directory:  python3 proof/scripts/make_fig_pulse.py
"""

import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from model import gate_report, trajectory

plt.style.use(pathlib.Path(__file__).with_name("publication.mplstyle"))
BROWN = "#D55E00"
TEAL = "#0072B2"

phis = np.load("proof/data/best_pulse_192.npy")
n = len(phis)
S = 7.725  # exact duration of the archived low-exposure pulse
durs = np.full(n, S / n)

rep = gate_report(phis, durs)
print("gate report: TR=%.7f closure=%.2e resid=%.2e Phi1=%.6f Phi2=%.6f"
      % (rep["TR"], rep["closure"], rep["phase_resid"], rep["Phi1"], rep["Phi2"]))
assert abs(rep["TR"] - 2.9359556) < 1e-6, "archived pulse does not reproduce the headline value"

s1, a1, b1, u1, al1 = trajectory(phis, durs, 1, nsub=25)
s2, a2, b2, u2, al2 = trajectory(phis, durs, 2, nsub=25)
p1 = 1.0 - u1
p2 = 1.0 - u2
zeta = np.unwrap(al2 - 2 * al1)

# Plot the actual piecewise-constant phase, not a derivative inferred from jumps.
chi_prof = np.unwrap(phis)
s_edges = np.concatenate(([0.0], np.cumsum(durs)))

fig, axs = plt.subplots(3, 1, figsize=(7.0, 5.2), sharex=True)

axs[0].plot(s1, p1, color=BROWN, lw=1.6, label="$p_1$ (single-excitation)")
axs[0].plot(s2, p2, color=TEAL, ls="--", lw=1.6, label="$p_2$ (collective)")
axs[0].set_ylim(0.0, 1.05)
axs[0].set_yticks([0.0, 0.5, 1.0])
axs[0].set_ylabel("Rydberg\npopulation")
axs[0].legend(loc="lower center", bbox_to_anchor=(0.5, 1.02), ncol=2,
              frameon=False)

axs[1].stairs(chi_prof, s_edges, baseline=None, color="0.25", lw=1.5)
axs[1].set_ylabel("Laser phase\n" + r"$\chi$ (rad)")
axs[1].set_xlim(0, S)

axs[2].plot(s1, zeta, color=BROWN, lw=1.6)
axs[2].axhline(-np.pi, ls=":", color="0.45", lw=1.0)
axs[2].set_yticks([-np.pi, -np.pi/2, 0], [r"$-\pi$", r"$-\pi/2$", "0"])
axs[2].set_ylabel("Nonlocal phase\n" + r"$\zeta$ (rad)")
axs[2].set_xlabel(r"Active time $s = \Omega_{\max}\,t$")

# Mark midpoint symmetry at s = S/2 across all subplots
for ax in axs:
    ax.axvline(S / 2, color="0.85", ls="-.", lw=0.8, zorder=0)

for label, ax in zip("abc", axs):
    ax.spines[["top", "right"]].set_visible(False)
    ax.text(0.02, 0.98, f"({label})", transform=ax.transAxes,
            va="top", fontsize=10, fontweight="bold",
            bbox=dict(facecolor="white", edgecolor="none", pad=1))
fig.align_ylabels(axs)
fig.tight_layout()
fig.savefig("figures/fig_pulse.png")
fig.savefig("figures/fig_pulse.pdf")
print("wrote figures/fig_pulse.png and figures/fig_pulse.pdf")
