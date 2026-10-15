"""Landscape scan with fast gradients: min T_R vs duration S."""

import json
import sys
import numpy as np
from grape_fast import optimize_S
from model import locher_tr_opt_pulse

PI = np.pi


def locher_init_factory(S):
    ph_l, du_l = locher_tr_opt_pulse(1200)
    s_l = np.concatenate([[0], np.cumsum(du_l)])
    mid_l = 0.5 * (s_l[:-1] + s_l[1:])
    un = np.unwrap(np.concatenate([[ph_l[0]], ph_l])[:-1])
    def init(mid):
        return np.interp(mid, mid_l * S / du_l.sum(), un)
    return init


if __name__ == "__main__":
    S_list = [float(x) for x in sys.argv[1:]] or \
        [6.5, 7.0, 7.3, 7.612, 7.725, 8.0, 8.5, 9.0, 10.0, 12.0, 16.0, 24.0, 40.0]
    out = {}
    for S in S_list:
        best = optimize_S(S, n=96, starts=14, seed=int(S * 1000) % (2**31),
                          locher_init=locher_init_factory(S))
        if best:
            rep = best[0]
            out[f"{S}"] = {"TR": rep["TR"], "E1": rep["E1"], "E2": rep["E2"],
                           "Phi1": rep["Phi1"], "Phi2": rep["Phi2"],
                           "closure": rep["closure"], "resid": rep["phase_resid"]}
            np.save(f"pulse_S{S:.3f}.npy", best[1])
            print(f"S={S:6.3f}  TR={rep['TR']:.5f}  E1={rep['E1']:.4f} E2={rep['E2']:.4f}  "
                  f"Phi1={rep['Phi1']:+.4f}  clos={rep['closure']:.1e}", flush=True)
        else:
            print(f"S={S:6.3f}  no converged start", flush=True)
        with open("landscape.json", "w") as f:
            json.dump(out, f, indent=1)
