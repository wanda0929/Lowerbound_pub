"""Five physical coordinates after ONLY the two verified charge actions.

Floating diagnostic; all local minima are upper estimates of the true minimum.
"""
import argparse
import json
import math
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).parent


def evaluator(cell, xi):
    data = np.load(ROOT / 'full-phase-polynomials.npz', allow_pickle=False)
    coefficients = defaultdict(complex)
    for coefficient, key in zip(data[f'c{cell}'], data[f'k{cell}']):
        q, anti, holo = int(key[0]), key[1:6], key[6:11]
        powers = tuple(anti[i] + holo[i] for i in (1, 2, 3, 4))
        frequencies = tuple(holo[i] - anti[i] for i in (2, 3, 4))
        coefficients[powers + frequencies] += coefficient * xi**q
    keys = np.asarray(list(coefficients), dtype=int)
    weights = np.asarray(list(coefficients.values()))
    powers, frequencies = keys[:, :4], keys[:, 4:]
    max_power = int(powers.max())

    def evaluate(x):
        a, b = x[:2]
        amplitudes = np.array([np.cos(a), np.sin(a), np.cos(b), np.sin(b)])
        derivatives = np.array([-np.sin(a), np.cos(a), -np.sin(b), np.cos(b)])
        table = amplitudes[:, None] ** np.arange(max_power + 1)
        factors = [table[i, powers[:, i]] for i in range(4)]
        phase = weights * np.exp(1j * (frequencies @ x[2:]))
        terms = phase * np.prod(factors, axis=0)
        value = np.real(terms.sum())
        gradient = np.empty(5)
        for axis in (0, 1):
            accum = 0j
            for i in (2 * axis, 2 * axis + 1):
                degree = powers[:, i]
                product = phase * degree * table[i, np.maximum(0, degree - 1)] * derivatives[i]
                for k in range(4):
                    if i != k:
                        product = product * factors[k]
                accum += product.sum()
            gradient[axis] = np.real(accum)
        gradient[2:] = np.real(1j * (terms @ frequencies))
        cost = np.sin(a)**2 / 2 + np.sin(b)**2 / 4
        cost_grad = np.array([np.sin(a) * np.cos(a), np.sin(b) * np.cos(b) / 2, 0, 0, 0])
        return value / cost, gradient / cost - value * cost_grad / cost**2

    return evaluate


def run(cell, xi, output, starts):
    ev = evaluator(cell, xi)
    rng = np.random.default_rng(711 + cell)
    bounds = [(1e-5, math.pi / 2 - 1e-5)] * 2 + [(-math.pi, math.pi)] * 3
    probe = np.array([.31, .62, .4, -.7, 1.2])
    analytic = ev(probe)[1]
    step = 1e-6
    finite = np.array([(ev(probe + np.eye(5)[i] * step)[0] - ev(probe - np.eye(5)[i] * step)[0]) / (2 * step) for i in range(5)])
    gradient_error = float(np.max(np.abs(finite - analytic)))
    assert gradient_error < 1e-3 * max(1, np.max(np.abs(analytic))), (analytic, finite)
    seeds = [np.array([rng.uniform(*bound) for bound in bounds]) for _ in range(starts)]
    old = json.loads((ROOT / 'full-phase.json').read_text())['rows']
    for row in old:
        if row['cell'] == cell + 1 and row['xi'] == xi:
            seeds.append(np.array(row['results'][0]['point']))
    records = []
    for seed in seeds:
        result = minimize(ev, seed, jac=True, method='L-BFGS-B', bounds=bounds,
                          options={'maxiter': 500, 'ftol': 1e-13, 'gtol': 1e-8})
        records.append({'ratio': float(result.fun), 'point': result.x.tolist(), 'success': bool(result.success)})
    records.sort(key=lambda x: x['ratio'])
    out = {'status': 'FLOATING ONLY; not a global minimum or a certificate', 'cell': cell + 1,
           'xi': xi, 'parameterization': 'u=1, g1=cos(t1), r1=sin(t1)exp(i a), g2=cos(t2)exp(i b), r2=sin(t2)exp(i c)',
           'gradient_error': gradient_error, 'results': records}
    output.write_text(json.dumps(out, indent=2) + '\n')
    print(cell + 1, xi, records[0], flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--cell', type=int, choices=range(5), required=True, help='zero-based source cell')
    parser.add_argument('--xi', type=float, required=True)
    parser.add_argument('--starts', type=int, default=12)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not 0 <= args.xi <= 1 or args.starts < 1:
        parser.error('--xi must be in [0,1] and --starts must be positive')
    run(args.cell, args.xi, args.output, args.starts)
