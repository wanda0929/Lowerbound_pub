#!/usr/bin/env python3
"""Exact replacement-allocation and stronger-crossing acceptance.

The pinned original bundle's entire predecessor chain remains a prerequisite.
This checker does not import an optimizer or any new producer.
"""
import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
import sys
from fractions import Fraction as F
from math import comb
from pathlib import Path

from flint import fmpq as Q, fmpq_mat as Mat

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
OLD = F('2.931287603326')
CAP = F('2.932')
SOURCE = '1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
BASE = '3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb'
OCC = 'cce6d0af84023f0d8619686d0b94f4f51f515c0b99c68560acfbea6489c144bd'
FINAL = '5f5edbf79a66e4ee060ae0d069eeaabe772e30f2a6df64f29d626d2c956c0784'
CROSS = '98560cc0bd55714dfb74814e377caac64cb4c736652e33868925da7b25703fd7'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def pinned(path, expected, compressed=False):
    raw = path.read_bytes()
    if compressed:
        raw = gzip.decompress(raw)
    need(digest(raw) == expected, 'pinned input: ' + str(path))
    return json.loads(raw)


def inputs(bundle):
    root = bundle / 'verification_results'
    spec = importlib.util.spec_from_file_location('inherited_signed_power', root / 'adaptive-slack/verify.py')
    v = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v)
    base = pinned(root / 'population-refinement/certified/population-certificate.json.gz', BASE, True)
    occ = pinned(root / 'reachability-slack/certified/occupation-certificate.json', OCC)
    final = pinned(root / 'reachability-slack/certified/certificate.json', FINAL)
    cross = pinned(root / 'joint-slack/certified/crossing-certificate.json', CROSS)
    need(v.SOURCE == SOURCE and v.L == F('2.9305') and F(final['bound']) == OLD, 'model constants')
    need(F(occ['counterexample_cap']) == F(final['counterexample_cap']) == CAP, 'predecessor caps')
    return v, base, occ, final, cross


def endpoint(v, beta, previous, previous_bound, target, gain):
    beta, previous = list(map(F, beta)), list(map(F, previous))
    need(len(beta) == len(previous) == 14 and min(beta) > 0, 'endpoint positivity')
    need(previous_bound <= target <= CAP, 'endpoint/cap')
    rho = (target - v.L) / (previous_bound - v.L)
    for i in range(14):
        t = F(i, 13)
        need(v.bvalue(beta, t) == v.bvalue(previous, rho * t) + gain - (target - previous_bound),
             'endpoint identity')


def allocation(v, base, occ, final, cert):
    need(cert['schema'] == 'minexposure/allocation-improvement-v1', 'allocation schema')
    need(cert['occupation_sha256'] == OCC and cert['final_sha256'] == FINAL, 'allocation predecessors')
    need(type(cert['grid']) is int and cert['grid'] == 8 and F(cert['counterexample_cap']) == CAP, 'allocation grid/cap')
    need(cert['scope'] == 'all-duration ideal-blockade stationary-torus', 'allocation scope')
    records = base['projection_records']
    allowed = {i for item in base['integration_bins'] for i, _, _ in item['allocations']}
    maps = {(x, y): v.popmap(7, x, y, 8) for x in range(8) for y in range(8)}
    seen, cache = set(), {}
    gain, coefficients, budgets = F(0), 0, 0
    for entry in cert['replacements']:
        i = entry['interval_index']
        need(type(i) is int and 0 <= i < 320 and i not in seen, 'duplicate/invalid interval')
        seen.add(i)
        item = base['integration_bins'][i]
        cell = item['cell']
        a, b = F(item['a']), F(item['b'])
        width = v.KNOTS[cell + 1] - v.KNOTS[cell]
        A, D = v.U * (v.KNOTS[cell] + width * a), v.U * (v.KNOTS[cell] + width * b)
        need(0 <= A < D < F(occ['previous_bound']) < OLD, 'unproved prefix')
        delta = list(map(Q, entry['bernstein']))
        previous = list(map(Q, occ['intervals'][i]['bernstein']))
        need(len(delta) == len(previous) == 15 and sum(delta) > sum(previous), 'replacement profile')
        need(len(entry['regions']) == 64, 'missing region')
        xy = set()
        transform = v.affine(14, a, b)
        for region in entry['regions']:
            x, y = region['x'], region['y']
            need(type(x) is int and type(y) is int and 0 <= x < 8 and 0 <= y < 8 and (x, y) not in xy,
                 'population coverage')
            xy.add((x, y))
            groups, count, _ = v.region_weights(region, records, allowed, cell)
            budgets += count
            pop, cost = maps[x, y]
            values = transform * v.tensor(groups, cache) * pop
            for k in range(15):
                for col, c in enumerate(cost):
                    need(values[k, col] >= delta[k] * c, 'allocation tensor')
                    coefficients += 1
        gain += (D - A) * F(str((sum(delta) - sum(previous)) / 15))
    need(seen and gain == F(cert['additional_occupation_slack']), 'occupation integral')
    need(F(cert['previous_bound']) == OLD, 'allocation previous endpoint')
    endpoint(v, cert['endpoint_bernstein'], final['endpoint_bernstein'], OLD, F(cert['bound']), gain)
    return gain, {'replaced_intervals': len(seen), 'allocation_coefficients': coefficients, 'gram_budget_checks': budgets}


def barrier(order):
    need(type(order) is int and order in (8, 16, 32, 64), 'barrier order')
    a = [F(1)]
    for k in range(order):
        a.append(a[-1] * F(2 * k + 1, 2 * k + 2))
    residual = [F(1)] + [F(0)] * (2 * order + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(a):
            residual[i + j] -= x * y
            residual[i + j + 1] += x * y
    need(min(residual) >= 0, 'barrier derivative bound')
    h = [3 * x / (2 * k + 3) for k, x in enumerate(a)]
    need(min(h) > 0, 'barrier monotonicity')
    return h


def crossing(v, oldcross, occ, cert):
    need(cert['schema'] == 'minexposure/reachable-crossings-v1', 'crossing schema')
    need(cert['occupation_certificate_sha256'] == OCC and cert['crossing_certificate_sha256'] == CROSS
         and cert['source_certificate_sha256'] == SOURCE, 'crossing predecessors')
    need(F(cert['counterexample_cap']) == CAP, 'crossing cap')
    n = cert['grid']
    need(type(n) is int and n in (16, 32, 64), 'crossing grid')
    h = barrier(cert['barrier_series_order'])
    energy = [F(i, n)**3 * sum((c * F(i, n)**k for k, c in enumerate(h)), F(0))**2 for i in range(n)]
    need(len(cert['crossings']) == len(oldcross['crossings']) == 4, 'crossing count')
    gain, coefficients, excluded = F(0), 0, 0
    maps = {}
    for j, entry in enumerate(cert['crossings']):
        old = oldcross['crossings'][j]
        need(entry['knot'] == old['knot'] == j, 'crossing order')
        lower = F(entry['bound'])
        need(F(entry['old_bound']) == F(old['bound']) <= lower, 'old crossing bound')
        need(entry['mode'] == 'reachable', 'crossing mode')
        C = v.U * v.KNOTS[j + 1]
        need(C < F(occ['previous_bound']), 'mandatory crossing')
        radius = min(C, CAP - C)
        power = [Q(0)] * 64
        seen = set()
        for rid, weight in old['allocations']:
            need(rid not in seen, 'duplicate pinned allocation')
            seen.add(rid)
            record = oldcross['records'][rid]
            need(record['knot'] == j, 'crossing projection')
            g, r, hh, s = record['population_exponents']
            rate = Q(weight) * Q(record['gamma'])
            need(rate > 0 and g + r <= 7 and hh + s <= 7, 'crossing factor')
            for i in range(g + 1):
                for k in range(hh + 1):
                    power[8 * (r + i) + s + k] += rate * (-1)**(i + k) * comb(g, i) * comb(hh, k)
        row = Mat([power])
        drops = 0
        for x in range(n):
            for y in range(n):
                A, D, T = 8 * energy[x], energy[y], 72 * radius**2
                if A + D > T or (T - A - D)**2 < 4 * A * D:
                    drops += 1
                    continue
                if (x, y) not in maps:
                    maps[x, y] = v.popmap(7, x, y, n)[0]
                values = row * maps[x, y]
                need(all(values[0, i] >= Q(str(lower)) for i in range(64)), 'crossing tensor')
                coefficients += 64
        need(drops == entry['discarded_boxes'] and n * n - drops == entry['retained_boxes'] > 0, 'crossing cover')
        excluded += drops
        gain += lower - F(old['bound'])
    need(gain == F(cert['additional_crossing_slack']), 'crossing integral')
    previous = F(occ['bound'])
    need(F(cert['previous_bound']) == previous, 'crossing previous endpoint')
    endpoint(v, cert['endpoint_bernstein'], occ['endpoint_bernstein'], previous, F(cert['bound']), gain)
    return gain, {'crossing_coefficients': coefficients, 'excluded_crossing_boxes': excluded}


def combined(v, final, cert, gain):
    need(cert['schema'] == 'minexposure/disjoint-slack-campaign-v1', 'combined schema')
    need(F(cert['previous_bound']) == OLD and F(cert['counterexample_cap']) == CAP, 'combined predecessor/cap')
    need(F(cert['additional_slack']) == gain and gain > 0, 'combined slack')
    need(F(cert['bound']) > OLD, 'combined improvement')
    endpoint(v, cert['endpoint_bernstein'], final['endpoint_bernstein'], OLD, F(cert['bound']), gain)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, default=HERE / 'certificate.json')
    parser.add_argument('--output', type=Path, default=HERE / 'independent.json')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    v, base, occ, final, oldcross = inputs(args.bundle)
    allocation_raw = gzip.decompress((HERE / 'allocation.json.gz').read_bytes())
    crossing_raw = (HERE / 'crossing.json').read_bytes()
    alloc, cross = json.loads(allocation_raw), json.loads(crossing_raw)
    cert = json.loads(args.certificate.read_bytes())
    need(cert['allocation_sha256'] == digest(allocation_raw) and cert['crossing_sha256'] == digest(crossing_raw), 'combined input bindings')
    base_path = args.bundle / 'verification_results/population-refinement/certified/population-certificate.json.gz'
    need(alloc['base_sha256'] == digest(base_path.read_bytes()), 'compressed base binding')
    ga, ra = allocation(v, base, occ, final, alloc)
    gc, rc = crossing(v, oldcross, occ, cross)
    extra_crossing = gc - F(final['additional_crossing_slack'])
    need(extra_crossing >= 0, 'crossing replacement loss')
    gain = ga + extra_crossing
    combined(v, final, cert, gain)
    tests = []
    if args.self_test:
        cases = [
            ('double occupation gain', lambda z: z.update(additional_slack=str(2 * gain))),
            ('changed target', lambda z: z.update(bound='2.935')),
            ('changed counterexample cap', lambda z: z.update(counterexample_cap='2.935')),
            ('negative endpoint coefficient', lambda z: z['endpoint_bernstein'].__setitem__(0, '-1')),
        ]
        for name, change in cases:
            bad = copy.deepcopy(cert)
            change(bad)
            try:
                combined(v, final, bad, gain)
            except ValueError:
                tests.append('rejected ' + name)
            else:
                raise ValueError('mutation accepted: ' + name)
        for name in ('over-budget allocation', 'missing region', 'inflated profile'):
            bad = copy.deepcopy(alloc)
            region = bad['replacements'][0]
            if name == 'over-budget allocation':
                region['regions'][0]['weights'][0][1] = '2'
            elif name == 'missing region':
                region['regions'].pop()
            else:
                region['bernstein'][0] = '1000'
            try:
                allocation(v, base, occ, final, bad)
            except ValueError:
                tests.append('rejected ' + name)
            else:
                raise ValueError('mutation accepted: ' + name)
        for name in ('inflated crossing', 'missing crossing', 'unsupported barrier'):
            bad = copy.deepcopy(cross)
            if name == 'inflated crossing':
                bad['crossings'][0]['bound'] = '1'
            elif name == 'missing crossing':
                bad['crossings'].pop()
            else:
                bad['barrier_series_order'] = 0
            try:
                crossing(v, oldcross, occ, bad)
            except ValueError:
                tests.append('rejected ' + name)
            else:
                raise ValueError('mutation accepted: ' + name)
    out = {'status': 'PASS', 'certified_lower_bound': cert['bound'],
           'bound_decimal': v.dec(F(cert['bound'])), 'increase_over_attachment': v.dec(F(cert['bound']) - OLD),
           'occupation_gain': str(ga), 'crossing_replacement_gain': str(extra_crossing),
           **ra, **rc, 'endpoint_identities_per_stage': 14, 'positive_endpoint_coefficients_per_stage': 14,
           'tests': tests, 'scope': 'all-duration ideal-blockade stationary-torus',
           'arithmetic': 'exact rational; no optimizer acceptance',
           'dependency': 'Complete pinned original extension chain and original global source audit.',
           'certificate_sha256': digest(args.certificate.read_bytes())}
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
