#!/usr/bin/env python3
"""Exact dark-population extension; original source audit remains a prerequisite.

No new producer imports. Reconstruct signed-power tensors, rather than the
producer's separated population tensors, and check coefficient inequalities.
"""
import argparse
import copy
import gzip
import importlib.util
import json
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

from flint import fmpq as Q

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('parent_check', HERE.parent / 'verify.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
need = parent.need
REGIONAL = '4d4a9202060a9607100bf58044bacb21de2f1e99e7e3eeba5124f82170aa248e'
PREVIOUS = '106e5d046b22c8456135c40f9a77ee01f346a69c694983d917b69ab8675d830c'


def excluded(x, y, n, radius):
    # f(p,q) decreases in p and increases in q. Check both signed extrema.
    for p, q, sign in ((F(x+1, n), F(y, n), 1),
                       (F(x, n), F(y+1, n), -1)):
        a, b = (1-p)*q, 2*(1-q)*p
        gap = a+b-radius**2/2
        if sign*(a-b) > 0 and gap > 0 and gap**2 > 4*a*b:
            return True
    return False


def check(v, base, occ, regional, alloc, cert):
    need(cert['schema'] == 'minexposure/exact-dark-population-v1', 'schema')
    need(F(cert['H']) == parent.CAP, 'cap')
    owned = {e['interval_index'] for e in alloc['replacements']}
    records = base['projection_records']
    allowed = {i for e in base['integration_bins'] for i, _, _ in e['allocations']}
    seen, maps, cache = set(), {}, {}
    gain, count, dropped, budgets = F(0), 0, 0, 0
    for e in cert['profiles']:
        i, n = e['interval_index'], e['grid']
        need(type(i) is int and 0 <= i < 320 and i not in seen and i not in owned,
             'overlapping/invalid interval')
        seen.add(i)
        need(type(n) is int and n in (8, 16, 32), 'grid')
        item = base['integration_bins'][i]
        cell, a, b = item['cell'], F(item['a']), F(item['b'])
        w = v.KNOTS[cell+1]-v.KNOTS[cell]
        left, right = v.U*(v.KNOTS[cell]+w*a), v.U*(v.KNOTS[cell]+w*b)
        need(0 <= left < right < F(occ['previous_bound']), 'unguaranteed prefix')
        radius = min(right, parent.CAP-left)
        need(list(map(F, (e['cost_left'], e['cost_right'], e['R']))) ==
             [left, right, radius], 'cost interval')
        old = list(map(Q, occ['intervals'][i]['bernstein']))
        delta = list(map(Q, e['new_profile']))
        need(list(map(Q, e['old_profile'])) == old and len(delta) == 15,
             'baseline/profile shape')
        source = regional['intervals'][i]
        need(source['mode'] == 'regional', 'regional mode')
        ng = regional['grid']
        regions = {(r['x'], r['y']): r for r in source['regions']}
        need(set(regions) == {(x, y) for x in range(ng) for y in range(ng)}, 'cover')
        tensors = {}
        drops = 0
        for x in range(n):
            for y in range(n):
                if excluded(x, y, n, radius):
                    drops += 1
                    continue
                key = (x*ng//n, y*ng//n)
                if key not in tensors:
                    groups, checks, _ = v.region_weights(regions[key], records, allowed, cell)
                    budgets += checks
                    tensors[key] = v.affine(14, a, b)*v.tensor(groups, cache)
                if (x, y, n) not in maps:
                    maps[x, y, n] = v.popmap(7, x, y, n)
                pop, costs = maps[x, y, n]
                values = tensors[key]*pop
                for k in range(15):
                    for j, c in enumerate(costs):
                        need(values[k, j] >= delta[k]*c, 'population coefficient')
                        count += 1
        need(drops == e['discarded_boxes'] and n*n-drops == e['retained_boxes'] > 0,
             'exclusion counts')
        increment = (right-left)*F(str((sum(delta)-sum(old))/15))
        need(increment == F(e['integrated_gain']) and increment > 0, 'interval gain')
        gain += increment
        dropped += drops
    need(seen and gain == F(cert['exact_integrated_gain']), 'total gain')
    return gain, dict(intervals=len(seen), coefficients=count, excluded_boxes=dropped,
                      gram_budget_checks=budgets)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    subprocess.run([sys.executable, str(HERE.parent/'verify.py'), '--bundle',
                    str(args.bundle), '--self-test'], check=True)
    v, base, occ, _, _ = parent.inputs(args.bundle)
    previous = parent.pinned(HERE.parent/'certificate.json', PREVIOUS)
    raw = (args.bundle/'verification_results/adaptive-slack/certified/certificate.json.gz').read_bytes()
    need(parent.digest(raw) == REGIONAL, 'regional binding')
    regional = json.loads(gzip.decompress(raw))
    alloc = json.loads(gzip.decompress((HERE.parent/'allocation.json.gz').read_bytes()))
    cert = json.loads((HERE/'profiles.json').read_bytes())
    gain, stats = check(v, base, occ, regional, alloc, cert)
    endpoint = json.loads((HERE/'endpoint.json').read_bytes())
    need(endpoint['profiles_sha256'] == parent.digest((HERE/'profiles.json').read_bytes()), 'profile binding')
    need(F(endpoint['gain']) == gain, 'endpoint gain')
    parent.endpoint(v, endpoint['endpoint_bernstein'], previous['endpoint_bernstein'],
                    F(previous['bound']), F(endpoint['bound']), gain)
    tests = []
    if args.self_test:
        # Strict equality must be retained; asymmetric boxes exercise both signs.
        need(not excluded(0, 0, 16, F(0)), 'zero diagonal')
        need(excluded(0, 15, 16, F(1)), 'positive corner')
        need(excluded(15, 0, 16, F(1)), 'negative corner')
        need(not excluded(0, 15, 16, F(2)), 'large radius')
        # At (p,q)=(1/7,3/7), sqrt(A)-sqrt(B)=sqrt(2)/7.
        # Thus the exact limiting radius is 2/7, not a numerical estimate.
        need(not excluded(0, 3, 7, F(2, 7)), 'strict boundary retained')
        need(excluded(0, 3, 7, F(2, 7)-F(1, 10**30)), 'below boundary')
        need(not excluded(0, 3, 7, F(2, 7)+F(1, 10**30)), 'above boundary')
        for name in ('overlap', 'inflated profile', 'wrong prefix'):
            bad = copy.deepcopy(cert)
            e = bad['profiles'][0]
            if name == 'overlap':
                e['interval_index'] = next(iter({r['interval_index'] for r in alloc['replacements']}))
            elif name == 'inflated profile':
                e['new_profile'][0] = '1000'
            else:
                e['cost_right'] = '3'
            try:
                check(v, base, occ, regional, alloc, bad)
            except ValueError:
                tests.append('rejected '+name)
            else:
                raise ValueError('accepted mutation: '+name)
    out = dict(status='PASS', bound=endpoint['bound'], bound_decimal=v.dec(F(endpoint['bound'])),
               exact_gain=str(gain), **stats, tests=tests,
               dependency='Original global source audit and complete pinned predecessor chain; source audit not rerun.')
    (HERE/'independent.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
