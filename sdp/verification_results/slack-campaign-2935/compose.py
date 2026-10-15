#!/usr/bin/env python3
"""Compose disjoint proved increments; verify.py must accept the result."""
import argparse
import gzip
import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bundle', type=Path, required=True)
args = parser.parse_args()
root = args.bundle / 'verification_results'
sys.path.insert(0, str(root / 'population-refinement'))
import certify_population_subdivision as polynomial

allocation_raw = gzip.decompress((HERE / 'allocation.json.gz').read_bytes())
crossing_raw = (HERE / 'crossing.json').read_bytes()
allocation, crossing = json.loads(allocation_raw), json.loads(crossing_raw)
previous = json.loads((root / 'reachability-slack/certified/certificate.json').read_bytes())
gain = F(allocation['additional_occupation_slack']) + F(crossing['additional_crossing_slack']) - F(previous['additional_crossing_slack'])
old, L, cap = F(previous['bound']), F('2.9305'), F(previous['counterexample_cap'])
power = polynomial.power_from_bernstein(list(map(F, previous['endpoint_bernstein'])))


def coefficients(bound):
    rho = (bound - L) / (old - L)
    p = [x * rho**i for i, x in enumerate(power)]
    p[0] += gain - (bound - old)
    return polynomial.bernstein_from_power(p)


scale = 10**12
lo, hi = int(old * scale), int(cap * scale) + 1
while lo + 1 < hi:
    mid = (lo + hi) // 2
    if min(coefficients(F(mid, scale))) > 0:
        lo = mid
    else:
        hi = mid
bound = F(lo, scale)
out = {'schema': 'minexposure/disjoint-slack-campaign-v1',
       'allocation_sha256': hashlib.sha256(allocation_raw).hexdigest(),
       'crossing_sha256': hashlib.sha256(crossing_raw).hexdigest(),
       'previous_bound': str(old), 'counterexample_cap': str(cap), 'additional_slack': str(gain),
       'bound': str(bound), 'endpoint_bernstein': list(map(str, coefficients(bound)))}
(HERE / 'certificate.json').write_text(json.dumps(out, indent=2) + '\n')
print('PRODUCED (requires exact acceptance):', bound, float(bound))
