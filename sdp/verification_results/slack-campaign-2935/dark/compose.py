#!/usr/bin/env python3
"""Produce endpoint data only; verify.py performs independent acceptance."""
import argparse
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
sys.path.insert(0, str(args.bundle/'verification_results/population-refinement'))
import certify_population_subdivision as polynomial

raw = (HERE/'profiles.json').read_bytes()
profiles = json.loads(raw)
previous = json.loads((HERE.parent/'certificate.json').read_bytes())
gain = F(profiles['exact_integrated_gain'])
old, L = F(previous['bound']), F('2.9305')
power = polynomial.power_from_bernstein(list(map(F, previous['endpoint_bernstein'])))


def coefficients(bound):
    rho = (bound-L)/(old-L)
    p = [x*rho**i for i, x in enumerate(power)]
    p[0] += gain-(bound-old)
    return polynomial.bernstein_from_power(p)


scale = 10**12
lo, hi = int(old*scale), int(F(profiles['H'])*scale)+1
while lo+1 < hi:
    mid = (lo+hi)//2
    if min(coefficients(F(mid, scale))) > 0:
        lo = mid
    else:
        hi = mid
bound = F(lo, scale)
out = dict(profiles_sha256=hashlib.sha256(raw).hexdigest(), gain=str(gain),
           bound=str(bound), endpoint_bernstein=list(map(str, coefficients(bound))))
(HERE/'endpoint.json').write_text(json.dumps(out, indent=2)+'\n')
print('PRODUCED, requires independent acceptance:', str(bound), float(bound))
