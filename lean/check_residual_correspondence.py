"""Compare every fixed residual coefficient with the pinned sign checker.

The Lean side is evaluated compositionally: actual Lean primitive tables plus
the fully decoded weights, polynomials, profiles and boxes. Only distributivity
and finite-sum regrouping are used to avoid repeating the huge literal residual
sum. This is external exact arithmetic, not a kernel theorem or direct execution
of residual at every index. No coefficient or retained box is sampled.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import flint
from flint import fmpq as Q, fmpq_mat as Mat
from bind_allocations import load_checker
from bind_regions import module
from bind_certificates import need
from check_allocated_identities import read_occupation


def factors(path, verifier):
    E,A,P,C = {},{},{},{}
    exposure_records = 0
    with path.open() as f:
        for line in f:
            tag,*s = line.split()
            if tag == 'E':
                i,a,b,*values = s
                need(int(i) == exposure_records, 'exposure factor order')
                exposure_records += 1
                need(len(values) == 225, 'exposure factor shape')
                a,b = Q(a),Q(b)
                values = list(map(Q,values))
                m = Mat(15,15,values)
                need(m == verifier.affine(14,F(str(a)),F(str(b))), 'all exposure factors')
                if (a,b) in E:
                    need(E[a,b] == m, 'duplicate exposure interval')
                E[a,b] = m
            elif tag == 'A':
                n,x = map(int,s[:2]); values = list(map(Q,s[2:]))
                need((n,x) not in A and len(values) == 64, 'affine factor shape/uniqueness')
                m = Mat(8,8,values)
                need(m == verifier.affine(7,F(x,n),F(x+1,n)), 'all population-axis affine factors')
                A[n,x] = m
            elif tag == 'P':
                key = tuple(map(int,s[:4])); values = list(map(Q,s[4:]))
                need(key not in P and len(values) == 8, 'population factor shape/uniqueness')
                P[key] = values
            elif tag == 'C':
                kind = s[0]; n,x,y = map(int,s[1:4]); values = list(map(Q,s[4:]))
                key = (kind,n,x,y)
                need(key not in C and len(values) == 64, 'cost factor shape/uniqueness')
                need(values == verifier.popmap(7,x,y,n)[1], 'all cost factors')
                C[key] = values
            else:
                raise ValueError('unknown factor tag '+tag)
    need(exposure_records == 321, 'all exposure profiles')
    need(set(A) == {(n,x) for n in (4,8,16,64) for x in range(n)}, 'all affine axes')
    need(set(P) == {(n,x,g,e) for n in (4,8,16) for x in range(n)
                    for g in range(8) for e in range(8-g)}, 'all population factors')
    return E,A,P,C


def compare(lean, external, nonnegative, label):
    need(lean == external, 'residual mismatch: '+label)
    minimum = None
    if nonnegative:
        for row in lean.tolist():
            for value in row:
                need(value >= 0, 'negative coefficient: '+label)
                minimum = value if minimum is None else min(minimum,value)
    return minimum


def occupation(path, regional, tables, v):
    _,projections,groups,maps,regions,profiles = read_occupation(path,regional)
    E,A,P,C = tables
    kind = 'regional' if regional else 'allocation'
    # Regroup the exact decoded finite sum by population powers. The exposure
    # coefficient is linear in p.polynomial, so this preserves every weight.
    grouped, tensors, population_cache = {},{},{}
    map_cells, projection_cells = {},{}
    for pi,mi,_,_,_ in regions:
        cell = profiles[pi][0]
        need(map_cells.setdefault(mi,cell) == cell, 'map cell ownership')
        for gi in maps[mi]:
            for p,_ in groups[gi]:
                need(projection_cells.setdefault(p,cell) == cell, 'projection cell ownership')
    records = [dict(cell=projection_cells[i],block=p[0],population_exponents=p[4],
                    polynomial=list(map(str,p[3]))) for i,p in enumerate(projections)]
    allowed = set(range(len(records)))
    for mi,mapping in enumerate(maps):
        by_ex = {}
        weights = []
        for block,gi in enumerate(mapping):
            for pi,w in groups[gi]:
                weights.append([pi,str(w)])
                owner,_,_,poly,ex = projections[pi]
                need(owner == block, 'original block ownership')
                out = by_ex.setdefault(tuple(ex),[Q(0)]*15)
                for k,c in enumerate(poly):
                    out[k] += w*c
        exponents = sorted(by_ex)
        grouped[mi] = (exponents,Mat([[by_ex[ex][k] for ex in exponents] for k in range(15)]))
        external_groups,_,_ = v.region_weights({'weights':weights},records,allowed,map_cells[mi])
        need(external_groups == by_ex, 'independent allocation grouping')
        tensors[mi] = v.tensor(external_groups,population_cache)
    cache = {}
    external_populations = {}
    minimum = None
    for ri,(pi,mi,x,y,n) in enumerate(regions):
        _,a,b,delta = profiles[pi]
        exponents,coeff = grouped[mi]
        if (pi,mi) not in cache:
            cache[pi,mi] = (E[a,b]*coeff, v.affine(14,F(str(a)),F(str(b)))*tensors[mi])
        left,right = cache[pi,mi]
        # This path uses Lean populationCoefficient, not the external tensor's
        # expansion (1-p)^g*p^e or its power-to-Bernstein population matrix.
        pop = Mat([[P[n,x,g,r][i]*P[n,y,h,s][j] for i in range(8) for j in range(8)]
                   for g,r,h,s in exponents])
        lc = Mat([C[kind,n,x,y]])
        if (n,x,y) not in external_populations:
            external_populations[n,x,y] = v.popmap(7,x,y,n)
        ep,ec = external_populations[n,x,y]
        d = Mat([[q] for q in delta])
        lean = left*pop-d*lc
        external = right*ep-d*Mat([ec])
        low = compare(lean,external,True,f'{kind}/{ri}')
        minimum = low if minimum is None else min(minimum,low)
        if ri%512 == 0:
            print(f'CHECKED {kind} {ri}/{len(regions)}',flush=True)
    count = len(regions)*15*8*8
    return dict(regions=len(regions),coefficients_compared=count,nonnegative_coefficients=count,
                minimum=str(minimum))


def interfaces(path,tables,v):
    powers,credits,bits = {},{},{}
    for line in path.open():
        tag,*s = line.split()
        if tag == 'P':
            powers[int(s[0])] = list(map(Q,s[1:]))
        elif tag == 'K':
            credits[int(s[0])] = Q(s[1])
        elif tag == 'X':
            bits[int(s[0])] = s[1]
    need(set(powers) == set(credits) == set(bits) == set(range(4)), 'four interfaces')
    need(all(len(p) == 64 for p in powers.values()) and
         all(len(s) == 4096 and set(s) <= {'0','1'} for s in bits.values()), 'interface shapes')
    _,A,_,_ = tables
    matrix = {j:Mat(8,8,powers[j]) for j in range(4)}
    compared = signed = 0
    minimum = None
    for x in range(64):
        left = {j:A[64,x]*matrix[j] for j in range(4)}
        for y in range(64):
            ep,_ = v.popmap(7,x,y,64)
            for j in range(4):
                values = left[j]*A[64,y].transpose()
                lean = Mat([[values[i,k]-credits[j] for i in range(8) for k in range(8)]])
                external = Mat([powers[j]])*ep-Mat([[credits[j]]*64])
                retained = bits[j][x*64+y] == '0'
                low = compare(lean,external,retained,f'interface/{j}/{x}/{y}')
                compared += 64
                if retained:
                    signed += 64
                    minimum = low if minimum is None else min(minimum,low)
        if x%8 == 0:
            print(f'CHECKED interface x={x}/64',flush=True)
    need(signed == 615296, 'all retained interface coefficients')
    return dict(boxes=4*64*64,coefficients_compared=compared,nonnegative_coefficients=signed,
                minimum=str(minimum),excluded_boxes_compared_but_not_required_nonnegative=True)


def controls(tables):
    E,A,P,C = tables
    good = Mat([P[8,2,3,1]])
    bad = Mat(good); bad[0,5] += Q(1,10**40)
    correct_cost = Mat([C['allocation',8,2,5]])
    wrong_cost = Mat([[Q(2*7+i,4*8*7)+Q(5*7+j,2*8*7) for i in range(8) for j in range(8)]])
    rejected = []
    for name,wrong,right in [
        ('interior coefficient perturbation',bad,good),
        ('transposed affine axes',A[8,2].transpose(),A[8,2]),
        ('swapped cost-sector weights',wrong_cost,correct_cost)]:
        try:
            compare(wrong,right,False,name)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('accepted control '+name)
    try:
        compare(Mat([[-Q(1,10**40)]]),Mat([[-Q(1,10**40)]]),True,'tiny negative')
    except ValueError:
        rejected.append('equal but negative coefficient')
    else:
        raise ValueError('accepted negative coefficient')
    return rejected


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('checkout',type=Path)
    for name in ('allocation','regional','interface','factors','report'):
        p.add_argument('--'+name,type=Path,required=True)
    a = p.parse_args()
    load_checker(a.checkout)  # Require the pinned revision and unchanged checker tree.
    external_path = a.checkout/'sdp/verification_results/adaptive-slack/verify.py'
    v = module(external_path,'residual_sign_verifier')
    prior = json.loads(Path('source-identities.json').read_text())
    for name in ('allocation','regional','interface'):
        need(hashlib.sha256(getattr(a,name).read_bytes()).hexdigest() == prior['decoded_sha256'][name],
             'previously bound decoded input '+name)
    for name,h in prior['definitions_sha256'].items():
        need(hashlib.sha256(Path(name).read_bytes()).hexdigest() == h, 'source definition drift '+name)
    tables = factors(a.factors,v)
    report = dict(status='PASS',python_flint=flint.__version__,negative_controls=controls(tables))
    report['allocation'] = occupation(a.allocation,False,tables,v)
    report['regional'] = occupation(a.regional,True,tables,v)
    report['interface'] = interfaces(a.interface,tables,v)
    report['method'] = 'complete compositional residual evaluation from Lean primitive tables; exact finite-sum regrouping'
    report['direct_Lean_residual_execution_at_every_index'] = False
    report['kernel_proof_term'] = False
    paths = [Path(__file__),Path('ResidualFactorsAudit.lean'),Path('source-identities.json'),
             Path('check_allocated_identities.py'),external_path,a.factors,a.allocation,a.regional,a.interface]
    report['sha256'] = {str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    a.report.write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: all residual coefficients compared; all required signs checked',flush=True)


if __name__ == '__main__':
    main()
