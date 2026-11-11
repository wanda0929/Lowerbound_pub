"""Exact, factorized checks of the three pinned tensor_identity contracts.

Inputs are fresh *DataAudit.lean dumps, not producer polynomial evaluations.
Expand every allocated Gram modulo QuotientNormalForm.relations, compare its
population polynomial, and verify the Bernstein change of basis coefficient
by coefficient for every interval used. Linearity then covers every weighted
region, profile and interface box without expanding repeated large sums.
This is an external rational check, not a Lean proof term. Source drift/jump
identities and correspondence to the separate sign checker are not claimed.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from math import comb
from pathlib import Path

import flint
from flint import fmpq as Q, fmpq_mat as Mat
from bind_certificates import need

ZERO = (0,) * 11


def add(p, e, c):
    p[e] = p.get(e, Q(0)) + c
    if not p[e]:
        del p[e]


def normalize(e):
    """Exactly normalTerm: u*u_bar=1, g*g_bar=1-r*r_bar."""
    e = list(e)
    for a in (1, 3, 7):
        n = min(e[a], e[a+1])
        e[a] -= n
        e[a+1] -= n
        if a == 3:
            g = n
        elif a == 7:
            h = n
    out = {}
    for i in range(g+1):
        for j in range(h+1):
            f = e.copy()
            f[5] += i; f[6] += i
            f[9] += j; f[10] += j
            add(out, tuple(f), Q((-1)**(i+j)*comb(g, i)*comb(h, j)))
    return out


def powers(code):
    need(code >= 0 and code//2 < 16**11, "column code range")
    return tuple(code//2//16**i % 16 for i in range(11))


def gram(columns, matrix, localizer):
    """Full conjugate-left Gram; coefficients live in Q(i)."""
    real, imag = {}, {}
    loc = ((1,), (0, 1), (1, -1), (0, 1, -1))[localizer]
    for i, left in enumerate(columns):
        for j, right in enumerate(columns):
            q = matrix[i][j]
            if not q:
                continue
            for code, c in left:
                a = powers(code)
                a = (a[0],) + tuple(a[k+1] if k % 2 else a[k-1] for k in range(1, 11))
                for other, d in right:
                    phase = (other % 2 - code % 2) % 4
                    out = real if phase % 2 == 0 else imag
                    sign = 1 if phase in (0, 1) else -1
                    b = powers(other)
                    for k, v in enumerate(loc):
                        if v:
                            e = tuple(a[t]+b[t]+(k if t == 0 else 0) for t in range(11))
                            for f, z in normalize(e).items():
                                add(out, f, q*c*d*sign*v*z)
    need(not imag, "imaginary Gram residual")
    return real


def population(poly, ex):
    g, r, h, s = ex
    need(min(ex) >= 0 and g+r <= 7 and h+s <= 7 and len(poly) <= 15, "tensor degree")
    result = {}
    for k, c in enumerate(poly):
        for i in range(g+1):
            for j in range(h+1):
                e = [0]*11
                e[0], e[5], e[6], e[9], e[10] = k, r+i, r+i, s+j, s+j
                add(result, tuple(e), c*(-1)**(i+j)*comb(g, i)*comb(h, j))
    return result


@lru_cache(None)
def affine(n, a, b):
    """Lean affineCoefficient, checked against an independent expansion of B_i.

    B[k,i] is the x^k coefficient of choose(n,i)*((x-a)/(b-a))^i
    *((b-x)/(b-a))^(n-i). B*A=I checks every power, not point samples.
    """
    a, b = Q(a), Q(b)
    need(a < b, "positive box width")
    A = Mat([[sum((Q(comb(p,l)*comb(i,l), comb(n,l))*a**(p-l)*(b-a)**l
                   for l in range(min(i,p)+1)), Q(0)) for p in range(n+1)] for i in range(n+1)])
    B = Mat(n+1, n+1)
    for i in range(n+1):
        for u in range(i+1):
            for v in range(n-i+1):
                B[u+v,i] += (comb(n,i)*comb(i,u)*comb(n-i,v)*(-a)**(i-u)*
                             b**(n-i-v)*(-1)**v/(b-a)**n)
    need(B*A == Mat([[int(i == j) for j in range(n+1)] for i in range(n+1)]),
         "Bernstein polynomial identity")
    need(all(A[i,0] == 1 and A[i,1] == a+(b-a)*Q(i,n) for i in range(n+1)),
         "partition of unity and linear cost coefficients")
    return A, B


def pairs(line):
    return [(int(t.split(':')[0]), Q(t.split(':')[1])) for t in line.split()]


def read_occupation(path, regional):
    sources, projections, groups, maps, regions, profiles = [], [], [], [], [], []
    with path.open() as f:
        def fields(tag, index):
            row = f.readline().split()
            need(row[:2] == [tag, str(index)], f"decode order {tag}/{index}")
            return row[2:]
        for i in range(3680 if regional else 736):
            n, loc = map(int, fields('S', i))
            basis = list(map(int, f.readline().split() if regional else fields('B', i)))
            rows = [pairs(x) for x in f.readline().strip().split('|')] if regional else []
            if not regional:
                rows = []
                for j in range(n):
                    row = fields('C', i)
                    need(row[0] == str(j), "facial row index")
                    rows.append(pairs(' '.join(row[1:])))
            f.readline()  # Original Q is irrelevant to the allocated identity.
            need(len(rows) == n, "facial shape")
            sources.append((loc, [[(basis[k], c) for k,c in row] for row in rows]))
        for i in range(6190 if regional else 1078):
            rid, block = map(int, fields('P', i))
            if regional:
                rows = list(map(int, f.readline().split()))
                matrix = list(map(Q, f.readline().split()))
                poly = list(map(Q, f.readline().split()))
                ex = list(map(int, f.readline().split()))
            else:
                rows = list(map(int, fields('R', i)))
                matrix = list(map(Q, fields('M', i)))
                ex = list(map(int, fields('E', i)))
                poly = list(map(Q, fields('F', i)))
            need(len(matrix) == len(rows)**2 and len(ex) == 4 and len(set(rows)) == len(rows), "projection shape")
            projections.append((block, rows, matrix, poly, ex))
        pending = f.readline()
        while pending.startswith('G '):
            tag, idx, *values = pending.split()
            need(int(idx) == len(groups), "group order")
            groups.append(pairs(f.readline() if regional else ' '.join(values)))
            pending = f.readline()
        while pending.startswith('M ' if regional else 'A '):
            _, idx, *values = pending.split()
            need(int(idx) == len(maps), "map order")
            maps.append(list(map(int, f.readline().split() if regional else values)))
            pending = f.readline()
        if regional:
            while pending.startswith('R '):
                _, idx, *values = pending.split()
                need(int(idx) == len(regions), "region order")
                regions.append(tuple(map(int, values)))
                pending = f.readline()
        while pending.startswith('D '):
            _, idx, *values = pending.split()
            need(int(idx) == len(profiles), "profile order")
            if regional:
                cell, a, b = values
                profiles.append((int(cell), Q(a), Q(b), list(map(Q, f.readline().split()))))
            else:
                profiles.append((2, Q(48+int(idx),64), Q(49+int(idx),64), list(map(Q, values))))
            pending = f.readline()
        need(pending.startswith('T '), "missing audit trailer")
    if not regional:
        regions = [(i//64, i, i%64//8, i%8, 8) for i in range(1024)]
    need(len(regions) == (9728 if regional else 1024), "all regions")
    return sources, projections, groups, maps, regions, profiles


def occupation(path, regional):
    sources, projections, groups, maps, regions, profiles = read_occupation(path, regional)
    for cell, a, b, delta in profiles:
        need(0 <= cell < 5 and len(delta) == 15, "profile shape")
        A, B = affine(14, str(a), str(b))
        d = Mat([[v] for v in delta])
        need(A*(B*d) == d, "profile polynomial round trip")
    owners = {}
    for pi, mi, x, y, n in regions:
        cell, a, b, delta = profiles[pi]
        need(len(delta) == 15 and 0 <= x < n and 0 <= y < n, "profile/box shape")
        affine(14, str(a), str(b))
        affine(7, str(Q(x,n)), str(Q(x+1,n)))
        affine(7, str(Q(y,n)), str(Q(y+1,n)))
        need(len(maps[mi]) == 736, "map length")
        for block, gi in enumerate(maps[mi]):
            for p, w in groups[gi]:
                need(projections[p][0] == block, "projection block ownership")
                old = owners.setdefault(p, cell)
                need(old == cell, "projection cell ownership")
    need(set(owners) == set(range(len(projections))), "all projections used")
    for p, (block, rows, matrix, poly, ex) in enumerate(projections):
        loc, columns = sources[owners[p]*736+block if regional else block]
        m = len(rows)
        actual = gram([columns[i] for i in rows], [matrix[i*m:(i+1)*m] for i in range(m)], loc)
        need(actual == population(poly, ex), f"normalized allocated Gram {p}")
    # The residual definition is a weighted sum of projectionCoefficient minus
    # delta[k0]*costCoefficient. The checked basis inverses establish the former
    # term for every projection; degree elevation of linear p1/2+p2/4 establishes
    # the latter. Bernstein partition of unity supplies the two unused axes.
    return dict(regions=len(regions), projections=len(projections),
                tensor_identities=len(regions), method="all Gram expansions and all interval basis identities; linearity")


def interfaces(path):
    with path.open() as f:
        def fields(tag, i):
            row = f.readline().split()
            need(row[:2] == [tag, str(i)], "interface decode order")
            return row[2:]
        totals = [{} for _ in range(4)]
        for j in range(4):
            for i in range(j*134, (j+1)*134):
                n, = map(int, fields('S', i))
                codes = list(map(int, fields('B', i)))
                fields('Q', i)
                diag = list(map(Q, fields('D', i)))
                need(len(codes) == len(diag) == n, "interface shape")
                for code, weight in zip(codes, diag):
                    if weight:
                        need(code % 2 == 0, "interface column phase")
                        for e, c in gram([[(code, Q(1))]], [[weight]], 0).items():
                            add(totals[j], e, c)
            p = list(map(Q, fields('P', j)))
            credit, = map(Q, fields('K', j))
            need(len(p) == 64, "interface power shape")
            expected = {}
            for a in range(8):
                for b in range(8):
                    e = list(ZERO)
                    e[5] = e[6] = a
                    e[9] = e[10] = b
                    add(expected, tuple(e), p[a*8+b])
            need(totals[j] == expected, f"interface allocated polynomial {j}")
    for i in range(64):
        affine(7, str(Q(i,64)), str(Q(i+1,64)))
    return dict(blocks=536, tensor_identities=4*64*64,
                method="full diagonal Gram expansions; all box basis identities; constant credit by partition of unity")


def controls():
    # i*g*r has |.|²=(1-p)*p, not its negative or p alone.
    e = list(ZERO); e[3] = e[5] = 1
    code = 2*sum(x*16**i for i,x in enumerate(e))+1
    actual = gram([[(code, Q(1))]], [[Q(2)]], 2)
    expected = population([Q(2), Q(-2)], [1,1,0,0])
    need(actual == expected, "conjugation/localizer positive control")
    need(actual != population([Q(-2), Q(2)], [1,1,0,0]), "phase sign negative control")
    need(actual != population([Q(2)], [1,1,0,0]), "missing localizer negative control")
    need(actual != population([Q(2), Q(-2)], [0,1,0,0]), "missing normalization negative control")
    r = 2*16**5
    full = gram([[(r,Q(1))], [(r+2,Q(1))]], [[Q(2),Q(1)],[Q(1),Q(3)]], 0)
    need(full == population([Q(2),Q(2),Q(3)], [0,1,0,0]), "off-diagonal positive control")
    need(full != population([Q(2),Q(0),Q(3)], [0,1,0,0]), "omitted off-diagonal negative control")
    u = 2*(16**1+16**5)
    need(gram([[(u,Q(1))]], [[Q(1)]], 0) == population([Q(1)], [0,1,0,0]),
         "control-circle normalization")
    A, B = affine(7, '2/9', '5/8')
    bad = Mat(A); bad[3,5] += 1
    need(B*bad != B*A, "changed interior coefficient negative control")
    need(B*A.transpose() != B*A, "transposed tensor convention negative control")
    return ["wrong phase sign", "missing localizer", "missing normalization",
            "omitted off-diagonal", "changed interior Bernstein coefficient", "transposed conversion"]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--allocation', type=Path, required=True)
    p.add_argument('--regional', type=Path, required=True)
    p.add_argument('--interface', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    a = p.parse_args()
    report = dict(status='PASS', python_flint=flint.__version__, negative_controls=controls())
    for name in ('allocation', 'regional', 'interface'):
        path = getattr(a, name)
        report[name] = interfaces(path) if name == 'interface' else occupation(path, name == 'regional')
        report[name]['decoded_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        print('PASS:', name, report[name], flush=True)
    report['basis_changes_checked'] = affine.cache_info().currsize
    report['source_identity_checked'] = False
    report['exhaustive_Lean_residual_evaluation'] = False
    report['trust_boundary'] = 'external exact algebra and decoder execution; no new kernel certificate instance'
    files = [Path(__file__), Path('LowerBoundCZ/SlackAllocation.lean'),
             Path('LowerBoundCZ/AllocationCodec.lean')]
    for stem in ('QuotientNormalForm', 'QuotientCertificate', 'Hierarchy'):
        files.append(Path('appendix-e/RequestProject/AppendixE/'+stem+'.lean'))
    for stem in ('Allocation', 'Regional', 'Interface'):
        files.append(Path(stem+'DataAudit.lean'))
    for stem in ('Allocations', 'Regions', 'Interfaces'):
        files.append(Path('LowerBoundCZ/Pinned'+stem+'.lean'))
    report['definitions_sha256'] = {str(f): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
    a.report.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
