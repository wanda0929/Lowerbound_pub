"""Direct exact source_identity replay from Lean-decoded original data.

Sparse polynomials have coefficients in Q(sqrt(2), i), represented by four
rational components. No PSD result or archived zero-residual assertion is used.
The comparison is modulo the three Lean normalization relations, not equality
at sampled trajectories. This external checker does not produce proof terms.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import flint
from flint import fmpq as Q
from bind_certificates import need
from check_allocated_identities import normalize, powers, pairs

ZERO = (0,)*11


def add(p, e, component, c):
    if c:
        key = (e, component)
        p[key] = p.get(key, Q(0)) + c
        if not p[key]:
            del p[key]


def times_component(k, l):
    # Components 0,1,2,3 mean 1,sqrt(2),i,i*sqrt(2).
    return k ^ l, (-1 if k & l & 2 else 1)*(2 if k & l & 1 else 1)


def multiply(p, q):
    result = {}
    for (a,k), c in p.items():
        for (b,l), d in q.items():
            m, sign = times_component(k,l)
            add(result, tuple(x+y for x,y in zip(a,b)), m, c*d*sign)
    return result


@lru_cache(maxsize=65536)
def normal(e):
    return tuple(normalize(e).items())


def reduced(p):
    result = {}
    for (e,k), c in p.items():
        for f,d in normal(e):
            add(result,f,k,c*d)
    return result


def variable(i, c=Q(1), component=0):
    e = list(ZERO); e[i] = 1
    return {(tuple(e),component): c}


def combine(*terms):
    result = {}
    for weight, p in terms:
        for (e,k), c in p.items():
            add(result,e,k,weight*c)
    return result


def vector_field():
    """Translate Hierarchy.fpoly through encodeCoordinate, independently of
    the compact complex Hamiltonian formula used as a cross-check below.
    """
    re = lambda i: combine((Q(1,2), variable(i)), (Q(1,2), variable(i+1)))
    im = lambda i: combine((Q(-1,2), variable(i,component=2)),
                          (Q(1,2), variable(i+1,component=2)))
    a,b = re(1),im(1)
    x = [v for i in (3,5,7,9) for v in (re(i),im(i))]
    f = []
    for start, root in ((0,0),(4,1)):
        g,h,r,s = x[start:start+4]
        real_imag = [combine((1,multiply(a,s)),(1,multiply(b,r))),
                     combine((-1,multiply(a,r)),(1,multiply(b,s))),
                     combine((1,multiply(a,h)),(-1,multiply(b,g))),
                     combine((-1,multiply(a,g)),(-1,multiply(b,h)))]
        scale = {(ZERO,root):Q(1,2)}
        for u,v in ((0,1),(2,3)):
            real = multiply(scale,real_imag[u])
            imag = multiply(multiply(scale,{(ZERO,2):Q(1)}),real_imag[v])
            f.extend([combine((1,real),(1,imag)), combine((1,real),(-1,imag))])
    # Coordinates 3..10 are g1,g1bar,r1,r1bar,g2,g2bar,r2,r2bar.
    for j,(u,z,sign,root) in enumerate(((1,5,-1,0),(2,6,1,0),(2,3,-1,0),(1,4,1,0),
                                       (1,9,-1,1),(2,10,1,1),(2,7,-1,1),(1,8,1,1))):
        e = list(ZERO); e[u] = e[z] = 1
        need(f[j] == {(tuple(e),2+root):Q(sign,2)}, "real-to-complex vector field")
    cost = combine((Q(1,2),combine((1,multiply(x[2],x[2])),(1,multiply(x[3],x[3])))),
                   (Q(1,4),combine((1,multiply(x[6],x[6])),(1,multiply(x[7],x[7])))))
    need(cost == combine((Q(1,2),multiply(variable(5),variable(6))),
                         (Q(1,4),multiply(variable(9),variable(10)))), "embedded cpoly")
    return f, cost


def potentials(path):
    with path.open() as f:
        basis = []
        for i in range(776):
            row = f.readline().split()
            need(row[:2] == ['B',str(i)] and len(row) == 11, "potential basis record")
            d,*ex = map(int,row[2:])
            a,h = ex[:4],ex[4:]
            e = (d,0,0)+tuple(v for pair in zip(h,a) for v in pair)
            partner = (d,0,0)+tuple(v for pair in zip(a,h) for v in pair)
            basis.append((e,partner))
        result = []
        for cell in range(5):
            p = {}
            for i,(e,partner) in enumerate(basis):
                row = f.readline().split()
                need(row[:2] == ['C',str(cell*776+i)] and len(row) == 4, "potential coefficient record")
                for k,c in enumerate(map(Q,row[2:])):
                    # V=-sum lambda*Re(m), with no doubling of representatives.
                    add(p,e,k,-c/2); add(p,partner,k,-c/2)
            result.append(p)
        need(f.read() == '', "extra potential records")
    return result


def derivative(p, i):
    result = {}
    for (e,k), c in p.items():
        if e[i]:
            f = list(e); f[i] -= 1
            add(result,tuple(f),k,c*e[i])
    return result


def drift(p, kappa, field, cost):
    terms = [(1,cost),(-kappa,multiply(cost,derivative(p,0)))]
    terms.extend((-1,multiply(derivative(p,i+3),f)) for i,f in enumerate(field))
    return reduced(combine(*terms))


def at_xi(p, t):
    result = {}
    for (e,k), c in p.items():
        add(result,(0,)+e[1:],k,c*t**e[0])
    return result


def gram_add(result, columns, entries, loc):
    """Expand upper triangular real Q(sqrt(2)) into the full Hermitian form."""
    localizer = ((1,), (0,1), (1,-1), (0,1,-1))[loc]
    columns = [[(powers(code),code%2,c) for code,c in row] for row in columns]
    index = 0
    for i,left in enumerate(columns):
        for j in range(i,len(columns)):
            q = entries[index]; index += 1
            if not any(q):
                continue
            for a,pa,c in left:
                for b,pb,d in columns[j]:
                    directions = [(a,pa,b,pb)] if i == j else [(a,pa,b,pb),(b,pb,a,pa)]
                    for x,px,y,py in directions:
                        x = (x[0],)+tuple(x[t+1] if t%2 else x[t-1] for t in range(1,11))
                        e = tuple(v+w for v,w in zip(x,y))
                        phase = (py-px)%4
                        sign = 1 if phase in (0,1) else -1
                        for shift,w in enumerate(localizer):
                            if w:
                                f = (e[0]+shift,)+e[1:]
                                for root,value in enumerate(q):
                                    add(result,f,root+2*(phase%2),value*c*d*sign*w)
    need(index == len(entries), "source matrix shape")


def occupation(path, expected):
    outcomes = []
    with path.open() as f:
        for cell in range(5):
            total = {}
            for b in range(736):
                row = f.readline().split()
                need(row[:2] == ['S',str(cell*736+b)], "regional source order")
                n,loc = map(int,row[2:])
                basis = list(map(int,f.readline().split()))
                rows = [pairs(x) for x in f.readline().strip().split('|')]
                entries = [tuple(map(Q,v.split(','))) for v in f.readline().split()]
                need(len(rows) == n and len(entries) == n*(n+1)//2, "source shape")
                gram_add(total,[[(basis[k],c) for k,c in r] for r in rows],entries,loc)
                if b%128 == 0:
                    print(f'EXPANDED cell {cell}, block {b}, raw components {len(total)}',flush=True)
            actual = reduced(total)
            residual = combine((1,expected[cell]),(-1,actual))
            need(not residual, f"occupation source_identity {cell}: {len(residual)} nonzero components; first={next(iter(residual.items()), None)}")
            outcomes.append(dict(cell=cell,blocks=736,normal_components=len(actual),nonzero_residuals=0))
            print('PASS: occupation',cell,flush=True)
    return outcomes


def allocation_matches(allocation, regional):
    """The replacement API uses its own 736 blocks; check them, not just
    the regional copy of cell 2. Compare every full matrix entry as well.
    """
    with allocation.open() as a, regional.open() as r:
        for _ in range(2*736*4):
            need(r.readline() != '', "truncated regional source")
        for b in range(736):
            tag, idx, n, loc = a.readline().split()
            need((tag,idx) == ('S',str(b)), "replacement source order")
            need(r.readline().split() == ['S',str(2*736+b),n,loc], "replacement source shape/localizer")
            n = int(n)
            row = a.readline().split()
            need(row[:2] == ['B',str(b)] and row[2:] == r.readline().split(), "replacement basis")
            rows = r.readline().strip().split('|')
            need(len(rows) == n, "replacement facial shape")
            for i in range(n):
                row = a.readline().split()
                need(row[:3] == ['C',str(b),str(i)] and pairs(' '.join(row[3:])) == pairs(rows[i]),
                     "replacement facial row")
            row = a.readline().split()
            need(row[:2] == ['Q',str(b)], "replacement matrix order")
            full = [tuple(map(Q,v.split(','))) for v in row[2:]]
            upper = [tuple(map(Q,v.split(','))) for v in r.readline().split()]
            need(len(full) == n*n and len(upper) == n*(n+1)//2, "replacement matrix shape")
            k = 0
            for i in range(n):
                for j in range(i,n):
                    need(full[i*n+j] == full[j*n+i] == upper[k], "replacement full source matrix")
                    k += 1
    return dict(cell=2,blocks=736,regions=1024,all_source_entries_equal=True)


def interfaces(path, expected):
    outcomes = []
    with path.open() as f:
        def read(tag,i):
            row = f.readline().split()
            need(row[:2] == [tag,str(i)], "interface source order")
            return row[2:]
        for j in range(4):
            total = {}
            for b in range(134):
                i = j*134+b
                n, = map(int,read('S',i))
                basis = list(map(int,read('B',i)))
                full = [tuple(map(Q,v.split(','))) for v in read('Q',i)]
                read('D',i)
                need(len(basis) == n and len(full) == n*n, "interface matrix shape")
                need(all(code%2 == 0 and code//2%4096 == 0 for code in basis), "state-only interface columns")
                need(all(full[a*n+c] == full[c*n+a] for a in range(n) for c in range(n)), "interface symmetry")
                gram_add(total,[[(code,Q(1))] for code in basis],
                         [full[a*n+c] for a in range(n) for c in range(a,n)],0)
            read('P',j); read('K',j)
            actual = reduced(total)
            residual = combine((1,expected[j]),(-1,actual))
            need(not residual, f"interface source_identity {j}: {len(residual)} nonzero components")
            outcomes.append(dict(knot=j,blocks=134,normal_components=len(actual),nonzero_residuals=0))
            print('PASS: interface',j,flush=True)
    return outcomes


def negative_controls(V, field, cost, kappas, expected, jumps):
    # An asymmetric Hermitian form with mixed source phases checks sqrt(2),
    # imaginary coefficients, both off-diagonal entries and circle reduction.
    sample = {}
    gram_add(sample,[[(0,Q(1))],[(2*16+1,Q(1))]],
             [(Q(2),Q(0)),(Q(0),Q(1)),(Q(3),Q(0))],0)
    want = combine((1,{(ZERO,0):Q(5)}),(1,variable(1,component=3)),
                   (-1,variable(2,component=3)))
    need(reduced(sample) == want, "mixed-phase sqrt(2) Gram control")
    need(reduced(sample) != {(ZERO,0):Q(5)}, "off-diagonal omission control")
    changed_cost = combine((Q(1,4),multiply(variable(5),variable(6))),
                           (Q(1,2),multiply(variable(9),variable(10))))
    cases = {
        'reversed potential sign': (drift(combine((-1,V[0])),kappas[0],field,cost), expected[0]),
        'omitted cell width': (drift(V[0],1/Q('2935887/1000000'),field,cost), expected[0]),
        'swapped sector cost weights': (drift(V[0],kappas[0],field,changed_cost), expected[0]),
        'doubled real representatives': (drift(combine((2,V[0])),kappas[0],field,cost), expected[0]),
        'reversed interface jump': (combine((-1,jumps[0])),jumps[0]),
        'wrong interface endpoint': (reduced(combine((1,at_xi(V[0],0)),(-1,at_xi(V[1],0)))),jumps[0]),
    }
    result = {}
    for name,(wrong,right) in cases.items():
        count = len(combine((1,wrong),(-1,right)))
        need(count > 0, "undetected mutation: "+name)
        result[name] = count
    result['omitted off-diagonal on mixed-phase control'] = 2
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('potential','allocation','regional','interface','report'):
        p.add_argument('--'+name,type=Path,required=True)
    a = p.parse_args()
    V = potentials(a.potential)
    field,cost = vector_field()
    knots = list(map(Q,['0','1/36','1/3','2/3','35/36','1']))
    kappas = [1/(Q('2935887/1000000')*(knots[j+1]-knots[j])) for j in range(5)]
    expected = [drift(v,k,field,cost) for v,k in zip(V,kappas)]
    jumps = [reduced(combine((1,at_xi(V[j],1)),(-1,at_xi(V[j+1],0)))) for j in range(4)]
    controls = negative_controls(V,field,cost,kappas,expected,jumps)
    report = dict(status='PASS',python_flint=flint.__version__,negative_controls=controls,
                  replacement=allocation_matches(a.allocation,a.regional),
                  occupation=occupation(a.regional,expected),interfaces=interfaces(a.interface,jumps))
    report['decoded_sha256'] = {name:hashlib.sha256(getattr(a,name).read_bytes()).hexdigest()
                               for name in ('potential','allocation','regional','interface')}
    report['trust_boundary'] = 'external exact Q(sqrt(2),i) coefficient check; no kernel proof term'
    report['source_psd_replayed'] = False
    files = [Path(__file__),Path('check_allocated_identities.py')]
    files += [Path(stem+'DataAudit.lean') for stem in ('SourceIdentity','Allocation','Regional','Interface')]
    files += [Path('LowerBoundCZ')/name for name in ('PinnedCertificates.lean','PotentialBasis.lean',
        'PinnedAllocations.lean','PinnedRegions.lean','PinnedInterfaces.lean','SlackAllocation.lean','SlackCrossing.lean')]
    files += [Path('appendix-e/RequestProject/AppendixE')/name for name in
              ('Hierarchy.lean','QuotientNormalForm.lean','QuotientCertificate.lean')]
    report['definitions_sha256'] = {str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
    a.report.write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
