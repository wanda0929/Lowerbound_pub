#!/usr/bin/env python3
"""Independent full-population crossing verifier; no producer/optimizer imports.

Checks Q - diag(sum(weight*gamma)) directly by rigorously enclosed LDL,
not the producer's inverse diagonals. The population polynomials are expanded
in powers and transformed to each rectangle explicitly. Existing occupation
and original global certificates are pinned, separately replayable dependencies.
"""
import argparse,copy,gzip,hashlib,json,sys
from fractions import Fraction as F
from pathlib import Path
from math import comb
from flint import arb_mat,ctx,fmpq as Q
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]/'population-refinement'
sys.path.insert(0,str(ROOT))
import verify_projected_slack as v
BASE='3932489adf01c5f6ca596663c1624c4ed71bae396d2922d2df2f2beeca882c14'
INTERFACE='de48f592c9ecbb2463bbeb0feb10e913c4a290e218cc50c339cb3ad29a040f2e'
OLD=F('2.931225938506')
def need(x,message):
    if not x:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def expand(ex,D):
    g,r,h,s=ex;A=[[Q(0)]*(D+1) for _ in range(D+1)]
    for i in range(g+1):
        for j in range(h+1):A[r+i][s+j]=Q((-1)**(i+j)*comb(g,i)*comb(h,j))
    return A

def transform(D,a,b):
    a=Q(str(a));h=Q(str(b))-a
    return [[sum((Q(comb(k,l)*comb(i,l),comb(D,l))*a**(k-l)*h**l for l in range(min(i,k)+1)),Q(0)) for k in range(D+1)] for i in range(D+1)]

def restrict(P,T,S):
    n=len(P);A=[[sum((T[i][k]*P[k][j] for k in range(n)),Q(0)) for j in range(n)] for i in range(n)]
    return [[sum((A[i][k]*S[j][k] for k in range(n)),Q(0)) for j in range(n)] for i in range(n)]

def bern_value(b,t):
    n=len(b)-1
    return sum((x*comb(n,i)*t**i*(1-t)**(n-i) for i,x in enumerate(b)),F(0))

def endpoint_check(base,c,K):
    B=F(c['bound']);need(OLD<B<v.U,'new bound outside permitted interval')
    beta=list(map(F,c['endpoint_bernstein']));need(len(beta)==14 and all(x>0 for x in beta),'endpoint coefficient signs')
    previous=list(map(F,base['endpoint_bernstein']));need(len(previous)==14,'base endpoint degree')
    rho=(B-v.L)/(OLD-v.L)
    for i in range(14):
        t=F(i,13);expected=bern_value(previous,rho*t)+K-v.KAPPA-(B-OLD)
        need(bern_value(beta,t)==expected,'endpoint polynomial identity')

def verify(c,source,bases,base):
    need(c['schema']=='minexposure/full-population-interface-v1','schema')
    need(c['source_certificate_sha256']==v.SOURCE and c['base_certificate_sha256']==BASE,'source binding')
    need(F(c['base_bound'])==OLD and F(c['old_interface_slack'])==v.KAPPA,'previous constants')
    need(source['knots']==['0','1/36','1/3','2/3','35/36','1'] and F(source['exposure_upper'])==v.U and F(source['bound_target'])==v.L,'source model')
    D=c['degree'];depth=c['population_subdivision_depth'];need(type(D)is int and 1<=D<=7 and type(depth)is int and 0<=depth<=4,'degree/subdivision')
    need(len(c['crossings'])==4 and [x['knot'] for x in c['crossings']]==list(range(4)),'all four mandatory crossings required')
    records=c['records'];used=set();matrices=0;coordinates=0;inequalities=0;total=F(0)
    N=1<<depth;Ts=[transform(D,F(k,N),F(k+1,N)) for k in range(N)]
    for j,item in enumerate(c['crossings']):
        polynomial=[[Q(0)]*(D+1) for _ in range(D+1)];by={};seen=set()
        for index,weight in item['allocations']:
            need(type(index)is int and 0<=index<len(records) and index not in seen,'duplicate/unknown projection');seen.add(index);used.add(index)
            rec=records[index];need(rec['knot']==j,'crossing mismatch');b=rec['block'];i=rec['row']
            need(type(b)is int and 0<=b<len(source['interface_grams_by_knot'][j]),'invalid block')
            rawQ=source['interface_grams_by_knot'][j][b];need(len(rawQ)==len(bases[b]),'basis dimension')
            need(type(i)is int and 0<=i<len(rawQ),'invalid coordinate');m=bases[b][i]
            need(m['cost_power']==0 and len(m['anti'])==len(m['holo'])==4,'state monomial')
            ex=[a+h for a,h in zip(m['anti'],m['holo'])]
            need(ex==rec['population_exponents'] and sum(ex)<=D and all(type(k)is int and k>=0 for k in ex),'population identity')
            w=F(weight);g=F(rec['gamma']);need(w>0 and g>0,'negative allocation')
            active=rec['active_indices'];need(len(set(active))==len(active) and all(type(k)is int and 0<=k<len(rawQ) for k in active) and i in active,'active face')
            if b not in by:
                need(all(all(x=='0' for x in rawQ[k]) for k in range(len(rawQ)) if k not in active),'omitted nonzero coordinate')
                by[b]={'active':active,'diag':{}}
            need(by[b]['active']==active,'inconsistent face')
            by[b]['diag'][i]=by[b]['diag'].get(i,F(0))+w*g
            coefficients=expand(ex,D);rate=Q(str(w*g))
            for a in range(D+1):
                for h in range(D+1):polynomial[a][h]+=rate*coefficients[a][h]
        for b,r in by.items():
            active=r['active'];rawQ=source['interface_grams_by_knot'][j][b]
            M=arb_mat([[v.scalar(rawQ[i][k])-(v.ba(r['diag'].get(i,F(0))) if i==k else 0) for k in active] for i in active])
            v.posdef(M);matrices+=1;coordinates+=len(active)
        bound=F(item['bound']);need(bound>0,'nonpositive crossing bound')
        for T in Ts:
            for S in Ts:
                coefficients=restrict(polynomial,T,S)
                need(all(x>=Q(str(bound)) for row in coefficients for x in row),'population coefficient inequality')
                inequalities+=(D+1)**2
        total+=bound;print('VERIFIED_CROSSING',j,'blocks',len(by),'bound',str(bound),flush=True)
    need(used==set(range(len(records))),'unused projection record')
    need(total==F(c['new_interface_slack']) and total>v.KAPPA,'crossing total')
    endpoint_check(base,c,total)
    return {'status':'PASS','certified_lower_bound':c['bound'],'previous_lower_bound':str(OLD),'exact_increase':str(F(c['bound'])-OLD),'new_interface_slack':str(total),'old_interface_slack':str(v.KAPPA),'matrix_inequalities':matrices,'matrix_coordinates':coordinates,'selected_monomials':len(records),'mandatory_crossings':4,'population_coefficient_inequalities':inequalities,'endpoint_polynomial_identities':14,'positive_endpoint_coefficients':14,'Arb_precision_bits':ctx.prec,'optimization_solver_used':False,'floating_tolerance_used':False,'scope':'all-duration ideal-blockade stationary-torus'}

def tests(base,c):
    passed=[]
    # Check restriction against independent direct evaluation for every monomial.
    for D in (1,3,7):
        T=transform(D,F(1,4),F(3,4))
        for k in range(D+1):
            beta=[F(str(T[i][k])) for i in range(D+1)]
            for t in (F(0),F(1,3),F(1)):
                need(bern_value(beta,t)==(F(1,4)+F(1,2)*t)**k,'restriction self test')
        passed.append('restriction degree '+str(D))
    for name,modify in [('changed target',lambda d:d.update(bound=str(F(d['bound'])+F(1,10000)))),('changed endpoint',lambda d:d['endpoint_bernstein'].__setitem__(3,str(F(d['endpoint_bernstein'][3])+1))),('false total',lambda d:d.update(new_interface_slack=str(F(d['new_interface_slack'])+1))),('negative endpoint',lambda d:d['endpoint_bernstein'].__setitem__(0,'-1'))]:
        bad=copy.deepcopy(c);modify(bad)
        try:endpoint_check(base,bad,F(bad['new_interface_slack']))
        except ValueError:passed.append('rejected '+name)
        else:raise ValueError('accepted mutation '+name)
    for M,label,valid in [(arb_mat([[2,1],[1,2]]),'positive matrix',True),(arb_mat([[1,2],[2,1]]),'indefinite matrix',False),(arb_mat([[1,1],[1,1]]),'singular matrix',False)]:
        try:v.posdef(M);ok=True
        except ValueError:ok=False
        need(ok==valid,'matrix self test');passed.append(label)
    return passed

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parts-dir',type=Path,required=True);ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--self-test',action='store_true');args=ap.parse_args();ctx.prec=384
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)));need(sha(raw)==v.SOURCE,'original source hash');source=json.loads(raw);del raw
    need(sha((ROOT/'certified/source-audit.json').read_bytes())==v.AUDIT,'source audit hash')
    oldraw=gzip.decompress((ROOT/'certified/normalized-interface-certificate.json.gz').read_bytes());need(sha(oldraw)==INTERFACE,'native basis dependency')
    basisraw=(ROOT/'certified/interface-bases.json').read_bytes();need(sha(basisraw)==json.loads(oldraw)['basis_sha256'],'native basis hash');bases=json.loads(basisraw)
    raw=(ROOT/'certified/subdivision-certificate.json').read_bytes();need(sha(raw)==BASE,'occupation certificate hash');base=json.loads(raw)
    c=json.loads(args.certificate.read_text());need(c['bases_sha256']==sha(basisraw),'claimed basis hash')
    result=verify(c,source,bases,base)
    if args.self_test:result['tests']=tests(base,c);result['tests_passed']=len(result['tests'])+1
    result.update(source_certificate_sha256=v.SOURCE,base_certificate_sha256=BASE,source_audit_sha256=v.AUDIT,certificate_sha256=sha(args.certificate.read_bytes()),dependency='Pinned global source, native bases, degree-seven occupation and subdivision certificates; replay with population-refinement/reproduce.sh')
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
