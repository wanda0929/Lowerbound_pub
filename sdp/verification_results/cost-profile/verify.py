#!/usr/bin/env python3
"""Independent rational verification of integrated cost-dependent slack.
Uses direct power expansion and exact tensor affine maps, not de Casteljau.
Requires the pinned global, projection, and population-refinement certificates.
"""
import argparse,copy,gzip,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
from flint import fmpq as Q,fmpq_mat as Mat
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]/'population-refinement'
BASEHASH='3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb'
REFHASH='3932489adf01c5f6ca596663c1624c4ed71bae396d2922d2df2f2beeca882c14'
SOURCE='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
L=F('2.9305');U=F('2.935887');OLD=F('2.931225938506');KNOTS=list(map(F,['0','1/36','1/3','2/3','35/36','1']))
def need(test,message):
    if not test:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def affine(D,a,b):
    a=Q(str(a));h=Q(str(b))-a
    return [[sum((Q(comb(k,l)*comb(i,l),comb(D,l))*a**(k-l)*h**l for l in range(min(i,k)+1)),Q(0)) for k in range(D+1)] for i in range(D+1)]
def bernval(beta,t):
    n=len(beta)-1
    return sum((v*comb(n,k)*t**k*(1-t)**(n-k) for k,v in enumerate(beta)),F(0))
def endpoint(c,ref,K):
    B=F(c['bound']);need(OLD<B<U,'target interval');new=list(map(F,c['endpoint_bernstein']));old=list(map(F,ref['endpoint_bernstein']));need(len(new)==len(old)==14 and all(x>0 for x in new),'endpoint signs')
    rho=(B-L)/(OLD-L)
    for k in range(14):
        t=F(k,13);need(bernval(new,t)==bernval(old,rho*t)+K-F(ref['occupation_slack'])-(B-OLD),'endpoint identity')
def population_map(D,depth):
    N=1<<depth;n=D+1;rows=[[] for _ in range(n*n)];cost=[]
    for x in range(N):
        T=affine(D,F(x,N),F(x+1,N))
        for y in range(N):
            S=affine(D,F(y,N),F(y+1,N))
            for i in range(n):
                for j in range(n):
                    cost.append(Q(x*D+i,2*N*D)+Q(y*D+j,4*N*D))
                    for a in range(n):
                        for b in range(n):rows[a*n+b].append(T[i][a]*S[j][b])
    return Mat(rows),cost

def verify(c,base,ref):
    need(c['schema']=='minexposure/exact-polynomial-cost-profile-v1','schema')
    need(c['source_certificate_sha256']==SOURCE and c['base_certificate_sha256']==BASEHASH and c['refinement_certificate_sha256']==REFHASH,'source binding')
    need(F(c['base_bound'])==OLD and F(c['base_occupation_slack'])==F(ref['occupation_slack']),'inherited constants')
    D=c['population_degree'];M=c['cost_degree'];depth=c['population_depth'];need(D==base['degree']==7 and M==14 and type(depth)is int and 1<=depth<=3,'degree/depth')
    need(len(c['profiles'])==len(base['integration_bins'])==320,'missing/extra cost intervals')
    popmap,cost=population_map(D,depth);records=base['projection_records'];cache={};K=Q(0);checks=0;profilecount=0
    for index,(profile,item) in enumerate(zip(c['profiles'],base['integration_bins'])):
        need(profile['interval_index']==index,'interval order');delta=list(map(Q,profile['bernstein']));need(len(delta)==M+1,'cost polynomial degree')
        if profile['mode']=='inherited_constant':need(all(x==Q(ref['refined_deltas'][index]) for x in delta),'altered inherited rate')
        else:
            need(profile['mode']=='polynomial','unknown profile type');profilecount+=1
            # Reconstruct the full signed power polynomial from verified projections.
            groups={}
            for rid,weight,unusedrate in item['allocations']:
                rec=records[rid];ex=tuple(rec['population_exponents']);p=groups.setdefault(ex,[Q(0)]*(M+1));w=Q(weight)
                for k,a in enumerate(rec['polynomial']):p[k]+=w*Q(a)
            power=[[Q(0)]*((D+1)**2) for k in range(M+1)]
            for ex,p in groups.items():
                if ex not in cache:
                    g,r,h,s=ex;cache[ex]=[((r+i)*(D+1)+s+j,Q((-1)**(i+j)*comb(g,i)*comb(h,j))) for i in range(g+1) for j in range(h+1)]
                for k,a in enumerate(p):
                    if a:
                        for position,b in cache[ex]:power[k][position]+=a*b
            matrix=Mat(affine(M,F(item['a']),F(item['b'])))*Mat(power)*popmap
            for k in range(M+1):
                for col,co in enumerate(cost):need(matrix[k,col]-delta[k]*co>=0,'negative tensor Bernstein coefficient');checks+=1
        j=item['cell'];mass=Q(str(U*(KNOTS[j+1]-KNOTS[j])*(F(item['b'])-F(item['a']))));K+=mass*sum(delta,Q(0))/(M+1)
        if index%40==0:print('VERIFIED_PROFILE',index,'polynomial_intervals',profilecount,flush=True)
    K=F(str(K));need(K==F(c['occupation_slack']) and K>F(ref['occupation_slack']),'integrated slack');endpoint(c,ref,K)
    return {'status':'PASS','certified_lower_bound':c['bound'],'previous_lower_bound':str(OLD),'exact_increase':str(F(c['bound'])-OLD),'occupation_slack':str(K),'old_occupation_slack':ref['occupation_slack'],'cost_intervals':320,'polynomial_intervals':profilecount,'tensor_coefficient_inequalities':checks,'endpoint_identities':14,'positive_endpoint_coefficients':14,'exact_rational_arithmetic':True,'floating_point_used':False,'optimization_used':False,'scope':'all-duration ideal-blockade stationary-torus'}

def tests(c,ref):
    out=[]
    for D in (1,7,14):
        T=affine(D,F(2,7),F(5,7))
        for p in range(D+1):
            b=[F(str(row[p])) for row in T]
            for t in (F(0),F(2,5),F(1)):need(bernval(b,t)==(F(2,7)+F(3,7)*t)**p,'affine identity test')
        out.append('affine degree '+str(D))
    for label,change in [('target',lambda z:z.update(bound=str(F(z['bound'])+F(1,10000)))),('endpoint',lambda z:z['endpoint_bernstein'].__setitem__(3,str(F(z['endpoint_bernstein'][3])+1))),('integral',lambda z:z.update(occupation_slack=str(F(z['occupation_slack'])+1)))]:
        z=copy.deepcopy(c);change(z)
        try:endpoint(z,ref,F(z['occupation_slack']))
        except ValueError:out.append('rejected '+label)
        else:raise ValueError('mutation accepted: '+label)
    # Integral of each degree-14 Bernstein basis is 1/15 (power expansion check).
    for i in range(15):
        integral=sum((F(comb(14,i)*comb(14-i,k)*(-1)**k,i+k+1) for k in range(15-i)),F(0));need(integral==F(1,15),'Bernstein integral test')
    out.append('exact Bernstein integrals');return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    raw=gzip.decompress((ROOT/'certified/population-certificate.json.gz').read_bytes());need(sha(raw)==BASEHASH,'base hash');base=json.loads(raw);del raw
    raw=(ROOT/'certified/subdivision-certificate.json').read_bytes();need(sha(raw)==REFHASH,'refinement hash');ref=json.loads(raw);c=json.loads(args.certificate.read_text())
    result=verify(c,base,ref)
    if args.self_test:result['tests']=tests(c,ref);result['tests_passed']=len(result['tests'])+1
    result.update(source_certificate_sha256=SOURCE,base_certificate_sha256=BASEHASH,refinement_certificate_sha256=REFHASH,certificate_sha256=sha(args.certificate.read_bytes()),dependency='Pinned original source, projection and population subdivision certificates; replay population-refinement/reproduce.sh')
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['occupation_slack','old_occupation_slack']},indent=2),flush=True)
if __name__=='__main__':main()
