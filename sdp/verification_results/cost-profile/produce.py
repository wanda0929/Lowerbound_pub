#!/usr/bin/env python3
"""Exact cost-profile extension of the verified population refinement.
No new optimizer is used. All original allocations and projections are fixed.
"""
import argparse,gzip,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
from flint import fmpq as Q
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]/'population-refinement'
sys.path.insert(0,str(ROOT))
import certify_population_subdivision as old
DEG=14
BASEHASH='3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb'
REFHASH='3932489adf01c5f6ca596663c1624c4ed71bae396d2922d2df2f2beeca882c14'

def bern(p,a,b):
    while len(p)>1 and not p[-1]:p.pop()
    n=len(p)-1;a=Q(str(a));h=Q(str(b))-a
    c=[sum((p[j]*comb(j,k)*a**(j-k)*h**k for j in range(k,n+1)),Q(0)) for k in range(n+1)]
    return [sum((c[k]*Q(comb(i,k),comb(n,k)) for k in range(i+1)),Q(0)) for i in range(n+1)]

def elevate(b,n):
    d=len(b)-1
    return [sum((b[k]*Q(comb(d,k)*comb(n-d,i-k),comb(n,i)) for k in range(max(0,i-(n-d)),min(d,i)+1)),Q(0)) for i in range(n+1)]

def pc(ex,D):
    g,r,h,s=ex;out=[]
    for i in range(r,D-g+1):
        for j in range(s,D-h+1):out.append((i*(D+1)+j,Q(comb(D-r-g,i-r),comb(D,i))*Q(comb(D-s-h,j-s),comb(D,j))))
    return out

def minimum_ratio(M,D,depth):
    n=D+1;N=1<<depth;cols=[old.partition([M[i*n+j] for i in range(n)],depth) for j in range(n)];minimum=None
    for x in range(N):
        rows=[old.partition([cols[j][x][i] for j in range(n)],depth) for i in range(n)]
        for y in range(N):
            for i in range(n):
                for j in range(n):
                    c=Q(x*D+i,2*N*D)+Q(y*D+j,4*N*D);v=rows[i][y][j]
                    if c:
                        r=v/c
                        if minimum is None or r<minimum:minimum=r
                    else:old.require(v>=0,'negative coefficient on zero-cost face')
    return minimum

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--population-depth',type=int,default=2);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    raw=gzip.decompress((ROOT/'certified/population-certificate.json.gz').read_bytes());old.require(hashlib.sha256(raw).hexdigest()==BASEHASH,'base certificate hash');base=json.loads(raw);del raw
    raw=(ROOT/'certified/subdivision-certificate.json').read_bytes();old.require(hashlib.sha256(raw).hexdigest()==REFHASH,'refinement hash');ref=json.loads(raw);D=base['degree'];records=base['projection_records'];cache={};popcache={};profiles=[];K=Q(0);oldbound=F(ref['bound']);used=0
    for index,item in enumerate(base['integration_bins']):
        j=item['cell'];a=F(item['a']);b=F(item['b']);N=[[Q(0)]*((D+1)**2) for k in range(DEG+1)]
        for rid,w,unused_rate in item['allocations']:
            r=records[rid];ex=tuple(r['population_exponents'])
            if ex not in popcache:popcache[ex]=pc(ex,D)
            if rid not in cache:
                stop=F(1) if j<4 else F(base['integration_bins'][-1]['b'])
                root=bern(list(map(Q,r['polynomial'])),F(0),stop)
                cache[rid]=old.partition(root,6)
            k=index%64;beta=elevate(cache[rid][k],DEG);weight=Q(w)
            for d,v in enumerate(beta):
                if v:
                    s=weight*v
                    for pos,c in popcache[ex]:N[d][pos]+=s*c
        delta=[minimum_ratio(M,D,args.population_depth) for M in N];mean=sum(delta,Q(0))/(DEG+1);baseline=Q(ref['refined_deltas'][index])
        if mean>baseline:
            mode='polynomial';used+=1
        else:delta=[baseline]*(DEG+1);mean=baseline;mode='inherited_constant'
        mass=Q(str(old.U*(old.KNOTS[j+1]-old.KNOTS[j])*(b-a)));K+=mass*mean
        profiles.append({'interval_index':index,'mode':mode,'bernstein':list(map(str,delta))})
        if index%40==0:print('PROFILE',index,'mean',float(mean),'inherited',float(baseline),'polynomial_intervals',used,flush=True)
    K=F(str(K));oldK=F(ref['occupation_slack']);old.require(K>oldK,'no occupation improvement')
    poly=old.power_from_bernstein(list(map(F,ref['endpoint_bernstein'])))
    def endpoint(B):
        rho=(B-old.L)/(oldbound-old.L);p=[c*rho**i for i,c in enumerate(poly)];p[0]+=K-oldK-(B-oldbound);return old.bernstein_from_power(p)
    scale=10**12;lo=int(oldbound*scale);hi=int(old.U*scale)
    while lo+1<hi:
        mid=(lo+hi)//2
        if all(x>0 for x in endpoint(F(mid,scale))):lo=mid
        else:hi=mid
    B=F(lo,scale);result={'schema':'minexposure/exact-polynomial-cost-profile-v1','status':'producer exact; independent verification required','base_certificate_sha256':BASEHASH,'refinement_certificate_sha256':REFHASH,'source_certificate_sha256':base['source_certificate_sha256'],'base_bound':str(oldbound),'bound':str(B),'bound_decimal':f'{lo//scale}.{lo%scale:012d}','base_occupation_slack':str(oldK),'occupation_slack':str(K),'population_degree':D,'cost_degree':DEG,'population_depth':args.population_depth,'profiles':profiles,'endpoint_bernstein':list(map(str,endpoint(B))),'projections_and_allocation_weights_unchanged':True}
    f=args.output/'certificate.json';f.write_text(json.dumps(result,indent=2)+'\n');summary={k:result[k] for k in ['status','bound','bound_decimal','base_bound']};summary.update(exact_increase=str(B-oldbound),occupation_slack_display=float(K),occupation_increase_display=float(K-oldK),polynomial_intervals=used,certificate_sha256=hashlib.sha256(f.read_bytes()).hexdigest());(args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
