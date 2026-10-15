#!/usr/bin/env python3
"""Exact population-subdivision extension of an independently verified certificate.

This producer never changes a projection, its allocation, or the integrated
cost prefix. It replaces global population Bernstein bounds by bounds on a
partition, preserving all original matrix and source-audit dependencies.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from fractions import Fraction as F
from math import comb
from pathlib import Path
from flint import fmpq as Q
sys.set_int_max_str_digits(0)
L=F('2.9305'); U=F('2.935887')
KNOTS=list(map(F,['0','1/36','1/3','2/3','35/36','1']))
def require(test,message):
    if not test: raise ValueError(message)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def split1(v):
    a=list(v);left=[a[0]];right=[a[-1]]
    while len(a)>1:
        a=[(a[i]+a[i+1])/2 for i in range(len(a)-1)]
        left.append(a[0]);right.append(a[-1])
    return left,list(reversed(right))
def partition(v,depth):
    if not depth:return [v]
    a,b=split1(v)
    return partition(a,depth-1)+partition(b,depth-1)
def numerator(data,item,cache):
    D=data['degree'];n=D+1;z=[Q(0)]*(n*n)
    for index,weight,rate in item['allocations']:
        ex=tuple(data['projection_records'][index]['population_exponents'])
        if ex not in cache:
            g,r,h,s=ex;out=[]
            for i in range(r,D-g+1):
                for j in range(s,D-h+1):
                    c=Q(comb(D-r-g,i-r),comb(D,i))*Q(comb(D-s-h,j-s),comb(D,j))
                    if c:out.append((i*n+j,c))
            cache[ex]=out
        w=Q(weight)*Q(rate)
        for i,c in cache[ex]:z[i]+=w*c
    return [z[i*n:(i+1)*n] for i in range(n)]
def box_bound(M,D,depth):
    # First subdivide every y-column in x, then each resulting x-row in y.
    n=D+1;N=1<<depth
    cols=[partition([M[i][j] for i in range(n)],depth) for j in range(n)]
    minimum=None
    for x in range(N):
        rows=[partition([cols[j][x][i] for j in range(n)],depth) for i in range(n)]
        for y in range(N):
            for i in range(n):
                for j in range(n):
                    c=Q(x*D+i,2*N*D)+Q(y*D+j,4*N*D)
                    value=rows[i][y][j]
                    require(value>=0,'negative numerator coefficient')
                    if c:
                        ratio=value/c
                        minimum=ratio if minimum is None or ratio<minimum else minimum
    return F(str(minimum))
def power_from_bernstein(b):
    d=len(b)-1;p=[F(0)]*(d+1)
    for k,c in enumerate(b):
        for j in range(d-k+1):p[k+j]+=c*comb(d,k)*comb(d-k,j)*(-1)**j
    return p
def bernstein_from_power(p):
    d=len(p)-1
    return [sum((p[j]*F(comb(i,j),comb(d,j)) for j in range(i+1)),F(0)) for i in range(d+1)]
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base-certificate',type=Path,required=True);ap.add_argument('--base-report',type=Path,required=True)
    ap.add_argument('--depth',type=int,default=2);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();require(1<=args.depth<=5,'unsupported depth')
    base=json.loads(args.base_certificate.read_text());audit=json.loads(args.base_report.read_text())
    require(audit['status']=='PASS' and audit['certificate_sha256']==digest(args.base_certificate),'base proof is not verified or mismatched')
    old=F(base['bound']);require(old==F(audit['certified_lower_bound']),'base bound mismatch')
    D=base['degree'];require(1<=D<=7,'unsupported degree')
    cache={};deltas=[];K=F(0);oldK=F(0)
    for k,item in enumerate(base['integration_bins']):
        M=numerator(base,item,cache);delta=box_bound(M,D,args.depth)
        require(delta>=F(item['delta']),'subdivision weakened a certified inequality')
        j=item['cell'];mass=U*(KNOTS[j+1]-KNOTS[j])*(F(item['b'])-F(item['a']))
        K+=mass*delta;oldK+=mass*F(item['delta']);deltas.append(str(delta))
        if k%40==0:print('REFINED_INTERVAL',k,flush=True)
    require(oldK==F(base['occupation_slack']),'base integral mismatch')
    p=power_from_bernstein(list(map(F,base['endpoint_bernstein'])))
    def endpoint(B):
        rho=(B-L)/(old-L);new=[c*rho**i for i,c in enumerate(p)]
        new[0]+=K-oldK-(B-old)
        return bernstein_from_power(new)
    scale=10**12;lo=int(old*scale);hi=int(U*scale)
    require(all(v>0 for v in endpoint(F(lo,scale))),'base endpoint not recovered')
    while lo+1<hi:
        mid=(lo+hi)//2
        if all(v>0 for v in endpoint(F(mid,scale))):lo=mid
        else:hi=mid
    B=F(lo,scale);require(B>=old,'lower bound decreased')
    report={'schema':'minexposure/exact-population-subdivision-v1','status':'producer exact; independent verification required',
      'source_certificate_sha256':base['source_certificate_sha256'],'base_certificate_sha256':digest(args.base_certificate),
      'base_report_sha256':digest(args.base_report),'base_bound':str(old),'degree':D,'population_subdivision_depth':args.depth,
      'refined_deltas':deltas,'base_occupation_slack':str(oldK),'occupation_slack':str(K),'occupation_slack_increase':str(K-oldK),
      'bound':str(B),'bound_decimal':f'{lo//scale}.{lo%scale:012d}','exact_increase':str(B-old),
      'endpoint_bernstein':list(map(str,endpoint(B))),'matrix_projections_and_allocations_unchanged':True}
    args.output.mkdir(parents=True,exist_ok=True)
    path=args.output/'subdivision-certificate.json';path.write_text(json.dumps(report,indent=2)+'\n')
    summary={k:report[k] for k in ['status','bound','bound_decimal','base_bound','exact_increase','degree','population_subdivision_depth']}
    summary.update(certificate_sha256=digest(path),interval_count=len(deltas),occupation_slack_display=float(K))
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
