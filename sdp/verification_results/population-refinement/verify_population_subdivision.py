#!/usr/bin/env python3
"""Independent exact-rational checker for population-subdivision strengthening.

No producer imports, optimization, or floating-point acceptance. This checker
expands population powers, reconstructs elevated Bernstein coefficients, and
uses explicit blossom matrices (not de Casteljau recursion) on every box.
The hash-bound full base-certificate verification is an explicit dependency.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from fractions import Fraction as R
from math import comb
from pathlib import Path
from flint import fmpq as Q, fmpq_mat as Mat
sys.set_int_max_str_digits(0)
SOURCE='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
L=R('2.9305');U=R('2.935887');KNOTS=list(map(R,['0','1/36','1/3','2/3','35/36','1']))
def check(value,message):
    if not value:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def elevated(a,b,D):
    # p^a(1-p)^b: direct power expansion, then power-to-Bernstein conversion.
    power=[R(0)]*(a+b+1)
    for k in range(b+1):power[a+k]=R((-1)**k*comb(b,k))
    return [sum((power[k]*R(comb(i,k),comb(D,k)) for k in range(min(i,len(power)-1)+1)),R(0)) for i in range(D+1)]
def restriction(D,a,b):
    # Blossom: coefficient i is evaluation at i copies of b, D-i copies of a.
    T=[]
    for i in range(D+1):
        row=[]
        for j in range(D+1):
            s=R(0)
            for k in range(max(0,j-(D-i)),min(i,j)+1):
                t=j-k
                s+=comb(i,k)*comb(D-i,t)*b**k*(1-b)**(i-k)*a**t*(1-a)**(D-i-t)
            row.append(Q(str(s)))
        check(sum(row,Q(0))==1,'blossom partition identity')
        T.append(row)
    return Mat(T)
def evalbern(coeff,t):
    d=len(coeff)-1
    return sum((coeff[k]*comb(d,k)*t**k*(1-t)**(d-k) for k in range(d+1)),R(0))
def endpoint_check(base,data,K):
    B=R(data['bound']);old=R(base['bound']);beta=list(map(R,data['endpoint_bernstein']))
    check(old<=B<U and len(beta)==14 and all(v>0 for v in beta),'endpoint range or positivity')
    prior=list(map(R,base['endpoint_bernstein']));check(len(prior)==14,'base endpoint degree')
    rho=(B-L)/(old-L)
    for i in range(14):
        t=R(i,13)
        expected=evalbern(prior,rho*t)+K-R(base['occupation_slack'])-(B-old)
        check(evalbern(beta,t)==expected,'exact endpoint polynomial identity')
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base-certificate',type=Path,required=True);ap.add_argument('--base-report',type=Path,required=True)
    ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    base=json.loads(args.base_certificate.read_text());audit=json.loads(args.base_report.read_text());data=json.loads(args.certificate.read_text())
    check(data['schema']=='minexposure/exact-population-subdivision-v1','schema')
    check(audit['status']=='PASS' and audit['certificate_sha256']==sha(args.base_certificate),'unverified base input')
    check(data['base_certificate_sha256']==sha(args.base_certificate) and data['base_report_sha256']==sha(args.base_report),'base input hashes')
    check(base['source_certificate_sha256']==SOURCE and data['source_certificate_sha256']==SOURCE and audit['source_certificate_sha256']==SOURCE,'source binding')
    check(R(data['base_bound'])==R(base['bound'])==R(audit['certified_lower_bound']),'base lower bound')
    D=data['degree'];depth=data['population_subdivision_depth'];check(type(D)is int and 1<=D<=7 and D==base['degree'],'degree')
    check(type(depth)is int and 1<=depth<=5,'subdivision depth');N=1<<depth;n=D+1
    transforms=[restriction(D,R(i,N),R(i+1,N)) for i in range(N)]
    deltas=list(map(R,data['refined_deltas']));check(len(deltas)==len(base['integration_bins']),'interval count')
    cache={};K=R(0);oldK=R(0);inequalities=0
    for it,(item,delta) in enumerate(zip(base['integration_bins'],deltas)):
        check(delta>=R(item['delta'])>=0,'nonnegative strengthening')
        values=[Q(0)]*(n*n)
        for idx,weight,rate in item['allocations']:
            e=tuple(base['projection_records'][idx]['population_exponents']);g,r,h,s=e
            check(min(e)>=0 and g+r<=D and h+s<=D and r+s>0,'population exponents')
            if e not in cache:
                p=elevated(r,g,D);q=elevated(s,h,D)
                cache[e]=[(i*n+j,Q(str(p[i]*q[j]))) for i in range(n) for j in range(n) if p[i] and q[j]]
            w=Q(weight)*Q(rate);check(w>=0,'nonnegative allocation')
            for k,c in cache[e]:values[k]+=w*c
        M=Mat(n,n,values)
        for x,T in enumerate(transforms):
            A=T*M
            for y,V in enumerate(transforms):
                B=A*V.transpose()
                for i in range(n):
                    for j in range(n):
                        c=R(x*D+i,2*N*D)+R(y*D+j,4*N*D)
                        check(B[i,j]>=Q(str(delta*c)),'negative local population Bernstein coefficient')
                        inequalities+=1
        cell=item['cell'];mass=U*(KNOTS[cell+1]-KNOTS[cell])*(R(item['b'])-R(item['a']))
        K+=mass*delta;oldK+=mass*R(item['delta'])
        if it%40==0:print('CHECKED_INTERVAL',it,flush=True)
    check(oldK==R(base['occupation_slack'])==R(data['base_occupation_slack']),'base integral')
    check(K==R(data['occupation_slack']) and K-oldK==R(data['occupation_slack_increase']),'new integral')
    check(R(data['exact_increase'])==R(data['bound'])-R(base['bound']),'reported bound increase')
    endpoint_check(base,data,K)
    tests=[]
    if args.self_test:
        for Dtest in [1,3,7]:
            T=restriction(Dtest,R(1,4),R(3,4));a,b=R(1,4),R(3,4)
            for j in range(Dtest+1):
                coeff=[R(str(T[i,j])) for i in range(Dtest+1)]
                for t in [R(0),R(2,7),R(1)]:
                    x=a+(b-a)*t
                    check(evalbern(coeff,t)==comb(Dtest,j)*x**j*(1-x)**(Dtest-j),'blossom evaluation self-test')
            tests.append('restriction basis degree '+str(Dtest))
        for label,mutation in [('changed target',{'bound':str(R(data['bound'])+R(1,1000))}),('changed endpoint coefficient',{'endpoint_bernstein':['-1']+data['endpoint_bernstein'][1:]})]:
            changed=dict(data,**mutation)
            try:endpoint_check(base,changed,K)
            except ValueError:tests.append('rejected '+label)
            else:raise ValueError('invalid certificate accepted: '+label)
        tests.append('valid complete certificate')
    out={'status':'PASS','schema':data['schema'],'certified_lower_bound':data['bound'],'base_certified_lower_bound':base['bound'],
      'exact_improvement':data['exact_increase'],'source_certificate_sha256':SOURCE,'base_certificate_sha256':sha(args.base_certificate),
      'base_report_sha256':sha(args.base_report),'certificate_sha256':sha(args.certificate),'cost_intervals':len(deltas),
      'population_boxes_per_interval':N*N,'exact_population_coefficient_inequalities':inequalities,'exact_endpoint_interpolation_identities':14,
      'positive_endpoint_bernstein_coefficients':14,'occupation_slack':str(K),'occupation_slack_increase':str(K-oldK),
      'floating_point_used':False,'optimization_used':False,'tests_passed':len(tests),'tests':tests,
      'dependency':'full verification of hash-bound base certificate, original source, metadata, and interface proof is required',
      'scope':'all-duration ideal-blockade stationary-torus'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS',json.dumps({k:v for k,v in out.items() if k not in ['occupation_slack','occupation_slack_increase']}),flush=True)
if __name__=='__main__':main()
