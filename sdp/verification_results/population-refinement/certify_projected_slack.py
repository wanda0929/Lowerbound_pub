#!/usr/bin/env python3
"""Validated trajectory slack producer. Source exact PSD audit is a dependency.
Arb inversion uses rigorous enclosures (never algorithm='approx'). The reduced
matrices and all cost integration/terminal exclusion tests are rational.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
from fractions import Fraction as F
from math import comb
from flint import arb, arb_mat, fmpq, ctx
sys.set_int_max_str_digits(0)
SRC='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
L=F('5861/2000');U=F('2935887/1000000');PREVIOUS=F('2930957146313/1000000000000')
KAPPA=F('1107565238703/1000000000000000000')
KNOTS=list(map(F,['0','1/36','1/3','2/3','35/36','1']))
def require(x,msg):
    if not x:raise ValueError(msg)
def field(s):
    a=F(0);b=F(0)
    for term in s.replace(' ','').replace('-','+-').split('+'):
        if not term:continue
        if term.endswith('*sqrt(2)'):b+=F(term[:-8])
        else:a+=F(term)
    return a,b
# '*sqrt(2)' has 8 characters.
def ball(s):
    a,b=field(s)
    return arb(fmpq(str(a)))+arb(fmpq(str(b)))*arb(2).sqrt()
def BQ(q):return arb(fmpq(str(q)))
def features(d):
    groups={}
    for row,t in enumerate(d['transform_rows']):
        if len(t)!=1:continue
        e=t[0];m=d['basis'][e['basis_index']]['monomial'];a,h=m['anti'],m['holo']
        ex=[a[i]+h[i] for i in range(5)]
        if ex[1] or ex[3] or ex[2]+ex[4]!=1:continue
        key=(1 if ex[2] else 2,tuple(a),tuple(h),d['basis_phases'][e['basis_index']])
        groups.setdefault(key,[]).append([row,m['cost_power'],e['coefficient']])
    return groups

def bernstein(p,a,b):
    n=len(p)-1
    powers=[sum((p[j]*comb(j,k)*a**(j-k)*(b-a)**k for j in range(k,n+1)),F(0)) for k in range(n+1)]
    return [sum((powers[k]*F(comb(i,k),comb(n,k)) for k in range(i+1)),F(0)) for i in range(n+1)]
def add_poly(a,b):
    out=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    return out
def multiply(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
LOCAL={'one':[F(1)],'xi':[F(0),F(1)],'one_minus_xi':[F(1),F(-1)],'xi_one_minus_xi':[F(0),F(1),F(-1)]}
def terminal(gs):
    p=[F(0)]*15
    for k,G in enumerate(gs):
        for i,row in enumerate(G):
            for j,v in enumerate(row):
                a,b=field(v);require(not b,'irrational terminal')
                if k==0:p[i+j]+=a
                else:p[i+j+1]+=a;p[i+j+2]-=a
    while len(p)>1 and p[-1]==0:p.pop()
    return p

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parts-dir',type=Path,required=True);ap.add_argument('--metadata',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--subdivisions',type=int,default=256)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    ctx.prec=256
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)))
    require(hashlib.sha256(raw).hexdigest()==SRC,'source hash');source=json.loads(raw);del raw
    metadata=json.loads(args.metadata.read_text());records=[];skipped=[];totalp=[[[F(0)],[F(0)]] for j in range(5)];start=time.monotonic()
    for d in metadata:
        if d['owner']['measure']!='occupation_cell':continue
        groups=features(d)
        if not groups:continue
        cell=d['owner']['cell_index'];bi=d['owner_block_index'];rawQ=source['occupation_grams_by_cell'][cell][bi]
        active=[i for i,row in enumerate(rawQ) if any(v!='0' and field(v)!=(0,0) for v in row)]
        groups={key:[e for e in es if e[0] in active] for key,es in groups.items()};groups={key:es for key,es in groups.items() if es}
        if not groups:continue
        qa=arb_mat([[ball(rawQ[i][j]) for j in active] for i in active])
        try:inverse=qa.inv()
        except (ZeroDivisionError,ValueError):
            skipped.append([cell,bi]);continue
        amap={a:i for i,a in enumerate(active)}
        for key,entries in groups.items():
            inds=[amap[e[0]] for e in entries];k=len(inds)
            try:S=arb_mat([[inverse[i,j] for j in inds] for i in inds]).inv()
            except (ZeroDivisionError,ValueError):
                skipped.append([cell,bi,'selected']);continue
            # Rational symmetric approximation with a rigorous row-norm discount.
            scale=1<<80
            mid=[[F(0)]*k for i in range(k)]
            for i in range(k):
                for j in range(i,k):
                    v=F(str(((S[i,j]+S[j,i])/2).mid().fmpq()))
                    q=F((v*scale).numerator//(v*scale).denominator,scale);mid[i][j]=mid[j][i]=q
            error=[]
            for i in range(k):
                e=sum((abs(S[i,j]-BQ(mid[i][j])) for j in range(k)),arb(0))
                error.append(F(str(e.upper().fmpq())))
            shift=2*max(error)+F(1,1<<100)
            for i in range(k):mid[i][i]-=shift
            # Explicit interval diagonal-dominance acceptance.
            for i in range(k):
                margin=S[i,i]-BQ(mid[i][i])-sum((abs(S[i,j]-BQ(mid[i][j])) for j in range(k) if j!=i),arb(0))
                require(margin>0,'Schur enclosure dominance')
            p=[F(0)]*(2*max(e[1] for e in entries)+1)
            for i,(_,power,coeff) in enumerate(entries):
                for j,(_,power2,coeff2) in enumerate(entries):p[power+power2]+=coeff*coeff2*mid[i][j]/len(groups)
            p=multiply(p,LOCAL[d['localizer']]);totalp[cell][key[0]-1]=add_poly(totalp[cell][key[0]-1],p)
            rec={'cell':cell,'block':bi,'sector':key[0],'anti':list(key[1]),'holo':list(key[2]),'phase':key[3],'entries':entries,'active_indices':active,'weight':str(F(1,len(groups))),'localizer':d['localizer'],'reduced_matrix':[[str(x) for x in row] for row in mid],'row_norm_discount':str(shift)}
            records.append(rec)
        if len(records)%20<3:print('PROGRESS',cell,bi,len(records),round(time.monotonic()-start,2),flush=True)
    # Cost-weighted integration, including only the guaranteed prefix of cell 5.
    subdivisions=args.subdivisions;bins=[];K=F(0)
    for j in range(5):
        stop=F(1) if j<4 else (PREVIOUS/U-KNOTS[j])/(KNOTS[j+1]-KNOTS[j]);piece=F(0)
        p1=[2*x for x in totalp[j][0]];p2=[4*x for x in totalp[j][1]]
        for i in range(subdivisions):
            a=stop*F(i,subdivisions);b=stop*F(i+1,subdivisions)
            delta=max(F(0),min(min(bernstein(p1,a,b)),min(bernstein(p2,a,b))))
            bins.append({'cell':j,'a':str(a),'b':str(b),'delta':str(delta)})
            piece+=U*(KNOTS[j+1]-KNOTS[j])*(b-a)*delta
        K+=piece;print('CELL',j,'guaranteed_slack_display',float(piece),flush=True)
    q=terminal(source['terminal_grams_by_cell'][4]);den=10**12
    def endpoint(target):
        p=q.copy();p[0]+=K+KAPPA-(target-L)
        return bernstein(p,36*L/U-35,36*target/U-35)
    low=int(PREVIOUS*den);high=int(U*den)
    require(all(x>0 for x in endpoint(F(low,den))),'previous target not recovered')
    while low+1<high:
        m=(low+high)//2
        if all(x>0 for x in endpoint(F(m,den))):low=m
        else:high=m
    target=F(low,den)
    report={'schema':'minexposure/validated-trajectory-schur-v1','source_certificate_sha256':SRC,'metadata_sha256':hashlib.sha256(args.metadata.read_bytes()).hexdigest(),'precision_bits':ctx.prec,'previous_bound':str(PREVIOUS),'bound':str(target),'bound_decimal':f'{low//den}.{low%den:012d}','interface_slack':str(KAPPA),'occupation_slack':str(K),'projection_records':records,'occupation_polynomials':[[[str(x) for x in p] for p in cell] for cell in totalp],'integration_bins':bins,'endpoint_bernstein':[str(x) for x in endpoint(target)],'skipped_blocks':skipped,'status':'validated producer; independent replay and source binding required'}
    (args.output/'trajectory-certificate.json').write_text(json.dumps(report,indent=2)+'\n')
    summary={k:report[k] for k in ['schema','bound','bound_decimal','occupation_slack','interface_slack','status']};summary['occupation_slack_display']=float(K);summary['projections']=len(records);summary['skipped']=len(skipped)
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
