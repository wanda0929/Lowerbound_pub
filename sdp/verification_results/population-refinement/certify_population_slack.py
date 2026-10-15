#!/usr/bin/env python3
"""Population-normalized trajectory slack. Validated Schur projections plus
rationalized LP allocations; final acceptance uses no LP tolerances.
"""
from __future__ import annotations
import argparse,gzip,hashlib,json,time,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
from flint import arb,arb_mat,ctx
import certify_projected_slack as base

def groups_of(d,degree):
    groups={}
    for row,t in enumerate(d['transform_rows']):
        if len(t)!=1:continue
        e=t[0];m=d['basis'][e['basis_index']]['monomial'];a,h=m['anti'],m['holo'];power=tuple(a[i]+h[i] for i in range(1,5))
        if sum(power)>degree or power[1]+power[3]==0:continue
        key=(tuple(a),tuple(h),d['basis_phases'][e['basis_index']],power)
        groups.setdefault(key,[]).append([row,m['cost_power'],e['coefficient']])
    return groups

def lower_matrix(S):
    n=S.nrows();scale=1<<80
    M=[[F(0)]*n for i in range(n)]
    for i in range(n):
        for j in range(i,n):
            v=F(str(((S[i,j]+S[j,i])/2).mid().fmpq()));r=v*scale
            M[i][j]=M[j][i]=F(r.numerator//r.denominator,scale)
    errors=[F(str(sum((abs(S[i,j]-base.BQ(M[i][j])) for j in range(n)),arb(0)).upper().fmpq())) for i in range(n)]
    shift=2*max(errors)+F(1,1<<100)
    for i in range(n):M[i][i]-=shift
    for i in range(n):base.require(S[i,i]-base.BQ(M[i][i])-sum((abs(S[i,j]-base.BQ(M[i][j])) for j in range(n) if j!=i),arb(0))>0,'reduced matrix enclosure')
    return M

def dyadic_bounds(p,stop,depth):
    root=base.bernstein(p,F(0),stop)
    def split(b,n):
        if n==0:return [max(F(0),min(b))]
        left=[b[0]];right=[b[-1]];a=b
        while len(a)>1:
            a=[(a[i]+a[i+1])/2 for i in range(len(a)-1)];left.append(a[0]);right.append(a[-1])
        return split(left,n-1)+split(list(reversed(right)),n-1)
    return split(root,depth)

def population_coefficients(exponents,D):
    g,r,h,s=exponents
    def coef(k,a,b):
        return F(comb(D-a-b,k-a),comb(D,k)) if a<=k<=D-b else F(0)
    return [coef(i,r,g)*coef(j,s,h) for i in range(D+1) for j in range(D+1)]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parts-dir',type=Path,required=True);ap.add_argument('--metadata',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--degree',type=int,default=3);ap.add_argument('--depth',type=int,default=6)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True);ctx.prec=256
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)));base.require(hashlib.sha256(raw).hexdigest()==base.SRC,'source hash');source=json.loads(raw);del raw
    metadata=json.loads(args.metadata.read_text());records=[];start=time.monotonic();skipped=[]
    for d in metadata:
        if d['owner']['measure']!='occupation_cell':continue
        groups=groups_of(d,args.degree)
        if not groups:continue
        j=d['owner']['cell_index'];b=d['owner_block_index'];rawQ=source['occupation_grams_by_cell'][j][b]
        active=[i for i,row in enumerate(rawQ) if any(v!='0' and base.field(v)!=(0,0) for v in row)]
        groups={key:[e for e in es if e[0] in active] for key,es in groups.items()};groups={key:es for key,es in groups.items() if es}
        if not groups:continue
        Q=arb_mat([[base.ball(rawQ[i][k]) for k in active] for i in active])
        try:inv=Q.inv()
        except (ZeroDivisionError,ValueError):skipped.append([j,b]);continue
        amap={i:k for k,i in enumerate(active)}
        for key,es in groups.items():
            inds=[amap[e[0]] for e in es]
            try:S=arb_mat([[inv[i,k] for k in inds] for i in inds]).inv();M=lower_matrix(S)
            except (ZeroDivisionError,ValueError):skipped.append([j,b,'selection']);continue
            p=[F(0)]*(2*max(e[1] for e in es)+1)
            for i,(_,power,c) in enumerate(es):
                for k,(_,power2,c2) in enumerate(es):p[power+power2]+=c*c2*M[i][k]
            p=base.multiply(p,base.LOCAL[d['localizer']])
            records.append({'cell':j,'block':b,'anti':list(key[0]),'holo':list(key[1]),'phase':key[2],'population_exponents':list(key[3]),'entries':es,'active_indices':active,'localizer':d['localizer'],'reduced_matrix':[[str(x) for x in row] for row in M],'polynomial':[str(x) for x in p]})
        if b%50==0:print('PROGRESS',j,b,len(records),round(time.monotonic()-start,1),flush=True)
    proj={'source_certificate_sha256':base.SRC,'metadata_sha256':hashlib.sha256(args.metadata.read_bytes()).hexdigest(),'degree':args.degree,'projection_records':records,'skipped':skipped}
    (args.output/'population-projections.json').write_text(json.dumps(proj,indent=2)+'\n');print('PROJECTIONS_READY',len(records),round(time.monotonic()-start,1),flush=True)
    bins=[];K=F(0);D=args.degree;N=1<<args.depth
    pcost=[F(i,2*D)+F(k,4*D) for i in range(D+1) for k in range(D+1)];nf=len(pcost)
    for j in range(5):
        ids=[i for i,r in enumerate(records) if r['cell']==j];rec=[records[i] for i in ids];nb=len(rec);blocks=sorted({r['block'] for r in rec});bm={b:i for i,b in enumerate(blocks)}
        stop=F(1) if j<4 else (base.PREVIOUS/base.U-base.KNOTS[j])/(base.KNOTS[j+1]-base.KNOTS[j])
        rates=[dyadic_bounds(list(map(F,r['polynomial'])),stop,args.depth) for r in rec]
        coeff=[population_coefficients(r['population_exponents'],D) for r in rec]
        Cpop=np.array([[float(coeff[t][k]) for t in range(nb)] for k in range(nf)])
        budget=csr_matrix((np.ones(nb),(np.array([bm[r['block']] for r in rec]),np.arange(nb))),shape=(len(blocks),nb))
        cost=np.array([float(v) for v in pcost]);objective=np.r_[np.zeros(nb),-1.0];piece=F(0)
        for k in range(N):
            b=[row[k] for row in rates];bfloat=np.array([float(v) for v in b]);scale=max(bfloat.max(),1e-30)
            A=vstack([hstack([budget,csr_matrix((len(blocks),1))]),hstack([csr_matrix(-Cpop*(bfloat/scale)[None,:]),csr_matrix(cost[:,None])])],format='csr')
            result=linprog(objective,A_ub=A,b_ub=np.r_[np.ones(len(blocks)),np.zeros(nf)],bounds=[(0,1)]*nb+[(0,None)],method='highs')
            base.require(result.success,'LP discovery failed')
            # Floor nonnegative weights to rationals, then enforce each budget exactly.
            weights=[F(int(max(0,x)*10**12),10**12) for x in result.x[:-1]]
            for block in blocks:
                indices=[i for i,r in enumerate(rec) if r['block']==block];s=sum((weights[i] for i in indices),F(0))
                if s>1:
                    for i in indices:weights[i]/=s
            selected=[i for i,w in enumerate(weights) if w>0]
            numer=[sum((weights[i]*b[i]*coeff[i][l] for i in selected),F(0)) for l in range(nf)]
            delta=min(numer[l]/pcost[l] for l in range(nf) if pcost[l]>0);base.require(delta>=0 and numer[0]>=0,'population Bernstein certificate')
            a=stop*F(k,N);end=stop*F(k+1,N);piece+=base.U*(base.KNOTS[j+1]-base.KNOTS[j])*(end-a)*delta
            bins.append({'cell':j,'a':str(a),'b':str(end),'delta':str(delta),'allocations':[[ids[i],str(weights[i]),str(b[i])] for i in selected]})
        K+=piece;print('CELL',j,'slack_display',float(piece),'groups',nb,'blocks',len(blocks),flush=True)
    q=base.terminal(source['terminal_grams_by_cell'][4]);den=10**12
    def beta(B):
        p=q.copy();p[0]+=K+base.KAPPA-(B-base.L)
        return base.bernstein(p,36*base.L/base.U-35,36*B/base.U-35)
    lo=int(base.PREVIOUS*den);hi=int(base.U*den)
    base.require(all(x>0 for x in beta(F(lo,den))),'old endpoint not recovered')
    while lo+1<hi:
        mid=(lo+hi)//2
        if all(x>0 for x in beta(F(mid,den))):lo=mid
        else:hi=mid
    target=F(lo,den)
    report=dict(proj,schema='minexposure/validated-population-trajectory-v1',status='producer validated; independent verification required',previous_bound=str(base.PREVIOUS),bound=str(target),bound_decimal=f'{lo//den}.{lo%den:012d}',occupation_slack=str(K),interface_slack=str(base.KAPPA),integration_bins=bins,endpoint_bernstein=list(map(str,beta(target))))
    path=args.output/'population-certificate.json';path.write_text(json.dumps(report,indent=2)+'\n')
    summary={'bound':str(target),'bound_decimal':report['bound_decimal'],'occupation_slack_display':float(K),'projection_records':len(records),'integration_bins':len(bins),'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'status':report['status']};(args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
