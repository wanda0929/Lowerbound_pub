#!/usr/bin/env python3
"""Discover and rigorously check scalar Schur bounds at mandatory crossings.
LP is discovery only. This producer requires separate independent verification.
"""
import argparse,gzip,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
from flint import arb,arb_mat,ctx,fmpq as Q
sys.set_int_max_str_digits(0)
P=Path(__file__).resolve().parents[1]/'population-refinement'
sys.path.insert(0,str(P))
import verify_projected_slack as v
from certify_population_subdivision import power_from_bernstein,bernstein_from_power,partition

def pc(ex,D):
    g,r,h,s=ex
    def row(a,b):
        return [Q(comb(D-a-b,i-a),comb(D,i)) if a<=i<=D-b else Q(0) for i in range(D+1)]
    return [a*b for a in row(r,g) for b in row(s,h)]

def restricted(cs,D,depth):
    n=D+1;N=1<<depth;M=[cs[i*n:(i+1)*n] for i in range(n)]
    columns=[partition([M[i][j] for i in range(n)],depth) for j in range(n)];out=[]
    for x in range(N):
        rows=[partition([columns[j][x][i] for j in range(n)],depth) for i in range(n)]
        for y in range(N):out.extend(rows[i][y][j] for i in range(n) for j in range(n))
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parts-dir',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--depth',type=int,default=1);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True);ctx.prec=256;D=7
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)));assert hashlib.sha256(raw).hexdigest()==v.SOURCE;source=json.loads(raw);del raw
    bases=json.loads((P/'certified/interface-bases.json').read_text());bp=P/'certified/subdivision-certificate.json';base=json.loads(bp.read_text());old=F(base['bound']);records=[];cross=[];K=F(0);pops={}
    for j,grams in enumerate(source['interface_grams_by_knot']):
        start=len(records)
        for b,rawQ in enumerate(grams):
            assert len(rawQ)==len(bases[b])
            active=[i for i,row in enumerate(rawQ) if any(x!='0' for x in row)]
            if not active:continue
            M=arb_mat([[v.scalar(rawQ[i][k]) for k in active] for i in active])
            try:H=M.inv()
            except (ZeroDivisionError,ValueError):continue
            best={}
            for ii,i in enumerate(active):
                m=bases[b][i];ex=tuple(a+h for a,h in zip(m['anti'],m['holo']));assert len(ex)==4 and sum(ex)<=D and m['cost_power']==0
                if not H[ii,ii]>0:continue
                g=(1/H[ii,ii]).lower().fmpq();gamma=F(int((g*Q(10**18)).floor()),10**18)
                if gamma<=0:continue
                assert 1/v.ba(gamma)-H[ii,ii]>0
                if ex not in best or gamma>best[ex][0]:best[ex]=(gamma,i)
            for ex,(gamma,i) in best.items():
                records.append({'knot':j,'block':b,'row':i,'active_indices':active,'population_exponents':list(ex),'gamma':str(gamma)})
            if b%50==0:print('BLOCK',j,b,'candidates',len(records)-start,flush=True)
        ids=list(range(start,len(records)));blocks=sorted({records[i]['block'] for i in ids});bm={b:k for k,b in enumerate(blocks)}
        for i in ids:
            ex=tuple(records[i]['population_exponents'])
            if ex not in pops:pops[ex]=restricted(pc(ex,D),D,args.depth)
        coeff=[pops[tuple(records[i]['population_exponents'])] for i in ids];gamma=[F(records[i]['gamma']) for i in ids];scale=max(map(float,gamma));nf=len(coeff[0]);n=len(ids)
        A=np.array([[float(c) for c in row] for row in coeff]).T*np.array([float(g)/scale for g in gamma])[None,:]
        budget=csr_matrix((np.ones(n),(np.array([bm[records[i]['block']] for i in ids]),np.arange(n))),shape=(len(blocks),n))
        res=linprog(np.r_[np.zeros(n),-1.],A_ub=vstack([hstack([budget,csr_matrix((len(blocks),1))]),hstack([csr_matrix(-A),csr_matrix(np.ones((nf,1)))])],format='csr'),b_ub=np.r_[np.ones(len(blocks)),np.zeros(nf)],bounds=[(0,1)]*n+[(0,None)],method='highs');assert res.success
        weights=[F(int(max(x,0)*10**12),10**12) for x in res.x[:-1]]
        for b in blocks:
            jj=[k for k,i in enumerate(ids) if records[i]['block']==b];s=sum((weights[k] for k in jj),F(0))
            if s>1:
                for k in jj:weights[k]/=s
        chosen=[k for k,w in enumerate(weights) if w];cs=[Q(0)]*nf
        for k in chosen:
            rate=Q(str(weights[k]*gamma[k]))
            for l,c in enumerate(coeff[k]):cs[l]+=rate*c
        bound=F(str(min(cs)));assert bound>0;K+=bound
        cross.append({'knot':j,'bound':str(bound),'allocations':[[ids[k],str(weights[k])] for k in chosen]});print('CROSSING',j,'bound',float(bound),'selected',len(chosen),flush=True)
    oldK=v.KAPPA;assert K>oldK
    p=power_from_bernstein(list(map(F,base['endpoint_bernstein'])))
    def endpoint(B):
        rho=(B-v.L)/(old-v.L);poly=[a*rho**i for i,a in enumerate(p)];poly[0]+=K-oldK-(B-old);return bernstein_from_power(poly)
    den=10**12;lo=int(old*den);hi=int(v.U*den)
    while lo+1<hi:
        mid=(lo+hi)//2
        if all(x>0 for x in endpoint(F(mid,den))):lo=mid
        else:hi=mid
    B=F(lo,den);assert B>old
    used={i for item in cross for i,w in item['allocations']};mapping={i:k for k,i in enumerate(sorted(used))};selected=[records[i] for i in sorted(used)]
    for item in cross:item['allocations']=[[mapping[i],w] for i,w in item['allocations']]
    cert={'schema':'minexposure/full-population-interface-v1','status':'producer passed; independent verification required','source_certificate_sha256':v.SOURCE,'bases_sha256':hashlib.sha256((P/'certified/interface-bases.json').read_bytes()).hexdigest(),'base_certificate_sha256':hashlib.sha256(bp.read_bytes()).hexdigest(),'base_bound':str(old),'bound':str(B),'bound_decimal':f'{lo//den}.{lo%den:012d}','degree':D,'population_subdivision_depth':args.depth,'old_interface_slack':str(oldK),'new_interface_slack':str(K),'records':selected,'crossings':cross,'endpoint_bernstein':list(map(str,endpoint(B)))}
    f=args.output/'certificate.json';f.write_text(json.dumps(cert,indent=2)+'\n');summary={k:cert[k] for k in ['status','base_bound','bound','bound_decimal','new_interface_slack']};summary.update(exact_increase=str(B-old),new_interface_slack_display=float(K),records=len(selected),certificate_sha256=hashlib.sha256(f.read_bytes()).hexdigest());(args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
