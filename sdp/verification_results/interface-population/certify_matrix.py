#!/usr/bin/env python3
"""Matrix-budget crossing producer. All floating optimization is discovery.
Final weights pass rigorously enclosed LDL and exact population inequalities.
The independent verify.py accepts neither eigenvectors nor LP tolerances.
"""
import argparse,gzip,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
import numpy as np
from scipy.optimize import linprog
from scipy.linalg import eigh
from scipy.sparse import csr_matrix,hstack,vstack
from flint import arb_mat,ctx,fmpq as Q
import certify as scalar_producer
v=scalar_producer.v
P=scalar_producer.P
sys.set_int_max_str_digits(0)

def candidates(source,bases,j,D):
    records=[];matrices={}
    for b,raw in enumerate(source['interface_grams_by_knot'][j]):
        active=[i for i,row in enumerate(raw) if any(x!='0' for x in row)]
        if not active:continue
        M=arb_mat([[v.scalar(raw[i][k]) for k in active] for i in active])
        try:H=M.inv()
        except (ZeroDivisionError,ValueError):continue
        best={};am={i:k for k,i in enumerate(active)}
        for k,i in enumerate(active):
            m=bases[b][i];ex=tuple(a+h for a,h in zip(m['anti'],m['holo']))
            assert sum(ex)<=D and m['cost_power']==0
            if not H[k,k]>0:continue
            gamma=F(int(((1/H[k,k]).lower().fmpq()*Q(10**18)).floor()),10**18)
            if gamma>0 and (ex not in best or gamma>best[ex][0]):best[ex]=(gamma,i)
        ids=[]
        for ex,(gamma,i) in best.items():
            assert 1/v.ba(gamma)-H[am[i],am[i]]>0
            ids.append(len(records));records.append({'knot':j,'block':b,'row':i,'active_indices':active,'population_exponents':list(ex),'gamma':str(gamma)})
        if not ids:continue
        selected=[am[records[i]['row']] for i in ids];g=np.sqrt([float(F(records[i]['gamma'])) for i in ids]);HF=np.array([[float(H[i,k].mid()) for k in selected] for i in selected]);HF=HF*g[:,None]*g[None,:]
        w,V=eigh((HF+HF.T)/2);R=np.sqrt(np.maximum(w,0))[:,None]*V.T
        matrices[b]={'M':M,'ids':ids,'R':R,'active':active}
    return records,matrices

def optimize(records,matrices,D,depth):
    n=len(records);pop=[scalar_producer.restricted(scalar_producer.pc(r['population_exponents'],D),D,depth) for r in records];nf=len(pop[0]);g=[F(r['gamma']) for r in records];scale=max(map(float,g))
    C=np.array([[float(x) for x in row] for row in pop]).T*np.array([float(x)/scale for x in g])[None,:]
    population=hstack([csr_matrix(-C),csr_matrix(np.ones((nf,1)))],format='csr');cuts=[];points=np.ones(n);solution=None
    for step in range(40):
        added=0;maxrho=0.
        for b,d in matrices.items():
            ids=d['ids'];R=d['R'];A=(R*points[ids][None,:])@R.T;w,V=eigh((A+A.T)/2);maxrho=max(maxrho,float(w[-1]))
            if w[-1]>1+1e-9:
                for k in np.argsort(w)[-3:]:
                    if w[k]<=1+1e-9:continue
                    coefficient=(R.T@V[:,k])**2;cuts.append(csr_matrix((coefficient,(np.zeros(len(ids),dtype=int),np.array(ids))),shape=(1,n+1)));added+=1
        if solution is not None and added==0:break
        A=vstack([population]+cuts,format='csr');rhs=np.r_[np.zeros(nf),np.ones(len(cuts))]
        result=linprog(np.r_[np.zeros(n),-1.],A_ub=A,b_ub=rhs,bounds=[(0,1)]*n+[(0,None)],method='highs');assert result.success
        solution=result;points=np.maximum(0,result.x[:-1]);print('CUT_ITERATION',step,'objective',result.x[-1]*scale,'max_rho',maxrho,'cuts',len(cuts),flush=True)
    weights=[F(int(x*10**12),10**12) for x in points]
    # Rigorous repair checks original matrices, not their discovery eigensystems.
    for b,d in matrices.items():
        ids=d['ids'];R=d['R'];A=(R*np.array([float(weights[i]) for i in ids])[None,:])@R.T;rho=float(eigh((A+A.T)/2,eigvals_only=True)[-1]);factor=F(int(min(1.,(1-1e-7)/max(rho,1e-30))*10**12),10**12)
        trial=[weights[i]*factor for i in ids];active=d['active'];am={i:k for k,i in enumerate(active)}
        for attempt in range(12):
            M=arb_mat(d['M']);discount={}
            for i,w in zip(ids,trial):
                k=am[records[i]['row']];discount[k]=discount.get(k,F(0))+w*g[i]
            for k,value in discount.items():M[k,k]-=v.ba(value)
            try:v.posdef(M);break
            except ValueError:
                trial=[w*F(99,100) for w in trial]
        else:raise ValueError('matrix repair failed')
        for i,w in zip(ids,trial):weights[i]=w
    coefficients=[Q(0)]*nf
    for i,w in enumerate(weights):
        if w:
            rate=Q(str(w*g[i]))
            for k,c in enumerate(pop[i]):coefficients[k]+=rate*c
    bound=F(str(min(coefficients)));assert bound>0
    return weights,bound,len(cuts)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parts-dir',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--depth',type=int,default=1);args=ap.parse_args();ctx.prec=384;args.output.mkdir(parents=True,exist_ok=True);D=7
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)));assert hashlib.sha256(raw).hexdigest()==v.SOURCE;source=json.loads(raw);del raw
    basisraw=(P/'certified/interface-bases.json').read_bytes();bases=json.loads(basisraw);basefile=P/'certified/subdivision-certificate.json';base=json.loads(basefile.read_text());old=F(base['bound'])
    retained=[];crossings=[];K=F(0);totalcuts=0
    for j in range(4):
        rec,mats=candidates(source,bases,j,D);print('CANDIDATES',j,len(rec),len(mats),flush=True)
        weights,bound,cuts=optimize(rec,mats,D,args.depth);totalcuts+=cuts;allocation=[]
        for r,w in zip(rec,weights):
            if w:allocation.append([len(retained),str(w)]);retained.append(r)
        crossings.append({'knot':j,'bound':str(bound),'allocations':allocation});K+=bound
        print('CROSSING_RESULT',j,float(bound),len(allocation),flush=True)
    assert K>v.KAPPA
    poly=scalar_producer.power_from_bernstein(list(map(F,base['endpoint_bernstein'])))
    def endpoint(B):
        rho=(B-v.L)/(old-v.L);p=[a*rho**i for i,a in enumerate(poly)];p[0]+=K-v.KAPPA-(B-old);return scalar_producer.bernstein_from_power(p)
    den=10**12;lo=int(old*den);hi=int(v.U*den)
    while lo+1<hi:
        mid=(lo+hi)//2
        if all(x>0 for x in endpoint(F(mid,den))):lo=mid
        else:hi=mid
    B=F(lo,den);cert={'schema':'minexposure/full-population-interface-v1','status':'producer rigorously repaired; independent verification required','source_certificate_sha256':v.SOURCE,'bases_sha256':hashlib.sha256(basisraw).hexdigest(),'base_certificate_sha256':hashlib.sha256(basefile.read_bytes()).hexdigest(),'base_bound':str(old),'bound':str(B),'bound_decimal':f'{lo//den}.{lo%den:012d}','degree':D,'population_subdivision_depth':args.depth,'old_interface_slack':str(v.KAPPA),'new_interface_slack':str(K),'records':retained,'crossings':crossings,'endpoint_bernstein':list(map(str,endpoint(B))),'discovery':'eigenvector cutting-plane LP, followed by original-matrix rigorous repair','cut_count':totalcuts}
    out=args.output/'certificate.json';out.write_text(json.dumps(cert,indent=2)+'\n');summary={k:cert[k] for k in ['status','bound','bound_decimal','base_bound','cut_count']};summary.update(exact_increase=str(B-old),interface_slack_display=float(K),records=len(retained),certificate_sha256=hashlib.sha256(out.read_bytes()).hexdigest());(args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
