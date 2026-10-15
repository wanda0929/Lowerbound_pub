#!/usr/bin/env python3
"""Independent population-slack proof checker. No producer or optimization imports.
Arb interval solves verify matrix order; Fraction arithmetic verifies the entire
population square and cost interval, not samples of a pulse.
"""
from __future__ import annotations
import argparse,gzip,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as R
from math import comb
from flint import arb,arb_mat,ctx
import verify_projected_slack as v
sys.set_int_max_str_digits(0)

def check_projection(rec,meta,src,cache):
    j=rec['cell'];b=rec['block'];d=meta[(j,b)];a,h=rec['anti'],rec['holo']
    v.demand(len(a)==5 and len(h)==5 and all(type(x)is int and x>=0 for x in a+h),'invalid exponents')
    power=[a[i]+h[i] for i in range(1,5)]
    v.demand(power==rec['population_exponents'] and power[1]+power[3]>0,'false population factor')
    v.demand(rec['localizer']==d['localizer'],'false localizer')
    es=rec['entries'];v.demand(len(es)>0 and len({e[0] for e in es})==len(es),'duplicate/empty selection')
    for row,p,c in es:
        tr=d['transform_rows'][row];v.demand(len(tr)==1 and tr[0]['coefficient']==c,'false facial transform')
        index=tr[0]['basis_index'];m=d['basis'][index]['monomial']
        v.demand(m['anti']==a and m['holo']==h and m['cost_power']==p and d['basis_phases'][index]==rec['phase'],'false selected monomial')
    active=rec['active_indices'];rawQ=src['occupation_grams_by_cell'][j][b]
    v.demand(len(set(active))==len(active) and all(type(i)is int and 0<=i<len(rawQ) for i in active),'invalid face')
    if (j,b) not in cache:
        v.demand(all(all(x=='0' for x in rawQ[i]) for i in range(len(rawQ)) if i not in active),'omitted nonzero row')
        Q=arb_mat([[v.scalar(rawQ[i][k]) for k in active] for i in active]);n=len(active)
        # One rigorous preconditioned solve QY=I per original block. This is
        # exactly the collection of selector-column solves used previously.
        identity=arb_mat([[int(i==k) for k in range(n)] for i in range(n)])
        Y=Q.solve(identity,algorithm='precond')
        cache[(j,b)]=(active,Y)
    act,Y=cache[(j,b)];v.demand(active==act,'inconsistent face')
    indices=[active.index(e[0]) for e in es];k=len(indices)
    H=arb_mat([[Y[i,c] for c in indices] for i in indices])
    M=[[R(x) for x in row] for row in rec['reduced_matrix']]
    v.demand(len(M)==k and all(len(row)==k for row in M) and all(M[i][l]==M[l][i] for i in range(k) for l in range(k)),'invalid reduced matrix')
    S=arb_mat([[v.ba(x) for x in row] for row in M]);v.posdef(S);v.posdef(S.inv()-H)
    p=[R(0)]*(2*max(e[1] for e in es)+1)
    for i,(_,ex,c) in enumerate(es):
        for l,(_,ex2,c2) in enumerate(es):p[ex+ex2]+=M[i][l]*c*c2
    loc={'one':[1],'xi':[0,1],'one_minus_xi':[1,-1],'xi_one_minus_xi':[0,1,-1]}[rec['localizer']]
    p=v.times(p,list(map(R,loc)));v.demand(p==list(map(R,rec['polynomial'])),'false projected polynomial')
    return p

def pop_coeff(power,D):
    # Derive via expanding (1-p)^g, then convert to elevated Bernstein basis.
    g,r,h,s=power
    def univariate(a,b):
        poly=[R(0)]*(a+b+1)
        for i in range(b+1):poly[a+i]=R((-1)**i*comb(b,i))
        return [sum((poly[k]*R(comb(j,k),comb(D,k)) for k in range(min(j,len(poly)-1)+1)),R(0)) for j in range(D+1)]
    f=univariate(r,g);z=univariate(s,h)
    return [x*y for x in f for y in z]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--parts-dir',type=Path,required=True);ap.add_argument('--metadata',type=Path,required=True);ap.add_argument('--source-audit',type=Path,required=True);ap.add_argument('--interface-report',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();ctx.prec=384
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)));v.demand(hashlib.sha256(raw).hexdigest()==v.SOURCE,'source hash');src=json.loads(raw);del raw
    v.demand(hashlib.sha256(args.source_audit.read_bytes()).hexdigest()==v.AUDIT,'source audit')
    old=json.loads(args.interface_report.read_text());v.demand(old['status']=='PASS' and R(old['certified_lower_bound'])==v.PREVIOUS and R(old['interface_slack_lower_bound'])==v.KAPPA and old['source_certificate_sha256']==v.SOURCE and old['certificate_sha256']=='de48f592c9ecbb2463bbeb0feb10e913c4a290e218cc50c339cb3ad29a040f2e','preceding theorem')
    data=json.loads(args.certificate.read_text());md=json.loads(args.metadata.read_text());meta={(d['owner']['cell_index'],d['owner_block_index']):d for d in md if d['owner']['measure']=='occupation_cell'}
    v.demand(data['source_certificate_sha256']==v.SOURCE and data['metadata_sha256']==hashlib.sha256(args.metadata.read_bytes()).hexdigest(),'source/basis binding')
    records=data['projection_records'];D=data['degree'];v.demand(type(D)is int and 1<=D<=7,'invalid population degree')
    used=sorted({i for b in data['integration_bins'] for i,w,s in b['allocations']})
    v.demand(all(type(i)is int and 0<=i<len(records) for i in used),'unknown projection')
    polys={};coeffs={};cache={};coordinates=0
    for n,i in enumerate(used):
        rec=records[i];v.demand(sum(rec['population_exponents'])<=D,'degree mismatch')
        polys[i]=check_projection(rec,meta,src,cache);coeffs[i]=pop_coeff(rec['population_exponents'],D);coordinates+=len(rec['entries'])
        if n%100==0:print('VERIFIED',n,'OF',len(used),flush=True)
    cost=[R(i,2*D)+R(j,4*D) for i in range(D+1) for j in range(D+1)];last=[R(0)]*5;K=R(0);positive=0;budgets=0
    for item in data['integration_bins']:
        j=item['cell'];v.demand(type(j)is int and 0<=j<5,'invalid cell');a,b,delta=map(R,[item['a'],item['b'],item['delta']])
        stop=R(1) if j<4 else (v.PREVIOUS/v.U-v.knots[j])/(v.knots[j+1]-v.knots[j])
        v.demand(a==last[j] and 0<=a<b<=stop and delta>=0,'invalid integration interval')
        sums={};numer=[R(0)]*len(cost)
        for i,w,s in item['allocations']:
            weight=R(w);rate=R(s);r=records[i];v.demand(r['cell']==j and weight>0 and rate>=0,'invalid allocation')
            key=r['block'];sums[key]=sums.get(key,R(0))+weight;v.demand(sums[key]<=1,'double-counted Gram budget')
            if rate:v.demand(rate<=v.min_bernstein(polys[i],a,b),'false interval rate')
            for k,c in enumerate(coeffs[i]):numer[k]+=weight*rate*c
        v.demand(all(numer[k]-delta*cost[k]>=0 for k in range(len(cost))),'negative population Bernstein coefficient')
        K+=v.U*(v.knots[j+1]-v.knots[j])*(b-a)*delta;last[j]=b;positive+=sum(numer[k]-delta*cost[k]>0 for k in range(len(cost)));budgets+=len(sums)
    v.demand(all(last[j]==(R(1) if j<4 else (v.PREVIOUS/v.U-v.knots[j])/(v.knots[j+1]-v.knots[j])) for j in range(5)),'incomplete cost coverage')
    v.demand(K==R(data['occupation_slack']) and R(data['interface_slack'])==v.KAPPA,'false integrated slack')
    target=R(data['bound']);v.demand(v.PREVIOUS<target<v.U and R(data['previous_bound'])==v.PREVIOUS,'invalid bound')
    beta=list(map(R,data['endpoint_bernstein']));v.demand(len(beta)==14 and all(x>0 for x in beta),'endpoint signs')
    G0,G1=src['terminal_grams_by_cell'][4];v.demand(R(G0[7][7])==R(G1[6][6]),'endpoint degree')
    for i in range(14):
        t=R(i,13);C=v.L+(target-v.L)*t;xi=36*C/v.U-35;q=R(0)
        for family,G in enumerate([G0,G1]):
            for row,vs in enumerate(G):
                for col,s in enumerate(vs):q+=R(s)*xi**(row+col)*(1 if family==0 else xi*(1-xi))
        expected=q+K+v.KAPPA-(target-v.L);actual=sum((beta[k]*comb(13,k)*t**k*(1-t)**(13-k) for k in range(14)),R(0));v.demand(expected==actual,'endpoint identity')
    out={'status':'PASS','certified_lower_bound':str(target),'previous_lower_bound':str(v.PREVIOUS),'exact_improvement':str(target-v.PREVIOUS),'projection_records_checked':len(used),'original_Gram_blocks_checked':len(cache),'selected_coordinates_checked':coordinates,'cost_intervals_checked':len(data['integration_bins']),'Gram_budget_checks':budgets,'population_Bernstein_inequalities':len(data['integration_bins'])*len(cost),'population_strict_inequalities':positive,'endpoint_exact_interpolation_identities':14,'positive_endpoint_Bernstein_coefficients':14,'Arb_precision_bits':ctx.prec,'optimization_solver_used_in_verifier':False,'floating_tolerance_used':False,'source_certificate_sha256':v.SOURCE,'source_audit_sha256':v.AUDIT,'metadata_sha256':data['metadata_sha256'],'certificate_sha256':hashlib.sha256(args.certificate.read_bytes()).hexdigest(),'occupation_slack':str(K),'interface_slack':str(v.KAPPA),'scope':'all-duration ideal-blockade stationary-torus'}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:x for k,x in out.items() if k!='occupation_slack'},indent=2),flush=True)
if __name__=='__main__':main()
