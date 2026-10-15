#!/usr/bin/env python3
"""Independent validated verifier, not importing the producer.
Checks projections by the inverse-order criterion S^{-1}-E^T Q^{-1}E > 0
using rigorously enclosed solves at 384 bits, rather than producer midpoint
rounding/Gershgorin. Source PSD and preceding interface theorem are dependencies.
"""
import argparse, ast, gzip, hashlib, json, sys
from pathlib import Path
from fractions import Fraction as R
from math import comb
from flint import arb, arb_mat, fmpq, ctx
sys.set_int_max_str_digits(0)
SOURCE='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
AUDIT='001885fa84d5f1819992a8a041e94066eda40f4f6a2fbaaf8b81c8b8bb0f7b53'
PREVIOUS=R('2930957146313/1000000000000');U=R('2935887/1000000');L=R('5861/2000');KAPPA=R('1107565238703/1000000000000000000')
knots=list(map(R,['0','1/36','1/3','2/3','35/36','1']))
def demand(v,msg):
    if not v:raise ValueError(msg)
def ba(v):return arb(fmpq(str(v)))
def scalar(s):
    def walk(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return arb(n.value)
        if isinstance(n,ast.UnaryOp):
            if isinstance(n.op,ast.USub):return -walk(n.operand)
            if isinstance(n.op,ast.UAdd):return walk(n.operand)
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='sqrt' and len(n.args)==1 and isinstance(n.args[0],ast.Constant) and n.args[0].value==2 and not n.keywords:return arb(2).sqrt()
        if isinstance(n,ast.BinOp):
            a,b=walk(n.left),walk(n.right)
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
            if isinstance(n.op,ast.Div):return a/b
        raise ValueError('invalid exact scalar syntax')
    return walk(ast.parse(s,mode='eval').body)
def posdef(M):
    n=M.nrows();work=[[M[i,j] for j in range(n)] for i in range(n)]
    for k in range(n):
        pivot=work[k][k];demand(pivot>0,'uncertified positive LDL pivot')
        for i in range(k+1,n):
            for j in range(i,n):
                x=work[j][i]-work[i][k]*work[j][k]/pivot
                work[j][i]=work[i][j]=x

def times(a,b):
    result=[R(0)]*(len(a)+len(b)-1)
    for i in range(len(a)):
        for j in range(len(b)):result[i+j]+=a[i]*b[j]
    return result

def min_bernstein(p,a,b):
    # Compose by Horner, independently of producer's binomial affine expansion.
    h=[R(0)]
    for c in reversed(p):
        h=times(h,[a,b-a]);h[0]+=c
    while len(h)>1 and h[-1]==0:h.pop()
    n=len(h)-1
    return min(sum((h[j]*R(comb(i,j),comb(n,j)) for j in range(i+1)),R(0)) for i in range(n+1))
def evaluate(p,x):
    v=R(0)
    for c in reversed(p):v=v*x+c
    return v

def verify(args):
    ctx.prec=384
    raw=gzip.decompress(b''.join((args.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)))
    demand(hashlib.sha256(raw).hexdigest()==SOURCE,'source certificate hash');src=json.loads(raw);del raw
    demand(hashlib.sha256(args.source_audit.read_bytes()).hexdigest()==AUDIT,'full source audit hash')
    old=json.loads(args.interface_report.read_text())
    demand(old['status']=='PASS' and R(old['certified_lower_bound'])==PREVIOUS and R(old['interface_slack_lower_bound'])==KAPPA,'preceding interface report')
    data=json.loads(args.certificate.read_text());meta=json.loads(args.metadata.read_text())
    demand(data['source_certificate_sha256']==SOURCE,'certificate source binding')
    demand(data['metadata_sha256']==hashlib.sha256(args.metadata.read_bytes()).hexdigest(),'metadata binding')
    lookup={(d['owner']['cell_index'],d['owner_block_index']):d for d in meta if d['owner']['measure']=='occupation_cell'}
    polys=[[[R(0)]*15 for k in range(2)] for j in range(5)];weights={};identities=0;cache={}
    locs={'one':[1],'xi':[0,1],'one_minus_xi':[1,-1],'xi_one_minus_xi':[0,1,-1]}
    for rec in data['projection_records']:
        j=rec['cell'];b=rec['block'];key=(j,b);d=lookup[key]
        w=R(rec['weight']);demand(w>0,'nonpositive budget');weights[key]=weights.get(key,R(0))+w
        demand(weights[key]<=1,'Gram budget double counting')
        demand(rec['localizer']==d['localizer'],'localizer mismatch')
        sector=rec['sector'];demand(sector in (1,2),'sector')
        a,h=rec['anti'],rec['holo'];e=[a[i]+h[i] for i in range(5)]
        demand(len(a)==5 and len(h)==5 and all(type(v)is int and v>=0 for v in a+h),'invalid exponents')
        demand(e[1]==0 and e[3]==0 and e[2]+e[4]==1 and e[2*sector]==1,'false Rydberg factor')
        entries=rec['entries'];demand(len({v[0] for v in entries})==len(entries),'duplicate row')
        for row,power,coef in entries:
            tr=d['transform_rows'][row];demand(len(tr)==1 and tr[0]['coefficient']==coef,'false transform')
            bi=tr[0]['basis_index'];m=d['basis'][bi]['monomial']
            demand(m['anti']==a and m['holo']==h and m['cost_power']==power,'false selected monomial')
            demand(d['basis_phases'][bi]==rec['phase'],'inconsistent complex phase')
        active=rec['active_indices'];rawQ=src['occupation_grams_by_cell'][j][b]
        demand(len(set(active))==len(active) and all(0<=i<len(rawQ) for i in active),'invalid active rows')
        if key not in cache:
            # Omitted rows must be literally exact zero; rejecting a differently
            # encoded zero is conservative, never accepting an omitted nonzero.
            demand(all(all(s=='0' for s in rawQ[i]) for i in range(len(rawQ)) if i not in active),'omitted nonzero row')
            Q=arb_mat([[scalar(rawQ[i][k]) for k in active] for i in active]);cache[key]=(active,Q)
        cached_active,Q=cache[key];demand(active==cached_active,'inconsistent active face')
        indices=[active.index(v[0]) for v in entries];n=len(active);k=len(indices)
        rhs=arb_mat([[int(i==indices[c]) for c in range(k)] for i in range(n)])
        Y=Q.solve(rhs,algorithm='precond')
        H=arb_mat([[Y[i,c] for c in range(k)] for i in indices])
        M=[[R(v) for v in row] for row in rec['reduced_matrix']]
        demand(len(M)==k and all(len(row)==k for row in M),'reduced dimension')
        demand(all(M[i][r]==M[r][i] for i in range(k) for r in range(k)),'reduced symmetry')
        S=arb_mat([[ba(v) for v in row] for row in M]);posdef(S);posdef(S.inv()-H)
        p=[R(0)]*(2*max(v[1] for v in entries)+1)
        for i,(_,power,coef) in enumerate(entries):
            for r,(_,power2,coef2) in enumerate(entries):p[power+power2]+=w*coef*coef2*M[i][r]
        p=times(p,list(map(R,locs[rec['localizer']])))
        for i,v in enumerate(p):polys[j][sector-1][i]+=v
        identities+=k
        if identities%50<k:print('VERIFIED_PROJECTED_COORDINATES',identities,flush=True)
    K=R(0);last=[R(0)]*5;bins_count=0
    for b in data['integration_bins']:
        j=b['cell'];a=R(b['a']);c=R(b['b']);delta=R(b['delta'])
        stop=R(1) if j<4 else (PREVIOUS/U-knots[j])/(knots[j+1]-knots[j])
        demand(a==last[j] and 0<=a<c<=stop and delta>=0,'invalid integration partition')
        if delta:
            demand(delta<=min_bernstein([2*x for x in polys[j][0]],a,c),'sector 1 polynomial lower bound')
            demand(delta<=min_bernstein([4*x for x in polys[j][1]],a,c),'sector 2 polynomial lower bound')
        K+=U*(knots[j+1]-knots[j])*(c-a)*delta;last[j]=c;bins_count+=1
    demand(all(last[j]==(R(1) if j<4 else (PREVIOUS/U-knots[j])/(knots[j+1]-knots[j])) for j in range(5)),'incomplete partition')
    demand(K==R(data['occupation_slack']) and KAPPA==R(data['interface_slack']),'false accumulated slack')
    target=R(data['bound']);demand(PREVIOUS<target<U and R(data['previous_bound'])==PREVIOUS,'invalid target')
    beta=list(map(R,data['endpoint_bernstein']));demand(len(beta)==14 and all(x>0 for x in beta),'endpoint Bernstein signs')
    # Direct source-Gram evaluation at fourteen exact nodes; no producer q used.
    for i in range(14):
        t=R(i,13);C=L+(target-L)*t;xi=36*C/U-35;value=R(0)
        for family,G in enumerate(src['terminal_grams_by_cell'][4]):
            for r,row in enumerate(G):
                for c,v in enumerate(row):value+=R(v)*xi**(r+c)*(1 if family==0 else xi*(1-xi))
        expected=value+K+KAPPA-(target-L)
        actual=sum((beta[k]*comb(13,k)*t**k*(1-t)**(13-k) for k in range(14)),R(0))
        demand(expected==actual,'endpoint interpolation identity')
    G0,G1=src['terminal_grams_by_cell'][4];demand(R(G0[7][7])==R(G1[6][6]),'degree-14 cancellation')
    output={'status':'PASS','certified_lower_bound':str(target),'validated_precision_bits':ctx.prec,'projected_blocks':len(weights),'projected_coordinate_count':identities,'projection_records':len(data['projection_records']),'integration_bins':bins_count,'occupation_slack':str(K),'interface_slack':str(KAPPA),'endpoint_exact_interpolation_identities':14,'positive_endpoint_bernstein_coefficients':14,'source_certificate_sha256':SOURCE,'source_audit_sha256':AUDIT,'certificate_sha256':hashlib.sha256(args.certificate.read_bytes()).hexdigest(),'scope':'all-duration, no waveform restriction','acceptance':'rigorous Arb matrix enclosures plus exact rational polynomial arithmetic; no floating tolerances'}
    args.output.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--certificate',type=Path,required=True);p.add_argument('--parts-dir',type=Path,required=True);p.add_argument('--metadata',type=Path,required=True);p.add_argument('--source-audit',type=Path,required=True);p.add_argument('--interface-report',type=Path,required=True);p.add_argument('--output',type=Path,required=True);verify(p.parse_args())
