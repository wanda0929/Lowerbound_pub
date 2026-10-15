#!/usr/bin/env python3
"""Independent standard-library verifier for accumulated interface slack.

No FLINT, matrix solve, or power-to-Bernstein conversion. It checks original
source bytes, each full quadratic-field matrix-vector identity, conservative
rational Schur bounds, and fourteen exact interpolation identities. The
source PSD/identity audit remains an explicit, separately checked dependency.
"""
from __future__ import annotations
import argparse, ast, copy, gzip, hashlib, json, sys
from fractions import Fraction
from math import comb
from pathlib import Path
sys.set_int_max_str_digits(0)
SOURCE='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
AUDIT='001885fa84d5f1819992a8a041e94066eda40f4f6a2fbaaf8b81c8b8bb0f7b53'
Q=Fraction
class K:
    def __init__(self,a=0,b=0):self.a,self.b=Q(a),Q(b)
    def __add__(self,z):return K(self.a+z.a,self.b+z.b)
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,z):return self+-z
    def __mul__(self,z):return K(self.a*z.a+2*self.b*z.b,self.a*z.b+self.b*z.a)
    def __truediv__(self,z):
        d=z.a*z.a-2*z.b*z.b
        return self*K(z.a/d,-z.b/d)
    def __eq__(self,z):return self.a==z.a and self.b==z.b
    def positive(self):
        if self.b==0:return self.a>0
        if self.b>0:
            return self.a>=0 or 2*self.b*self.b>self.a*self.a
        return self.a>0 and self.a*self.a>2*self.b*self.b
class Scalar(ast.NodeVisitor):
    def visit_Expression(self,n):return self.visit(n.body)
    def visit_Constant(self,n):
        check(isinstance(n.value,int),'noninteger scalar literal');return K(n.value)
    def visit_UnaryOp(self,n):
        a=self.visit(n.operand)
        if isinstance(n.op,ast.USub):return -a
        check(isinstance(n.op,ast.UAdd),'invalid unary operator');return a
    def visit_BinOp(self,n):
        a,b=self.visit(n.left),self.visit(n.right)
        if isinstance(n.op,ast.Add):return a+b
        if isinstance(n.op,ast.Sub):return a-b
        if isinstance(n.op,ast.Mult):return a*b
        check(isinstance(n.op,ast.Div),'invalid binary operator');return a/b
    def visit_Call(self,n):
        check(isinstance(n.func,ast.Name) and n.func.id=='sqrt' and len(n.args)==1 and isinstance(n.args[0],ast.Constant) and n.args[0].value==2 and not n.keywords,'invalid radical');return K(0,1)
    def generic_visit(self,n):raise ValueError('unsupported scalar syntax')
def scalar(s):return Scalar().visit(ast.parse(s,mode='eval'))
def check(v,message):
    if not v:raise ValueError(message)
def gram_value(matrix,x):
    result=K()
    for i,row in enumerate(matrix):
        for j,entry in enumerate(row):result=result+entry*K(x**(i+j))
    return result

def verify(c,source,bases):
    check(c['source_certificate_sha256']==SOURCE,'wrong source binding')
    check(source['knots']==['0','1/36','1/3','2/3','35/36','1'] and source['order']==7,'wrong source model')
    L=Q('5861/2000');U=Q('2935887/1000000');B=Q(c['certified_lower_bound'])
    check(Q(source['bound_target'])==L and Q(source['exposure_upper'])==U,'wrong source endpoints')
    check(Q(c['source_bound'])==L and Q(c['previous_bound'])==Q('293095608263/100000000000'),'wrong lower-bound provenance')
    check(U*Q(35,36)<L<Q(c['previous_bound'])<B<U,'invalid exclusion interval')
    check(c['excluded_cost_interval']==[str(L),str(B)],'inconsistent exclusion interval')
    seen=set();total=Q(0);identities=0
    for r in c['interface_records']:
        j,k,i=r['knot_index'],r['block_index'],r['constant_index']
        check(j in range(4) and j not in seen,'duplicate or invalid crossing');seen.add(j)
        raw=source['interface_grams_by_knot'][j][k]
        check(r['gram']==raw and r['basis']==bases[k],'source Gram or basis mismatch')
        check(len(raw)==len(bases[k])==r['dimension'],'wrong dimension')
        m=bases[k][i]
        check(m['cost_power']==0 and len(m['anti'])==len(m['holo'])==4 and all(v==0 for v in m['anti']+m['holo']),'selected coordinate is not constant one')
        n=len(raw);matrix=[[scalar(v) for v in row] for row in raw]
        check(all(len(row)==n for row in matrix),'nonsquare matrix')
        check(all(matrix[a][b]==matrix[b][a] for a in range(n) for b in range(n)),'nonsymmetric matrix')
        y=[K(*v) for v in r['inverse_column']];check(len(y)==n,'wrong inverse column dimension')
        for a in range(n):
            product=K()
            for b in range(n):product=product+matrix[a][b]*y[b]
            check(product==K(int(a==i)),'full inverse-column identity failed');identities+=1
        check(y[i]==K(*r['inverse_diagonal']) and y[i].positive(),'invalid inverse quadratic form')
        gamma=Q(r['gamma']);check(gamma>0 and (K(1)-K(gamma)*y[i]).positive(),'invalid Schur lower bound')
        total+=gamma
    check(seen and total==Q(c['interface_slack_lower_bound']),'incorrect accumulated interface slack')
    check(c['terminal_grams']==source['terminal_grams_by_cell'][4],'terminal source mismatch')
    grams=[[[scalar(v) for v in row] for row in matrix] for matrix in c['terminal_grams']]
    check([len(z) for z in grams]==[8,7] and all(len(row)==len(matrix) for matrix in grams for row in matrix),'terminal dimensions')
    check(grams[0][7][7]==grams[1][6][6],'degree-14 coefficient does not cancel')
    beta=list(map(Q,c['positive_bernstein_coefficients']))
    check(len(beta)==14 and all(v>0 for v in beta),'nonpositive Bernstein coefficient')
    check(Q(c['minimum_positive_margin'])==min(beta),'wrong margin')
    for k in range(14):
        t=Q(k,13);cost=L+(B-L)*t;x=36*cost/U-35
        left=gram_value(grams[0],x)+K(x*(1-x))*gram_value(grams[1],x)+K(total-(B-L))
        right=sum((beta[i]*comb(13,i)*t**i*(1-t)**(13-i) for i in range(14)),Q(0))
        check(left==K(right),'exact degree-13 interpolation identity failed')
    return {'status':'PASS','certified_lower_bound':str(B),'mandatory_crossings':len(seen),'full_quadratic_field_row_identities':identities,'exact_interpolation_identities':14,'strictly_positive_bernstein_coefficients':14,'interface_slack_lower_bound':str(total),'floating_point_used':False}

def rejection_tests(c,source,bases):
    tests=[]
    def trial(name,change):
        mutant=copy.deepcopy(c);change(mutant)
        try:verify(mutant,source,bases)
        except (ValueError,IndexError,ZeroDivisionError):tests.append(name);return
        raise ValueError('mutation incorrectly accepted: '+name)
    trial('wrong source hash',lambda d:d.update(source_certificate_sha256='0'*64))
    trial('wrong target',lambda d:d.update(certified_lower_bound=str(Q(d['certified_lower_bound'])+Q(1,10000))))
    trial('wrong accumulated slack',lambda d:d.update(interface_slack_lower_bound=str(2*Q(d['interface_slack_lower_bound']))))
    trial('duplicate crossing',lambda d:d['interface_records'].append(copy.deepcopy(d['interface_records'][0])))
    trial('negative Bernstein coefficient',lambda d:d['positive_bernstein_coefficients'].__setitem__(0,'-1'))
    trial('altered source Gram',lambda d:d['interface_records'][0]['gram'][0].__setitem__(0,'123456'))
    trial('invalid Schur bound',lambda d:d['interface_records'][0].update(gamma='1000000'))
    def alter_y(d):
        r=d['interface_records'][0];i=r['constant_index'];r['inverse_column'][i][0]=str(Q(r['inverse_column'][i][0])+1)
    trial('altered inverse column',alter_y)
    trial('nonconstant coordinate',lambda d:d['interface_records'][0].update(constant_index=d['interface_records'][0]['constant_index']+1))
    return tests

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--certificate',type=Path,required=True);p.add_argument('--parts-dir',type=Path,required=True)
    p.add_argument('--bases',type=Path,required=True);p.add_argument('--source-audit',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--self-test',action='store_true')
    a=p.parse_args()
    raw=gzip.decompress(b''.join((a.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)))
    check(hashlib.sha256(raw).hexdigest()==SOURCE,'full source SHA256 failed')
    source=json.loads(raw);del raw
    auditraw=a.source_audit.read_bytes();check(hashlib.sha256(auditraw).hexdigest()==AUDIT,'unexpected full source audit bytes')
    audit=json.loads(auditraw)
    check(audit['nonzero_exact_residual_count']==0 and audit['all_gram_matrices_exactly_positive_semidefinite'] and Q(audit['certified_bound'])==Q('5861/2000'),'source audit failed')
    c=json.loads(a.certificate.read_text());basisraw=a.bases.read_bytes()
    check(hashlib.sha256(basisraw).hexdigest()==c['basis_sha256'],'native basis hash mismatch')
    bases=json.loads(basisraw);result=verify(c,source,bases)
    if a.self_test:
        result['rejected_mutations']=rejection_tests(c,source,bases)
        result['tests_passed']=1+len(result['rejected_mutations'])
    result['source_certificate_sha256']=SOURCE;result['source_audit_sha256']=AUDIT
    result['new_certificate_sha256']=hashlib.sha256(a.certificate.read_bytes()).hexdigest()
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
