#!/usr/bin/env python3
"""Independent exact verification of state-normalized crossing penalties.

Uses no producer code, FLINT, matrix inversion, optimizer, or Bernstein
conversion. Full original source bytes and the separate source audit are
required. All new identities are checked in the standard library.
"""
from __future__ import annotations
import argparse,copy,gzip,hashlib,json,sys
from fractions import Fraction as Q
from math import comb
from pathlib import Path
from verify_interface_slack import K,scalar,check,gram_value,SOURCE,AUDIT
sys.set_int_max_str_digits(0)

def label(m):
    check(m['cost_power']==0 and len(m['anti'])==len(m['holo'])==4,'invalid state-only monomial')
    e=[a+b for a,b in zip(m['anti'],m['holo'])]
    if all(v==0 for v in e):return 'constant'
    check(sum(e)==1 and all(v in (0,1) for v in e),'not a degree-one state monomial')
    return ('g1','r1','g2','r2')[e.index(1)]

def verify(c,source,bases):
    check(c['schema']=='minexposure/exact-normalized-interface-terminal-slack-v1' and c['source_certificate_sha256']==SOURCE,'wrong schema or source')
    check(source['knots']==['0','1/36','1/3','2/3','35/36','1'] and source['order']==7,'wrong source formulation')
    L=Q('5861/2000');U=Q('2935887/1000000');B=Q(c['certified_lower_bound'])
    check(Q(source['bound_target'])==L and Q(source['exposure_upper'])==U,'source endpoint mismatch')
    check(Q(c['source_bound'])==L and Q(c['previous_bound'])==Q('293095608263/100000000000'),'bound provenance mismatch')
    check(35*U/36<L<Q(c['previous_bound'])<B<U,'invalid counterexample sublevel')
    check(c['excluded_cost_interval']==[str(L),str(B)],'exclusion interval mismatch')
    gains=[{} for _ in range(4)];seen=set();rows=0
    for r in c['interface_records']:
        j,k,i=r['knot_index'],r['block_index'],r['feature_index'];n=r['dimension']
        check(j in range(4) and (j,k) not in seen,'Gram budget double counted');seen.add((j,k))
        check(r['gram']==source['interface_grams_by_knot'][j][k] and r['basis']==bases[k],'source block or basis mismatch')
        check(len(r['gram'])==len(bases[k])==n,'dimension mismatch')
        name=label(bases[k][i]);check(name==r['feature'] and name not in gains[j],'feature mismatch or repetition')
        matrix=[[scalar(v) for v in row] for row in r['gram']]
        check(all(len(row)==n for row in matrix),'nonsquare matrix')
        check(all(matrix[a][b]==matrix[b][a] for a in range(n) for b in range(n)),'Gram symmetry failure')
        y=[K(*v) for v in r['inverse_column']];check(len(y)==n,'inverse column dimension')
        for a in range(n):
            s=K()
            for b in range(n):s=s+matrix[a][b]*y[b]
            check(s==K(int(a==i)),'exact inverse-column identity failed');rows+=1
        check(y[i]==K(*r['inverse_diagonal']) and y[i].positive(),'inverse diagonal failure')
        gamma=Q(r['gamma']);check(gamma>0 and (K(1)-K(gamma)*y[i]).positive(),'Schur inequality failed')
        gains[j][name]=gamma
    total=Q(0)
    for j,g in enumerate(gains):
        value=g.get('constant',Q(0))+min(g.get('g1',Q(0)),g.get('r1',Q(0)))+min(g.get('g2',Q(0)),g.get('r2',Q(0)))
        summary=c['interface_summaries'][j]
        check(summary['knot_index']==j and {k:Q(v) for k,v in summary['feature_bounds'].items()}==g and Q(summary['uniform_interface_bound'])==value,'invalid norm-identity accumulation')
        total+=value
    check(total>0 and total==Q(c['interface_slack_lower_bound']),'total mandatory slack mismatch')
    check(c['terminal_grams']==source['terminal_grams_by_cell'][4],'terminal source mismatch')
    grams=[[[scalar(v) for v in row] for row in G] for G in c['terminal_grams']]
    check([len(G) for G in grams]==[8,7] and all(len(row)==len(G) for G in grams for row in G),'terminal dimensions')
    check(grams[0][7][7]==grams[1][6][6],'degree-14 cancellation failed')
    beta=list(map(Q,c['positive_bernstein_coefficients']))
    check(len(beta)==14 and all(v>0 for v in beta) and min(beta)==Q(c['minimum_positive_margin']),'Bernstein positivity failure')
    for k in range(14):
        t=Q(k,13);x=36*(L+(B-L)*t)/U-35
        left=gram_value(grams[0],x)+K(x*(1-x))*gram_value(grams[1],x)+K(total-(B-L))
        right=sum((beta[i]*comb(13,i)*t**i*(1-t)**(13-i) for i in range(14)),Q(0))
        check(left==K(right),'exact interpolation identity failed')
    return {'status':'PASS','certified_lower_bound':str(B),'gram_blocks':len(seen),'exact_quadratic_field_row_identities':rows,'mandatory_crossings':4,'exact_interpolation_identities':14,'strictly_positive_bernstein_coefficients':14,'interface_slack_lower_bound':str(total),'floating_point_used_for_acceptance':False}

def tests(c,source,bases):
    passed=[]
    def trial(name,fn):
        z=copy.deepcopy(c);fn(z)
        try:verify(z,source,bases)
        except (ValueError,IndexError,ZeroDivisionError):passed.append(name);return
        raise ValueError('incorrectly accepted mutation: '+name)
    trial('source hash',lambda d:d.update(source_certificate_sha256='0'*64))
    trial('Gram double counting',lambda d:d['interface_records'].append(copy.deepcopy(d['interface_records'][0])))
    trial('false feature',lambda d:d['interface_records'][0].update(feature='not a state variable'))
    trial('false total slack',lambda d:d.update(interface_slack_lower_bound=str(2*Q(d['interface_slack_lower_bound']))))
    trial('false norm bound',lambda d:d['interface_summaries'][0].update(uniform_interface_bound='1000'))
    trial('false Schur margin',lambda d:d['interface_records'][0].update(gamma='1000000000'))
    trial('changed Gram',lambda d:d['interface_records'][0]['gram'][0].__setitem__(0,'1000'))
    trial('negative Bernstein coefficient',lambda d:d['positive_bernstein_coefficients'].__setitem__(0,'-1'))
    trial('changed terminal Gram',lambda d:d['terminal_grams'][0][0].__setitem__(0,'1000'))
    trial('changed target',lambda d:d.update(certified_lower_bound=str(Q(d['certified_lower_bound'])+Q(1,1000))))
    def change_y(d):
        r=d['interface_records'][0];i=r['feature_index'];r['inverse_column'][i][0]=str(Q(r['inverse_column'][i][0])+1)
    trial('changed inverse column',change_y)
    return passed

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['certificate','parts-dir','bases','source-audit','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--self-test',action='store_true');a=p.parse_args()
    raw=gzip.decompress(b''.join((a.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)))
    check(hashlib.sha256(raw).hexdigest()==SOURCE,'full source SHA256 failed');source=json.loads(raw);del raw
    raw=a.source_audit.read_bytes();check(hashlib.sha256(raw).hexdigest()==AUDIT,'source audit hash failed')
    audit=json.loads(raw);check(audit['nonzero_exact_residual_count']==0 and audit['all_gram_matrices_exactly_positive_semidefinite'] and Q(audit['certified_bound'])==Q('5861/2000'),'source audit failed')
    c=json.loads(a.certificate.read_text());raw=a.bases.read_bytes();check(hashlib.sha256(raw).hexdigest()==c['basis_sha256'],'native basis hash failed');bases=json.loads(raw)
    result=verify(c,source,bases)
    if a.self_test:result['rejected_mutations']=tests(c,source,bases);result['tests_passed']=1+len(result['rejected_mutations'])
    result.update(source_certificate_sha256=SOURCE,source_audit_sha256=AUDIT,certificate_sha256=hashlib.sha256(a.certificate.read_bytes()).hexdigest())
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
