#!/usr/bin/env python3
"""Exact endpoint composition of separately verified disjoint slack bounds.

This is not a replacement for either verifier or the original global audit.
reproduce.sh replays every extension verifier before checking this endpoint.
"""
import argparse,copy,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
from decimal import Decimal,localcontext
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]
SOURCE='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
REFHASH='3932489adf01c5f6ca596663c1624c4ed71bae396d2922d2df2f2beeca882c14'
B0=F('2.931225938506');L=F('2.9305');U=F('2.935887');UPPER=F('2.935875225844105');KAPPA0=F('1107565238703/1000000000000000000')
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dec(x):
    with localcontext() as c:c.prec=60;return str(Decimal(x.numerator)/Decimal(x.denominator))
def value(b,t):
    return sum((x*comb(13,k)*t**k*(1-t)**(13-k) for k,x in enumerate(b)),F(0))
def load(args):
    refpath=ROOT/'population-refinement/certified/subdivision-certificate.json';need(sha(refpath)==REFHASH,'base endpoint hash');ref=json.loads(refpath.read_text())
    cross=json.loads(args.crossing.read_text());profile=json.loads(args.profile.read_text());cr=json.loads(args.crossing_report.read_text());pr=json.loads(args.profile_report.read_text())
    for report,cert,path in [(cr,cross,args.crossing),(pr,profile,args.profile)]:
        need(report['status']=='PASS' and report['certificate_sha256']==sha(path) and F(report['certified_lower_bound'])==F(cert['bound']),'unverified or mismatched dependency')
        need(cert['source_certificate_sha256']==report['source_certificate_sha256']==SOURCE,'source mismatch')
    need(cross['base_certificate_sha256']==profile['refinement_certificate_sha256']==REFHASH,'distinct base endpoints')
    K=F(profile['occupation_slack']);K0=F(ref['occupation_slack']);kap=F(cross['new_interface_slack'])
    need(K==F(pr['occupation_slack']) and kap==F(cr['new_interface_slack']),'changed slack constants')
    need(F(profile['base_occupation_slack'])==K0 and F(cross['old_interface_slack'])==KAPPA0 and F(ref['bound'])==B0,'old constants')
    need(K>K0 and kap>KAPPA0,'no gain')
    return ref,cross,profile,K-K0+kap-KAPPA0,{'source_certificate_sha256':SOURCE,'refinement_certificate_sha256':REFHASH,'crossing_certificate_sha256':sha(args.crossing),'profile_certificate_sha256':sha(args.profile),'crossing_report_sha256':sha(args.crossing_report),'profile_report_sha256':sha(args.profile_report)}
def validate(c,ref,delta,bindings):
    need(c['schema']=='minexposure/combined-disjoint-slack-v1','combined schema')
    need(c['bindings']==bindings,'dependency hashes')
    B=F(c['bound']);beta=list(map(F,c['endpoint_bernstein']));need(B0<B<U and len(beta)==14 and min(beta)>0,'target or signs')
    need(F(c['total_slack_increment'])==delta,'double-counted or altered slack')
    rho=(B-L)/(B0-L);old=list(map(F,ref['endpoint_bernstein']))
    for k in range(14):
        t=F(k,13);need(value(beta,t)==value(old,rho*t)+delta-(B-B0),'complete endpoint polynomial identity')
    return True

def main():
    ap=argparse.ArgumentParser()
    for name in ['crossing','profile','crossing-report','profile-report','output']:ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--check',type=Path);args=ap.parse_args();ref,cross,profile,delta,bindings=load(args)
    if args.check:c=json.loads(args.check.read_text())
    else:
        # Producer conversion uses binomial power expansion; acceptance below
        # evaluates Bernstein polynomials directly at 14 rational nodes.
        p=[F(0)]*14
        for k,b in enumerate(map(F,ref['endpoint_bernstein'])):
            for j in range(14-k):p[k+j]+=b*comb(13,k)*comb(13-k,j)*(-1)**j
        def coefficients(B):
            rho=(B-L)/(B0-L);q=[a*rho**i for i,a in enumerate(p)];q[0]+=delta-(B-B0)
            return [sum((q[j]*F(comb(i,j),comb(13,j)) for j in range(i+1)),F(0)) for i in range(14)]
        den=10**12;lo=int(max(F(cross['bound']),F(profile['bound']))*den);hi=int(U*den)
        need(all(x>0 for x in coefficients(F(lo,den))),'component endpoint not recovered')
        while lo+1<hi:
            mid=(lo+hi)//2
            if min(coefficients(F(mid,den)))>0:lo=mid
            else:hi=mid
        B=F(lo,den);c={'schema':'minexposure/combined-disjoint-slack-v1','bound':str(B),'bound_decimal':dec(B),'previous_bound':str(B0),'total_slack_increment':str(delta),'occupation_slack':profile['occupation_slack'],'interface_slack':cross['new_interface_slack'],'endpoint_bernstein':list(map(str,coefficients(B))),'bindings':bindings}
    validate(c,ref,delta,bindings);tests=['valid certificate']
    for name,change in [('changed target',lambda z:z.update(bound=str(F(z['bound'])+F(1,10000)))),('doubled increment',lambda z:z.update(total_slack_increment=str(2*delta))),('changed endpoint',lambda z:z['endpoint_bernstein'].__setitem__(7,str(F(z['endpoint_bernstein'][7])+1))),('changed dependency',lambda z:z['bindings'].update(source_certificate_sha256='0'*64))]:
        z=copy.deepcopy(c);change(z)
        try:validate(z,ref,delta,bindings)
        except ValueError:tests.append('rejected '+name)
        else:raise ValueError('accepted mutation '+name)
    B=F(c['bound']);report={'status':'PASS','certified_lower_bound':str(B),'new_lower_bound_decimal':dec(B),'previous_lower_bound':str(B0),'exact_increase':str(B-B0),'exact_increase_decimal':dec(B-B0),'inherited_strict_upper_bound':dec(UPPER),'remaining_gap_strictly_less_than':dec(UPPER-B),'percentage_of_previous_gap_closed':dec(100*(B-B0)/(UPPER-B0)),'crossing_only_bound':cross['bound'],'profile_only_bound':profile['bound'],'endpoint_identities':14,'strictly_positive_endpoint_coefficients':14,'tests':tests,'tests_passed':len(tests),'arithmetic':'exact rational','scope':'all-duration ideal-blockade stationary-torus','bindings':bindings,'dependency':'Both extension verifiers and the inherited base proof must pass; see reproduce.sh','old_penalties_added_again':False,'time_cap_used':False}
    args.output.mkdir(parents=True,exist_ok=True)
    if not args.check:(args.output/'certificate.json').write_text(json.dumps(c,indent=2)+'\n')
    certificate=args.check or args.output/'certificate.json';report['certificate_sha256']=sha(certificate)
    (args.output/'independent.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
