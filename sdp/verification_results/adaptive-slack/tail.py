#!/usr/bin/env python3
"""Exact mandatory-prefix extension; no circular use of the final bound.
The tail ends at the independently proved regional endpoint, not at the target.
Construction uses coefficient conversion; acceptance reconstructs signed powers.
"""
import argparse,copy,hashlib,json,sys,importlib.util
from fractions import Fraction as F
from pathlib import Path
from math import comb
from flint import fmpq as Q,fmpq_mat as Mat
import verify as v
sys.path.insert(0,str(v.ROOT/'population-refinement'))
import certify_population_subdivision as b
sp=importlib.util.spec_from_file_location('old_cost_producer',v.ROOT/'cost-profile/produce.py');cp=importlib.util.module_from_spec(sp);sp.loader.exec_module(cp)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def producer(base,reg,report,reg_hash,report_hash):
 P0=F(base['previous_bound']);P1=F(reg['bound']);a=36*P0/v.U-35;z=36*P1/v.U-35;n=reg['grid'];entry=reg['intervals'][-1]
 v.need(entry['mode']=='regional' and entry['interval_index']==319,'last interval requires regional proof');common=None
 for region in entry['regions']:
  groups={}
  for rid,w in region['weights']:
   rec=base['projection_records'][rid];ex=tuple(rec['population_exponents']);p=groups.setdefault(ex,[Q(0)]*15)
   for k,c in enumerate(rec['polynomial']):p[k]+=Q(w)*Q(c)
  exs=sorted(groups);coeff=Mat([[cp.elevate(cp.bern(groups[e].copy(),a,z),14)[k] for e in exs] for k in range(15)])
  x,y=region['x'],region['y'];pops=[]
  for g,r,hh,s in exs:
   def uni(g,r,left):
    p=[Q(0)]*(g+r+1)
    for k in range(g+1):p[r+k]=Q((-1)**k*comb(g,k))
    return cp.elevate(cp.bern(p,F(left,n),F(left+1,n)),7)
   X=uni(g,r,x);Y=uni(hh,s,y);pops.append([u*w for u in X for w in Y])
  values=coeff*Mat(pops);C=[Q(x*7+i,14*n)+Q(y*7+j,28*n) for i in range(8) for j in range(8)];d=[]
  for k in range(15):
   for col,c in enumerate(C):
    if not c:v.need(values[k,col]>=0,'zero cost face')
   d.append(min(values[k,col]/c for col,c in enumerate(C) if c))
  common=d if common is None else [min(x,y) for x,y in zip(common,d)]
 gain=(P1-P0)*F(str(sum(common,Q(0))/15));v.need(gain>0,'positive tail contribution');p=b.power_from_bernstein(list(map(F,reg['endpoint_bernstein'])))
 def endpoint(B):
  rho=(B-v.L)/(P1-v.L);q=[c*rho**i for i,c in enumerate(p)];q[0]+=gain-(B-P1);return b.bernstein_from_power(q)
 scale=10**12;lo=int(P1*scale);hi=int(v.U*scale)
 while lo+1<hi:
  mid=(lo+hi)//2
  if min(endpoint(F(mid,scale)))>0:lo=mid
  else:hi=mid
 B=F(lo,scale)
 return {'schema':'minexposure/mandatory-tail-v1','regional_certificate_sha256':reg_hash,'regional_report_sha256':report_hash,'source_certificate_sha256':v.SOURCE,'base_certificate_sha256':v.BASE,'prefix_from':str(P0),'prefix_to':str(P1),'local_from':str(a),'local_to':str(z),'grid':n,'tail_bernstein':list(map(str,common)),'additional_occupation_slack':str(gain),'bound':str(B),'previous_bound':str(P1),'endpoint_bernstein':list(map(str,endpoint(B)))}
def verify(c,base,reg,report,reg_hash,report_hash):
 v.need(c['schema']=='minexposure/mandatory-tail-v1' and c['source_certificate_sha256']==v.SOURCE and c['base_certificate_sha256']==v.BASE,'schema/source')
 v.need(c['regional_certificate_sha256']==reg_hash and c['regional_report_sha256']==report_hash,'regional binding')
 v.need(report['status']=='PASS' and report['certificate_sha256']==reg_hash and F(report['certified_lower_bound'])==F(reg['bound']),'verified predecessor')
 P0=F(base['previous_bound']);P1=F(reg['bound']);a=36*P0/v.U-35;z=36*P1/v.U-35
 v.need(F(c['prefix_from'])==P0 and F(c['prefix_to'])==P1 and F(c['local_from'])==a and F(c['local_to'])==z and 0<a<z<1,'overlapping or unproved tail')
 v.need(F(base['integration_bins'][-1]['b'])==a,'prefix boundary');n=c['grid'];v.need(type(n)is int and n==reg['grid'],'grid');d=list(map(Q,c['tail_bernstein']));v.need(len(d)==15,'tail degree')
 allowed={i for item in base['integration_bins'] for i,w,s in item['allocations']};seen=set();T=v.affine(14,a,z);cache={};checks=0
 for region in reg['intervals'][-1]['regions']:
  x,y=region['x'],region['y'];v.need((x,y) not in seen and 0<=x<n and 0<=y<n,'region coverage');seen.add((x,y))
  groups,nb,ids=v.region_weights(region,base['projection_records'],allowed,4);P,C=v.popmap(7,x,y,n);mat=T*v.tensor(groups,cache)*P
  for k in range(15):
   for col,co in enumerate(C):v.need(mat[k,col]-d[k]*co>=0,'tail polynomial inequality');checks+=1
 v.need(len(seen)==n*n,'incomplete coverage');gain=(P1-P0)*F(str(sum(d,Q(0))/15));v.need(gain==F(c['additional_occupation_slack']) and gain>0,'tail integral')
 B=F(c['bound']);beta=list(map(F,c['endpoint_bernstein']));old=list(map(F,reg['endpoint_bernstein']));v.need(P1<B<v.U and len(beta)==14 and min(beta)>0 and F(c['previous_bound'])==P1,'endpoint signs');rho=(B-v.L)/(P1-v.L)
 for k in range(14):
  t=F(k,13);v.need(v.bvalue(beta,t)==v.bvalue(old,rho*t)+gain-(B-P1),'endpoint identity')
 return {'status':'PASS','certified_lower_bound':str(B),'bound_decimal':v.dec(B),'regional_bound':str(P1),'previous_round_bound':str(v.OLD),'increase_over_regional_bound':v.dec(B-P1),'increase_over_previous_round':v.dec(B-v.OLD),'remaining_gap_strictly_less_than':v.dec(v.UPPER-B),'additional_occupation_slack':str(gain),'additional_occupation_slack_decimal':v.dec(gain),'tail_coefficient_inequalities':checks,'endpoint_identities':14,'positive_endpoint_coefficients':14,'source_certificate_sha256':v.SOURCE,'regional_certificate_sha256':reg_hash,'arithmetic':'exact rational','scope':'all-duration ideal-blockade stationary-torus','dependency':'Regional certificate and complete original-dependent predecessor proof chain.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--regional-certificate',type=Path,required=True);ap.add_argument('--regional-report',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--check',type=Path);ap.add_argument('--self-test',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 base=v.load(v.ROOT/'population-refinement/certified/population-certificate.json.gz',v.BASE,True);reg=json.loads(a.regional_certificate.read_text());report=json.loads(a.regional_report.read_text());rh=h(a.regional_certificate);ah=h(a.regional_report)
 c=json.loads(a.check.read_text()) if a.check else producer(base,reg,report,rh,ah);result=verify(c,base,reg,report,rh,ah)
 if a.self_test:
  rejected=[]
  for name,fn in [('overlap with prior prefix',lambda z:z.update(prefix_from='2.9305')),('unproved future prefix',lambda z:z.update(prefix_to='2.935')),('false tail integral',lambda z:z.update(additional_occupation_slack='1')),('inflated tail profile',lambda z:z['tail_bernstein'].__setitem__(0,'1')),('changed target',lambda z:z.update(bound='2.935')),('wrong predecessor',lambda z:z.update(regional_certificate_sha256='0'*64))]:
   z=copy.deepcopy(c);fn(z)
   try:verify(z,base,reg,report,rh,ah)
   except ValueError:rejected.append(name)
   else:raise ValueError('accepted mutation '+name)
  result['rejected_mutations']=rejected;result['tests_passed']=len(rejected)+1
 if not a.check:(a.output/'certificate.json').write_text(json.dumps(c,indent=2)+'\n')
 result['certificate_sha256']=h(a.check or a.output/'certificate.json');(a.output/'independent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
