#!/usr/bin/env python3
"""Reachability refinement of pinned crossing matrices; exact acceptance.
Producer: factorwise Bernstein conversion. Checker: signed power expansion.
The new occupation proof and the full original-dependent chain are dependencies.
"""
import argparse,copy,hashlib,importlib.util,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
from flint import fmpq as Q,fmpq_mat as Mat
import verify as rv
v=rv.v;ROOT=rv.ROOT
CROSS='98560cc0bd55714dfb74814e377caac64cb4c736652e33868925da7b25703fd7'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def provenance(oc,report,och,rh):
 v.need(report['status']=='PASS' and report['certificate_sha256']==och and F(report['certified_lower_bound'])==F(oc['bound']),'occupation prerequisite report')
 v.need(oc['schema']=='minexposure/reachability-slack-v1' and oc['source_certificate_sha256']==v.SOURCE and oc['previous_certificate_sha256']==rv.TAIL,'occupation prerequisite source')
 return {'occupation_certificate_sha256':och,'occupation_report_sha256':rh,'crossing_certificate_sha256':CROSS,'source_certificate_sha256':v.SOURCE}
def grouped(cross,j):
 groups={};seen=set();rs=cross['records'];item=cross['crossings'][j]
 v.need(item['knot']==j,'crossing order')
 for rid,w in item['allocations']:
  v.need(rid not in seen,'duplicate inherited record');seen.add(rid);rec=rs[rid];v.need(rec['knot']==j,'record crossing')
  ex=tuple(rec['population_exponents']);rate=Q(w)*Q(rec['gamma']);v.need(rate>0,'positive inherited diagonal')
  groups[ex]=groups.get(ex,Q(0))+rate
 return groups

def make(cross,oc,report,och,rh,n):
 bindings=provenance(oc,report,och,rh);cap=F(oc['counterexample_cap']);h,_=rv.barrier_coefficients();items=[];gain=F(0)
 spec=importlib.util.spec_from_file_location('crossing_factorwise_conversion',ROOT/'cost-profile/produce.py');cp=importlib.util.module_from_spec(spec);spec.loader.exec_module(cp)
 for j in range(4):
  C=v.U*v.KNOTS[j+1];R=min(C,cap-C);groups=grouped(cross,j);minimum=None;drop=0;alive=0
  for x in range(n):
   for y in range(n):
    if rv.excluded(x,y,n,R,h):drop+=1;continue
    alive+=1;out=[Q(0)]*64
    for (g,r,hh,s),weight in groups.items():
     def uni(g,r,i):
      p=[Q(0)]*(g+r+1)
      for k in range(g+1):p[r+k]=Q((-1)**k*comb(g,k))
      return cp.elevate(cp.bern(p,F(i,n),F(i+1,n)),7)
     a=uni(g,r,x);b=uni(hh,s,y)
     for i,u in enumerate(a):
      for k,z in enumerate(b):out[8*i+k]+=weight*u*z
    m=min(out);minimum=m if minimum is None else min(minimum,m)
  old=F(cross['crossings'][j]['bound']);new=max(old,F(str(minimum)));gain+=new-old
  items.append({'knot':j,'bound':str(new),'old_bound':str(old),'mode':'reachable' if new>old else 'inherited','discarded_boxes':drop,'retained_boxes':alive})
  print('REACHABLE_CROSSING',j,'old',float(old),'new',float(new),'excluded',drop,flush=True)
 oldB=F(oc['bound']);v.need(gain>=0,'crossing loss')
 sys.path.insert(0,str(ROOT/'population-refinement'));import certify_population_subdivision as pc
 power=pc.power_from_bernstein(list(map(F,oc['endpoint_bernstein'])))
 def endpoint(B):
  rho=(B-v.L)/(oldB-v.L);p=[a*rho**i for i,a in enumerate(power)];p[0]+=gain-(B-oldB);return pc.bernstein_from_power(p)
 scale=10**12;lo=int(oldB*scale);hi=int(cap*scale)+1
 while lo+1<hi:
  mid=(lo+hi)//2
  if min(endpoint(F(mid,scale)))>0:lo=mid
  else:hi=mid
 B=F(lo,scale)
 return {'schema':'minexposure/reachable-crossings-v1',**bindings,'counterexample_cap':str(cap),'grid':n,'crossings':items,'additional_crossing_slack':str(gain),'previous_bound':str(oldB),'bound':str(B),'bound_decimal':v.dec(B),'endpoint_bernstein':list(map(str,endpoint(B))),'status':'producer; separate checker required'}

def verify(c,cross,oc,report,och,rh):
 bindings=provenance(oc,report,och,rh)
 v.need(c['schema']=='minexposure/reachable-crossings-v1' and all(c[k]==val for k,val in bindings.items()),'binding/schema')
 cap=F(oc['counterexample_cap']);v.need(F(c['counterexample_cap'])==cap,'counterexample cap');n=c['grid'];v.need(type(n)is int and n in (4,8,16,32),'grid')
 h,_=rv.barrier_coefficients();v.need(len(c['crossings'])==len(cross['crossings'])==4,'crossing coverage')
 maps={};gain=F(0);checks=0;drops=0;changed=0
 for j,(entry,previous) in enumerate(zip(c['crossings'],cross['crossings'])):
  v.need(entry['knot']==previous['knot']==j,'crossing assignment');old=F(previous['bound']);new=F(entry['bound']);v.need(F(entry['old_bound'])==old and new>=old,'old crossing penalty')
  if entry['mode']=='inherited':v.need(new==old,'false inherited crossing')
  else:
   v.need(entry['mode']=='reachable' and new>old,'crossing mode');groups=grouped(cross,j);power=[Q(0)]*64
   for (g,r,hh,s),rate in groups.items():
    for i in range(g+1):
     for k in range(hh+1):power[(r+i)*8+s+k]+=rate*((-1)**(i+k)*comb(g,i)*comb(hh,k))
   C=v.U*v.KNOTS[j+1];v.need(C<rv.B0<cap,'mandatory crossing');R=min(C,cap-C);row=Mat([power]);drop=0;alive=0
   for x in range(n):
    for y in range(n):
     if rv.excluded(x,y,n,R,h):drop+=1;continue
     alive+=1
     if (x,y) not in maps:maps[x,y]=v.popmap(7,x,y,n)[0]
     out=row*maps[x,y]
     for k in range(64):v.need(out[0,k]>=Q(str(new)),'reachable crossing polynomial');checks+=1
   v.need(drop+alive==n*n and alive>0 and drop==entry['discarded_boxes'] and alive==entry['retained_boxes'],'crossing population cover');drops+=drop;changed+=1
  gain+=new-old
 v.need(gain==F(c['additional_crossing_slack']),'total crossing increment')
 oldB=F(oc['bound']);B=F(c['bound']);v.need(F(c['previous_bound'])==oldB and rv.B0<oldB<=B<=cap,'endpoint/sublevel')
 beta=list(map(F,c['endpoint_bernstein']));prev=list(map(F,oc['endpoint_bernstein']));v.need(len(beta)==len(prev)==14 and min(beta)>0,'endpoint positivity');rho=(B-v.L)/(oldB-v.L)
 for i in range(14):
  t=F(i,13);v.need(v.bvalue(beta,t)==v.bvalue(prev,rho*t)+gain-(B-oldB),'combined endpoint identity')
 return {'status':'PASS','certified_lower_bound':str(B),'bound_decimal':v.dec(B),'previous_repository_bound':str(rv.B0),'increase_over_previous_repository_bound':v.dec(B-rv.B0),'occupation_only_bound':str(oldB),'increase_over_occupation_only_bound':v.dec(B-oldB),'remaining_gap_strictly_less_than':v.dec(v.UPPER-B),'counterexample_cap':str(cap),'changed_crossings':changed,'excluded_crossing_boxes':drops,'exact_crossing_coefficients_checked':checks,'additional_crossing_slack':str(gain),'additional_crossing_slack_decimal':v.dec(gain),'endpoint_interpolation_identities':14,'strictly_positive_endpoint_coefficients':14,'bindings':bindings,'arithmetic':'exact rational; no optimizer or tolerance','scope':'all-duration ideal-blockade stationary-torus','dependency':'New occupation verifier plus all pinned predecessor extensions and original global source audit.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--occupation',type=Path,required=True);ap.add_argument('--occupation-report',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--check',type=Path);ap.add_argument('--grid',type=int,default=16);ap.add_argument('--self-test',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 cross=rv.load(ROOT/'joint-slack/certified/crossing-certificate.json',CROSS);oc=json.loads(a.occupation.read_text());report=json.loads(a.occupation_report.read_text());och=digest(a.occupation);rh=digest(a.occupation_report)
 c=json.loads(a.check.read_text()) if a.check else make(cross,oc,report,och,rh,a.grid)
 out=verify(c,cross,oc,report,och,rh)
 if a.self_test:
  passed=[]
  cases=[('false crossing increment',lambda z:z.update(additional_crossing_slack='1')),('changed target',lambda z:z.update(bound='2.935')),('wrong sublevel',lambda z:z.update(counterexample_cap='2.935')),('missing crossing',lambda z:z['crossings'].pop()),('changed occupation predecessor',lambda z:z.update(occupation_certificate_sha256='0'*64))]
  for name,fn in cases:
   z=copy.deepcopy(c);fn(z)
   try:verify(z,cross,oc,report,och,rh)
   except ValueError:passed.append('rejected '+name)
   else:raise ValueError('mutation accepted '+name)
  out['tests']=passed;out['tests_passed']=1+len(passed)
 if not a.check:(a.output/'certificate.json').write_text(json.dumps(c,indent=2)+'\n')
 out['certificate_sha256']=digest(a.check or a.output/'certificate.json');(a.output/'independent.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',json.dumps(out,indent=2),flush=True)
if __name__=='__main__':main()
