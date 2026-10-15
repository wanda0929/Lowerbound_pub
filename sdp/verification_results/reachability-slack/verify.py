#!/usr/bin/env python3
"""Independent verifier of reachability-restricted slack integration.

Does not import the new producer. Signed power tensors and direct affine maps
are reconstructed from previously verified projection polynomials. The original
global certificate and all predecessors are explicit mathematical dependencies.
"""
from __future__ import annotations
import argparse,copy,gzip,hashlib,importlib.util,json,sys
from pathlib import Path
from fractions import Fraction as F
from flint import fmpq as Q
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('inherited_regional_checker',ROOT/'adaptive-slack/verify.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
REG='ca4813512b0b3b911ed37815012c29b1688173e3e5f8ebeb6a31361674a9b772'
TAIL='356384c59c270f7cf893c2b6c8a075951abfea66ef29b8ee2a6593881acd9129'
B0=F('2.931286076089')
def sha(raw):return hashlib.sha256(raw).hexdigest()
def load(p,h,z=False):
 raw=p.read_bytes();raw=gzip.decompress(raw) if z else raw
 v.need(sha(raw)==h,'dependency bytes '+str(p));return json.loads(raw)
def inputs():
 return (load(ROOT/'population-refinement/certified/population-certificate.json.gz',v.BASE,True),load(ROOT/'adaptive-slack/certified/certificate.json.gz',REG,True),load(ROOT/'adaptive-slack/certified/tail-certificate.json',TAIL))

def barrier_coefficients():
 # Reconstruct central-binomial coefficients through the differential recurrence,
 # independently of the producer's closed combinatorial formula.
 c=[F(1)]
 for k in range(8):c.append(c[-1]*F(2*k+1,2*k+2))
 h=[3*x/F(2*k+3) for k,x in enumerate(c)]
 v.need(all(x>0 for x in h),'barrier monotonicity')
 # G=p^(3/2)*h/3, so G'=sqrt(p)*S/2.
 v.need(all(h[k]*F(2*k+3,3)==c[k] for k in range(9)),'barrier derivative identity')
 sq=[F(0)]*17
 for i,a in enumerate(c):
  for j,b in enumerate(c):sq[i+j]+=a*b
 residual=[F(0)]*18;residual[0]=1
 for i,a in enumerate(sq):residual[i]-=a;residual[i+1]+=a
 v.need(all(x>=0 for x in residual),'barrier derivative bound')
 return h,residual

def square_term(p,h):
 value=F(0)
 for c in reversed(h):value=value*p+c
 return p*p*p*value*value

def excluded(x,y,n,R,h):
 # The entire box is excluded only by monotonicity from its lower corner.
 # sqrt(A)+sqrt(D)>sqrt(T); no rounded radicals or population samples.
 A=8*square_term(F(x,n),h);D=square_term(F(y,n),h);T=72*R*R
 if A+D>T:return True
 return 4*A*D>(T-A-D)*(T-A-D)

def endpoint(c,tail,gain):
 B=F(c['bound']);cap=F(c['counterexample_cap'])
 v.need(B0<B<=cap<v.U and F(c['previous_bound'])==B0,'invalid target/sublevel')
 beta=list(map(F,c['endpoint_bernstein']));prev=list(map(F,tail['endpoint_bernstein']))
 v.need(len(beta)==len(prev)==14 and min(beta)>0 and F(tail['bound'])==B0,'endpoint signs or predecessor')
 rho=(B-v.L)/(B0-v.L)
 for k in range(14):
  t=F(k,13);v.need(v.bvalue(beta,t)==v.bvalue(prev,rho*t)+gain-(B-B0),'endpoint polynomial identity')

def check(c,base,reg,tail,verbose=True):
 v.need(c['schema']=='minexposure/reachability-slack-v1','schema')
 v.need(c['source_certificate_sha256']==v.SOURCE and c['base_certificate_sha256']==v.BASE and c['regional_certificate_sha256']==REG and c['previous_certificate_sha256']==TAIL,'source/predecessor binding')
 cap=F(c['counterexample_cap']);n=c['grid'];ng=reg['grid']
 v.need(B0<cap<v.U and type(n)is int and n in (4,8,16,32) and n%ng==0,'invalid partition or sublevel')
 v.need(c['barrier_series_order']==8,'wrong barrier')
 h,residual=barrier_coefficients();recs=base['projection_records'];allowed={i for item in base['integration_bins'] for i,w,s in item['allocations']}
 v.need(len(c['intervals'])==len(base['integration_bins'])==len(reg['intervals'])==320,'cost interval coverage')
 gain=F(0);K=F(0);oldK=F(0);checks=0;drops=0;kept=0;changed=0;budgets=0;ids=set();cache={};maps={}
 for index,(entry,prior,item) in enumerate(zip(c['intervals'],reg['intervals'],base['integration_bins'])):
  v.need(entry['interval_index']==index and prior['interval_index']==index,'cost interval assignment')
  delta=list(map(Q,entry['bernstein']));previous=list(map(Q,prior['bernstein']));v.need(len(delta)==len(previous)==15,'cost degree')
  j=item['cell'];a,b=map(F,[item['a'],item['b']]);w=v.KNOTS[j+1]-v.KNOTS[j]
  A=v.U*(v.KNOTS[j]+w*a);D=v.U*(v.KNOTS[j]+w*b)
  v.need(0<=A<D<B0<cap,'unproved mandatory interval')
  oldmean=F(str(sum(previous,Q(0))/15));mean=F(str(sum(delta,Q(0))/15));oldK+=(D-A)*oldmean;K+=(D-A)*mean
  if entry['mode']=='inherited':v.need(delta==previous,'altered inherited profile')
  else:
   v.need(entry['mode']=='reachable' and prior['mode']=='regional' and mean>oldmean,'invalid strengthened profile')
   regions={(r['x'],r['y']):r for r in prior['regions']}
   v.need(len(regions)==len(prior['regions'])==ng*ng and set(regions)=={(x,y) for x in range(ng) for y in range(ng)},'predecessor population coverage')
   R=min(D,cap-A);T=v.affine(14,a,b);power={};drop=0;alive=0
   for x in range(n):
    for y in range(n):
     if excluded(x,y,n,R,h):drop+=1;continue
     alive+=1;key=(x*ng//n,y*ng//n)
     if key not in power:
      groups,nb,used=v.region_weights(regions[key],recs,allowed,j);budgets+=nb;ids.update(used);power[key]=T*v.tensor(groups,cache)
     if (x,y) not in maps:maps[x,y]=v.popmap(7,x,y,n)
     P,C=maps[x,y];M=power[key]*P
     for k in range(15):
      for col,cost in enumerate(C):v.need(M[k,col]-delta[k]*cost>=0,'reachable tensor inequality');checks+=1
   v.need(alive>0 and alive+drop==n*n,'incomplete box partition')
   v.need(drop==entry['discarded_boxes'] and alive==entry['retained_boxes'],'false exclusion counts')
   drops+=drop;kept+=alive;changed+=1;gain+=(D-A)*(mean-oldmean)
  if verbose and index%32==0:print('VERIFIED_REACHABILITY_INTERVAL',index,'changed',changed,flush=True)
 v.need(oldK==F(reg['occupation_slack'])==F(c['old_prefix_slack']),'old prefix integral')
 v.need(K==F(c['new_prefix_slack']) and gain==K-oldK==F(c['additional_slack']) and gain>0,'new prefix integral')
 v.need(changed==c['changed_intervals'] and drops==c['discarded_boxes'],'false aggregate counts')
 endpoint(c,tail,gain);B=F(c['bound'])
 return {'status':'PASS','certified_lower_bound':str(B),'bound_decimal':v.dec(B),'previous_lower_bound':str(B0),'increase_decimal':v.dec(B-B0),'exact_increase':str(B-B0),'remaining_gap_strictly_less_than':v.dec(v.UPPER-B),'counterexample_cap':str(cap),'changed_intervals':changed,'cost_intervals':320,'excluded_population_boxes':drops,'retained_population_boxes':kept,'exact_tensor_inequalities':checks,'exact_gram_budget_checks':budgets,'inherited_projection_ids':len(ids),'additional_slack':str(gain),'additional_slack_decimal':v.dec(gain),'barrier_residual_coefficients':list(map(str,residual)),'barrier_residual_coefficients_nonnegative':True,'endpoint_interpolation_identities':14,'strictly_positive_endpoint_coefficients':14,'source_certificate_sha256':v.SOURCE,'base_certificate_sha256':v.BASE,'regional_certificate_sha256':REG,'previous_certificate_sha256':TAIL,'arithmetic':'exact rational','floating_point_used_for_acceptance':False,'optimizer_used_for_acceptance':False,'scope':'all-duration ideal-blockade stationary-torus','dependency':'All pinned predecessor certificates and the original exact global audit; hashes bind inputs, not mathematical correctness.'}

def self_tests(c,base,reg,tail):
 passed=[];h,_=barrier_coefficients()
 for R in (F(0),F(1,1000),F(1)):
  v.need(not excluded(0,0,8,R,h),'origin must remain');passed.append('zero-cost origin remains '+str(R))
 v.need(excluded(8,0,8,F(0),h) and not excluded(8,8,8,F(2),h),'barrier corner tests');passed.append('exact strict corner exclusion')
 for name,fn in [('false target',lambda z:z.update(bound='2.935')),('doubled occupation increment',lambda z:z.update(additional_slack=str(2*F(z['additional_slack'])))),('negative endpoint coefficient',lambda z:z['endpoint_bernstein'].__setitem__(0,'-1')),('cap below target',lambda z:z.update(counterexample_cap=str(B0)))]:
  z=copy.deepcopy(c);fn(z)
  try:endpoint(z,tail,F(z['additional_slack']))
  except ValueError:passed.append('rejected '+name)
  else:raise ValueError('accepted mutation '+name)
 # Mutations of a real strengthened interval are rejected by full acceptance.
 first=next(i for i,e in enumerate(c['intervals']) if e['mode']=='reachable')
 cases=[('invented excluded rectangle',lambda z:z['intervals'][first].__setitem__('discarded_boxes',z['intervals'][first]['discarded_boxes']+1)),('inflated reachable polynomial',lambda z:z['intervals'][first]['bernstein'].__setitem__(0,'1000000')),('missing cost interval',lambda z:z['intervals'].pop()),('wrong barrier order',lambda z:z.update(barrier_series_order=7))]
 for name,fn in cases:
  z=copy.deepcopy(c);fn(z)
  try:check(z,base,reg,tail,False)
  except ValueError:passed.append('rejected '+name)
  else:raise ValueError('accepted mutation '+name)
 return passed

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
 base,reg,tail=inputs();c=json.loads(args.certificate.read_text());out=check(c,base,reg,tail)
 if args.self_test:out['tests']=self_tests(c,base,reg,tail);out['tests_passed']=1+len(out['tests'])
 out['certificate_sha256']=sha(args.certificate.read_bytes());args.output.write_text(json.dumps(out,indent=2)+'\n');print('PASS',json.dumps({k:x for k,x in out.items() if k not in ['additional_slack','barrier_residual_coefficients']},indent=2),flush=True)
if __name__=='__main__':main()
