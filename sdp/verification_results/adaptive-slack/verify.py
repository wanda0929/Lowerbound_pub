#!/usr/bin/env python3
"""Independent exact regional-allocation checker; no producer or optimizer imports.
Full original and predecessor proofs remain explicit dependencies. Every used
projection ID was checked by the pinned degree-seven predecessor verifier.
"""
import argparse,copy,gzip,hashlib,json,sys
from pathlib import Path
from fractions import Fraction as F
from math import comb
from decimal import Decimal,localcontext
from flint import fmpq as Q,fmpq_mat as Mat
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]
BASE='3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb'
JOINT='7d6e5c4c085331d7bf64a49fa2039910aaf4f34ac2e2c04c1e1c25bd87fdcc84'
PROFILE='8952644ae8aff9d692ea7cb25a462de507f29f85af02b1578e063d0eba86a7f7'
SOURCE='1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52'
L=F('2.9305');U=F('2.935887');OLD=F('2.931272845583');UPPER=F('2.935875225844105')
KNOTS=list(map(F,['0','1/36','1/3','2/3','35/36','1']))
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def load(p,h,zipped=False):
 raw=p.read_bytes();raw=gzip.decompress(raw) if zipped else raw
 need(sha(raw)==h,'dependency bytes: '+str(p));return json.loads(raw)
def dec(x):
 with localcontext() as ctx:ctx.prec=60;return str(Decimal(x.numerator)/Decimal(x.denominator))
def affine(D,a,b):
 a=Q(str(a));h=Q(str(b))-a
 return Mat([[sum((Q(comb(k,l)*comb(i,l),comb(D,l))*a**(k-l)*h**l for l in range(min(i,k)+1)),Q(0)) for k in range(D+1)] for i in range(D+1)])
def bvalue(beta,t):
 d=len(beta)-1
 return sum((x*comb(d,k)*t**k*(1-t)**(d-k) for k,x in enumerate(beta)),F(0))
def popmap(D,x,y,n):
 T=affine(D,F(x,n),F(x+1,n));S=affine(D,F(y,n),F(y+1,n))
 A=Mat([[T[i,a]*S[j,b] for i in range(D+1) for j in range(D+1)] for a in range(D+1) for b in range(D+1)])
 cost=[Q(x*D+i,2*n*D)+Q(y*D+j,4*n*D) for i in range(D+1) for j in range(D+1)]
 return A,cost

def region_weights(region,recs,allowed,cell):
 seen=set();budgets={};groups={}
 for row in region['weights']:
  need(type(row)is list and len(row)==2,'invalid allocation record');rid,ws=row
  need(type(rid)is int and rid in allowed and rid not in seen,'unverified or duplicate projection');seen.add(rid)
  rec=recs[rid];need(rec['cell']==cell,'wrong projection cell');w=Q(ws);need(w>0,'nonpositive allocation')
  block=rec['block'];budgets[block]=budgets.get(block,Q(0))+w;need(budgets[block]<=1,'double-counted matrix budget')
  ex=tuple(rec['population_exponents']);p=groups.setdefault(ex,[Q(0)]*15)
  for k,a in enumerate(rec['polynomial']):need(k<=14,'excess polynomial degree');p[k]+=w*Q(a)
 return groups,len(budgets),seen

def tensor(groups,cache):
 power=[[Q(0)]*64 for k in range(15)]
 for ex,p in groups.items():
  if ex not in cache:
   g,r,h,s=ex;need(g+r<=7 and h+s<=7,'invalid population degree')
   cache[ex]=[((r+i)*8+s+j,Q((-1)**(i+j)*comb(g,i)*comb(h,j))) for i in range(g+1) for j in range(h+1)]
  for k,a in enumerate(p):
   if a:
    for pos,c in cache[ex]:power[k][pos]+=a*c
 return Mat(power)

def endpoint(c,joint,K):
 B=F(c['bound']);need(OLD<B<U,'bound interval')
 need(F(c['previous_bound'])==OLD and F(c['old_occupation_slack'])==F(joint['occupation_slack']),'old endpoint or slack')
 beta=list(map(F,c['endpoint_bernstein']));prev=list(map(F,joint['endpoint_bernstein']))
 need(len(beta)==len(prev)==14 and min(beta)>0,'endpoint signs');rho=(B-L)/(OLD-L)
 for k in range(14):
  t=F(k,13)
  need(bvalue(beta,t)==bvalue(prev,rho*t)+K-F(joint['occupation_slack'])-(B-OLD),'endpoint polynomial identity')

def verify(c,base,joint,profile,verbose=True):
 need(c['schema']=='minexposure/regional-allocation-v1','schema')
 need(c['base_certificate_sha256']==BASE and c['previous_certificate_sha256']==JOINT and c['profile_certificate_sha256']==PROFILE and c['source_certificate_sha256']==SOURCE,'dependency binding')
 need(c['population_degree']==7 and c['cost_degree']==14,'degree');n=c['grid'];need(type(n)is int and n in (1,2,4,8),'grid')
 need(F(joint['bound'])==OLD and F(joint['occupation_slack'])==F(profile['occupation_slack']),'inconsistent predecessor')
 need(len(c['intervals'])==len(base['integration_bins'])==len(profile['profiles'])==320,'interval coverage')
 recs=base['projection_records'];allowed={i for b in base['integration_bins'] for i,w,s in b['allocations']}
 maps={(x,y):popmap(7,x,y,n) for x in range(n) for y in range(n)};cache={};K=Q(0);count=0;budgetcount=0;regional=0;ids=set()
 for index,(entry,item) in enumerate(zip(c['intervals'],base['integration_bins'])):
  need(entry['interval_index']==index,'interval order');delta=list(map(Q,entry['bernstein']));need(len(delta)==15,'profile degree')
  if entry['mode']=='inherited':
   need(entry['regions']==[] and delta==list(map(Q,profile['profiles'][index]['bernstein'])),'false inherited profile')
  else:
   need(entry['mode']=='regional' and len(entry['regions'])==n*n,'region count');seen=set();regional+=1;T=affine(14,F(item['a']),F(item['b']))
   for region in entry['regions']:
    x,y=region['x'],region['y'];need(type(x)is int and type(y)is int and 0<=x<n and 0<=y<n and (x,y) not in seen,'population coverage');seen.add((x,y))
    groups,nb,used=region_weights(region,recs,allowed,item['cell']);budgetcount+=nb;ids.update(used)
    P,C=maps[x,y];values=T*tensor(groups,cache)*P
    for k in range(15):
     for col,co in enumerate(C):need(values[k,col]-delta[k]*co>=0,'negative regional tensor coefficient');count+=1
   need(len(seen)==n*n,'missing population region')
  j=item['cell'];mass=Q(str(U*(KNOTS[j+1]-KNOTS[j])*(F(item['b'])-F(item['a']))));K+=mass*sum(delta,Q(0))/15
  if verbose and index%32==0:print('VERIFIED_REGIONAL_INTERVAL',index,flush=True)
 K=F(str(K));need(K==F(c['occupation_slack']) and K>F(profile['occupation_slack']),'integrated slack');endpoint(c,joint,K);B=F(c['bound'])
 return {'status':'PASS','certified_lower_bound':str(B),'bound_decimal':dec(B),'previous_lower_bound':str(OLD),'exact_increase':str(B-OLD),'increase_decimal':dec(B-OLD),'remaining_gap_strictly_less_than':dec(UPPER-B),'occupation_slack':str(K),'occupation_slack_increase':str(K-F(profile['occupation_slack'])),'cost_intervals':320,'regional_intervals':regional,'regions_per_interval':n*n,'tensor_coefficient_inequalities':count,'exact_gram_budget_checks':budgetcount,'previously_verified_projections_used':len(ids),'endpoint_interpolation_identities':14,'positive_endpoint_coefficients':14,'arithmetic':'exact rational; no floating tolerance or optimizer','source_certificate_sha256':SOURCE,'base_certificate_sha256':BASE,'previous_certificate_sha256':JOINT,'profile_certificate_sha256':PROFILE,'scope':'all-duration ideal-blockade stationary-torus','dependency':'Full predecessor extension chain and original exact source audit are required; hashes alone are not mathematical verification.'}

def tests(c,base,joint):
 passed=[]
 for d in [1,7,14]:
  T=affine(d,F(1,7),F(3,7))
  for power in range(d+1):
   beta=[F(str(T[i,power])) for i in range(d+1)]
   for t in (F(0),F(3,5),F(1)):need(bvalue(beta,t)==(F(1,7)+F(2,7)*t)**power,'affine test')
  passed.append('exact affine identity degree '+str(d))
 for label,change in [('changed target',lambda z:z.update(bound=str(F(z['bound'])+F(1,100000)))),('changed endpoint coefficient',lambda z:z['endpoint_bernstein'].__setitem__(0,'-1')),('doubled occupation gain',lambda z:z.update(occupation_slack=str(2*F(z['occupation_slack'])-F(z['old_occupation_slack']))))]:
  z=copy.deepcopy(c);change(z)
  try:endpoint(z,joint,F(z['occupation_slack']))
  except ValueError:passed.append('rejected '+label)
  else:raise ValueError('mutation accepted '+label)
 return passed

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
 base=load(ROOT/'population-refinement/certified/population-certificate.json.gz',BASE,True);joint=load(ROOT/'joint-slack/certified/certificate.json',JOINT);profile=load(ROOT/'joint-slack/certified/profile-certificate.json',PROFILE);c=json.loads(args.certificate.read_text())
 out=verify(c,base,joint,profile)
 if args.self_test:out['tests']=tests(c,base,joint);out['tests_passed']=1+len(out['tests'])
 out['certificate_sha256']=sha(args.certificate.read_bytes());args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if not k.startswith('occupation_slack')},indent=2),flush=True)
if __name__=='__main__':main()
