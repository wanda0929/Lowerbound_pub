#!/usr/bin/env python3
"""Discover regional Gram allocations; optimizer values are never certificates.
The independent verifier reconstructs signed polynomials and checks all budgets.
"""
import argparse,gzip,hashlib,json,sys,time,importlib.util
from pathlib import Path
from fractions import Fraction as F
from math import comb
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
from flint import fmpq as Q,fmpq_mat as Mat
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'population-refinement'))
import certify_population_subdivision as old
sp=importlib.util.spec_from_file_location('old_cost_producer',ROOT/'cost-profile/produce.py');cp=importlib.util.module_from_spec(sp);sp.loader.exec_module(cp)
BASE='3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb'
JOINT='7d6e5c4c085331d7bf64a49fa2039910aaf4f34ac2e2c04c1e1c25bd87fdcc84'
PROFILE='8952644ae8aff9d692ea7cb25a462de507f29f85af02b1578e063d0eba86a7f7'
D=7;M=14;DEN=10**12

def sha(raw):return hashlib.sha256(raw).hexdigest()
def fl(q):return float(F(str(q)))
def load(p,h,compressed=False):
 raw=p.read_bytes();raw=gzip.decompress(raw) if compressed else raw
 if sha(raw)!=h:raise ValueError('dependency hash mismatch '+str(p))
 return json.loads(raw)
def pop(ex,x,y,n):
 g,r,h,s=ex
 def uni(g,r,k):
  p=[Q(0)]*(g+r+1)
  for i in range(g+1):p[r+i]=Q((-1)**i*comb(g,i))
  return cp.elevate(cp.bern(p,F(k,n),F(k+1,n)),D)
 return [u*v for u in uni(g,r,x) for v in uni(h,s,y)]
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--grid',type=int,default=4);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 n=args.grid
 if n not in (1,2,4,8):raise ValueError('grid')
 base=load(ROOT/'population-refinement/certified/population-certificate.json.gz',BASE,True)
 joint=load(ROOT/'joint-slack/certified/certificate.json',JOINT)
 profile=load(ROOT/'joint-slack/certified/profile-certificate.json',PROFILE)
 recs=base['projection_records'];used=sorted({i for b in base['integration_bins'] for i,w,s in b['allocations']})
 boxes=[(x,y) for x in range(n) for y in range(n)];data=[];K=Q(0);start=time.monotonic();region_count=0
 for cell in range(5):
  beta_cache={};ids=[i for i in used if recs[i]['cell']==cell];nb=len(ids);blocks=sorted({recs[i]['block'] for i in ids});bm={b:k for k,b in enumerate(blocks)}
  exs=sorted({tuple(recs[i]['population_exponents']) for i in ids});em={e:k for k,e in enumerate(exs)}
  budget=csr_matrix((np.ones(nb),([bm[recs[i]['block']] for i in ids],np.arange(nb))),shape=(len(blocks),nb))
  pm={};pf={};C={}
  for x,y in boxes:
   p=[pop(e,x,y,n) for e in exs];pm[x,y]=Mat(p);pf[x,y]=np.array([[fl(v) for v in p[em[tuple(recs[i]['population_exponents'])]]] for i in ids]).T
   C[x,y]=[Q(x*D+i,2*n*D)+Q(y*D+j,4*n*D) for i in range(D+1) for j in range(D+1)]
  stop=F(1) if cell<4 else F(base['integration_bins'][-1]['b'])
  for rid in ids:
   b=cp.elevate(cp.bern(list(map(Q,recs[rid]['polynomial'])),F(0),stop),M)
   beta_cache[rid]=old.partition(b,6)
  for index in range(cell*64,(cell+1)*64):
   item=base['integration_bins'][index];local=index%64;betas=[beta_cache[rid][local] for rid in ids]
   means=np.array([fl(sum(b,Q(0))/(M+1)) for b in betas]);scale=max(means.max(),1e-30);common=None;allocs=[]
   for x,y in boxes:
    cf=np.array([fl(v) for v in C[x,y]])
    A=vstack([hstack([budget,csr_matrix((len(blocks),1))]),hstack([csr_matrix(-pf[x,y]*(means/scale)),csr_matrix(cf[:,None])])],format='csr')
    r=linprog(np.r_[np.zeros(nb),-1.],A_ub=A,b_ub=np.r_[np.ones(len(blocks)),np.zeros(len(cf))],bounds=[(0,1)]*nb+[(0,None)],method='highs')
    if not r.success:raise ValueError(r.message)
    # Rationalize first; repair each budget exactly, independently of LP tolerances.
    weights=[Q(int(max(0.,v)*DEN),DEN) for v in r.x[:-1]];sums={}
    for ii,w in enumerate(weights):
     block=recs[ids[ii]]['block'];sums[block]=sums.get(block,Q(0))+w
    for ii,w in enumerate(weights):
     s=sums[recs[ids[ii]]['block']]
     if s>1:weights[ii]=w/s
    coeff=[[Q(0)]*len(exs) for k in range(M+1)];selected=[]
    for ii,w in enumerate(weights):
     if not w:continue
     rid=ids[ii];e=em[tuple(recs[rid]['population_exponents'])];selected.append([rid,str(w)])
     for k in range(M+1):coeff[k][e]+=w*betas[ii][k]
    tensor=Mat(coeff)*pm[x,y];delta=[]
    for k in range(M+1):
     vals=[]
     for col,c in enumerate(C[x,y]):
      if c:vals.append(tensor[k,col]/c)
      elif tensor[k,col]<0:raise ValueError('zero cost face')
     delta.append(min(vals))
    common=delta if common is None else [min(a,b) for a,b in zip(common,delta)]
    allocs.append({'x':x,'y':y,'weights':selected})
   baseline=list(map(Q,profile['profiles'][index]['bernstein']))
   if sum(common,Q(0))>sum(baseline,Q(0)):mode='regional';region_count+=1
   else:mode='inherited';common=baseline;allocs=[]
   a,b=F(item['a']),F(item['b']);mass=Q(str(old.U*(old.KNOTS[cell+1]-old.KNOTS[cell])*(b-a)));K+=mass*sum(common,Q(0))/(M+1)
   data.append({'interval_index':index,'mode':mode,'bernstein':list(map(str,common)),'regions':allocs})
   if index%16==0:print('REGIONAL',index,'mean',fl(sum(common,Q(0))/15),'old',fl(sum(baseline,Q(0))/15),'improved_intervals',region_count,'seconds',round(time.monotonic()-start,1),flush=True)
 K=F(str(K));oldK=F(profile['occupation_slack']);B0=F(joint['bound']);p=old.power_from_bernstein(list(map(F,joint['endpoint_bernstein'])))
 def endpoint(B):
  rho=(B-old.L)/(B0-old.L);z=[a*rho**i for i,a in enumerate(p)];z[0]+=K-oldK-(B-B0);return old.bernstein_from_power(z)
 lo=int(B0*DEN);hi=int(old.U*DEN)
 while lo+1<hi:
  mid=(lo+hi)//2
  if min(endpoint(F(mid,DEN)))>0:lo=mid
  else:hi=mid
 B=F(lo,DEN);c={'schema':'minexposure/regional-allocation-v1','base_certificate_sha256':BASE,'previous_certificate_sha256':JOINT,'profile_certificate_sha256':PROFILE,'source_certificate_sha256':base['source_certificate_sha256'],'bound':str(B),'previous_bound':str(B0),'occupation_slack':str(K),'old_occupation_slack':str(oldK),'population_degree':D,'cost_degree':M,'grid':n,'intervals':data,'endpoint_bernstein':list(map(str,endpoint(B)))}
 path=args.output/'certificate.json';path.write_text(json.dumps(c,separators=(',',':'))+'\n')
 summary={'status':'constructed; independent verification required','occupation_slack_display':float(K),'improved_intervals':region_count,'intervals':len(data),'grid':n,'bound':str(B),'bound_decimal':f'{lo//DEN}.{lo%DEN:012d}','exact_increase':str(B-B0),'certificate_sha256':sha(path.read_bytes())}
 (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
