#!/usr/bin/env python3
"""Produce rational reachability-restricted slack profiles.

Conditional domain: exact-CZ trajectories with terminal exposure at most cap.
This is a proof search, not an accepted lower bound until verify.py passes.
"""
from __future__ import annotations
import argparse,gzip,hashlib,importlib.util,json,sys
from fractions import Fraction as F
from pathlib import Path
from math import comb
from flint import fmpq as Q,fmpq_mat as Mat
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[1]
def module(name,p):
 spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
v=module('inherited_regional_verifier',ROOT/'adaptive-slack/verify.py')
cp=module('inherited_cost_producer',ROOT/'cost-profile/produce.py')
sys.path.insert(0,str(ROOT/'population-refinement'))
import certify_population_subdivision as old
REG='ca4813512b0b3b911ed37815012c29b1688173e3e5f8ebeb6a31361674a9b772'
TAIL='356384c59c270f7cf893c2b6c8a075951abfea66ef29b8ee2a6593881acd9129'
B0=F('2.931286076089')
HCOEF=[F(3*comb(2*k,k),4**k*(2*k+3)) for k in range(9)]
def sha(raw):return hashlib.sha256(raw).hexdigest()
def load(p,h,z=False):
 raw=p.read_bytes();raw=gzip.decompress(raw) if z else raw
 v.need(sha(raw)==h,'input hash '+str(p));return json.loads(raw)
def energy(p):
 h=sum((c*p**i for i,c in enumerate(HCOEF)),F(0));return p**3*h*h

def impossible(p,q,r):
 # Equivalent, with rational arithmetic, to sqrt(8*energy(p))+sqrt(energy(q)) > sqrt(72)*r.
 a=8*energy(p);b=energy(q);gap=72*r*r-a-b
 return gap<0 or gap*gap<4*a*b

def load_inputs():
 base=load(ROOT/'population-refinement/certified/population-certificate.json.gz',v.BASE,True)
 reg=load(ROOT/'adaptive-slack/certified/certificate.json.gz',REG,True)
 tail=load(ROOT/'adaptive-slack/certified/tail-certificate.json',TAIL)
 v.need(F(tail['bound'])==B0,'latest endpoint')
 return base,reg,tail

def regional_tensor(groups,a,b):
 exs=sorted(groups)
 co=[cp.elevate(cp.bern(p.copy(),a,b),14) for p in [groups[e] for e in exs]]
 return exs,Mat([[co[m][k] for m in range(len(exs))] for k in range(15)])

def population(ex,x,y,n,cache):
 key=(ex,x,y,n)
 if key not in cache:
  g,r,h,s=ex
  def uni(g,r,i):
   poly=[Q(0)]*(g+r+1)
   for k in range(g+1):poly[r+k]=Q((-1)**k*comb(g,k))
   return cp.elevate(cp.bern(poly,F(i,n),F(i+1,n)),7)
  X=uni(g,r,x);Y=uni(h,s,y);cache[key]=[a*b for a in X for b in Y]
 return cache[key]

def make(base,reg,tail,cap,n):
 v.need(B0<cap<v.U and n in (4,8,16,32) and n%reg['grid']==0,'configuration')
 recs=base['projection_records'];allowed={i for item in base['integration_bins'] for i,w,s in item['allocations']}
 popcache={};new=[];gain=F(0);removed=0;improved=0;K=F(0);oldK=F(0);ng=reg['grid'];factor=n//ng
 for index,(item,entry) in enumerate(zip(base['integration_bins'],reg['intervals'])):
  j=item['cell'];a=F(item['a']);b=F(item['b']);width=v.KNOTS[j+1]-v.KNOTS[j]
  A=v.U*(v.KNOTS[j]+width*a);D=v.U*(v.KNOTS[j]+width*b);R=min(D,cap-A)
  prior=list(map(F,entry['bernstein']));mean0=sum(prior,F(0))/15;oldK+=(D-A)*mean0
  out={'interval_index':index,'mode':'inherited','bernstein':list(map(str,prior))}
  # Skip intervals where even the far corner is allowed: the reachability test cannot remove a state there.
  if entry['mode']=='regional' and impossible(F(1),F(1),R):
   ds=None;drop=0;alive=0
   for region in entry['regions']:
    x0=region['x']*factor;y0=region['y']*factor
    cells=[(x,y) for x in range(x0,x0+factor) for y in range(y0,y0+factor)]
    cells_ok=[]
    for x,y in cells:
     if impossible(F(x,n),F(y,n),R):drop+=1
     else:cells_ok.append((x,y))
    if not cells_ok:continue
    groups,_,_=v.region_weights(region,recs,allowed,j);exs,M=regional_tensor(groups,a,b)
    for x,y in cells_ok:
     P=Mat([population(e,x,y,n,popcache) for e in exs]);values=M*P
     cost=[Q(x*7+i,2*n*7)+Q(y*7+k,4*n*7) for i in range(8) for k in range(8)]
     ds1=[]
     for k in range(15):
      ratios=[]
      for col,c in enumerate(cost):
       if c:ratios.append(values[k,col]/c)
       else:v.need(values[k,col]>=0,'zero-cost coefficient')
      ds1.append(min(ratios))
     ds=ds1 if ds is None else [min(x,y) for x,y in zip(ds,ds1)];alive+=1
   v.need(alive>0 and drop+alive==n*n,'covering population partition')
   proposal=list(map(lambda x:F(str(x)),ds));mean=sum(proposal,F(0))/15
   if mean>mean0:
    out.update(mode='reachable',bernstein=list(map(str,proposal)),discarded_boxes=drop,retained_boxes=alive)
    removed+=drop;improved+=1;gain+=(D-A)*(mean-mean0)
  K+=(D-A)*sum(map(F,out['bernstein']),F(0))/15;new.append(out)
  if index%32==0:print('REACHABILITY_INTERVAL',index,'improved',improved,'gain',float(gain),flush=True)
 v.need(oldK==F(reg['occupation_slack']) and K-oldK==gain and gain>0,'integral improvement')
 previous=list(map(F,tail['endpoint_bernstein']));power=old.power_from_bernstein(previous)
 def endpoint(B):
  rho=(B-v.L)/(B0-v.L);p=[c*rho**i for i,c in enumerate(power)];p[0]+=gain-(B-B0);return old.bernstein_from_power(p)
 scale=10**12;lo=int(B0*scale);hi=int(cap*scale)+1
 while lo+1<hi:
  mid=(lo+hi)//2
  if min(endpoint(F(mid,scale)))>0:lo=mid
  else:hi=mid
 B=F(lo,scale);v.need(B0<B<=cap and min(endpoint(B))>0,'no certified candidate endpoint')
 return {'schema':'minexposure/reachability-slack-v1','status':'producer exact; independent verification required','source_certificate_sha256':v.SOURCE,'base_certificate_sha256':v.BASE,'regional_certificate_sha256':REG,'previous_certificate_sha256':TAIL,'previous_bound':str(B0),'counterexample_cap':str(cap),'grid':n,'barrier_series_order':8,'intervals':new,'old_prefix_slack':str(oldK),'new_prefix_slack':str(K),'additional_slack':str(gain),'bound':str(B),'bound_decimal':v.dec(B),'endpoint_bernstein':list(map(str,endpoint(B))),'changed_intervals':improved,'discarded_boxes':removed,'scope':'all-duration ideal-blockade stationary-torus; terminal sublevel used only in contradiction'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--cap',default='2.932');ap.add_argument('--grid',type=int,default=8);args=ap.parse_args();base,reg,tail=load_inputs()
 result=make(base,reg,tail,F(args.cap),args.grid);args.output.mkdir(parents=True,exist_ok=True);p=args.output/'certificate.json';p.write_text(json.dumps(result,indent=2)+'\n')
 summary={k:result[k] for k in ['status','bound','bound_decimal','previous_bound','counterexample_cap','grid','changed_intervals','discarded_boxes']};summary.update(additional_slack_display=float(F(result['additional_slack'])),certificate_sha256=sha(p.read_bytes()))
 (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('SUMMARY',json.dumps(summary),flush=True)
if __name__=='__main__':main()
