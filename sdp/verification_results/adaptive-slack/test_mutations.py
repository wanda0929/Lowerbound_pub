#!/usr/bin/env python3
"""Reject deliberately corrupted copies of the actual regional certificate."""
import argparse,copy,json
from pathlib import Path
import verify as v

def main():
 p=argparse.ArgumentParser();p.add_argument('--certificate',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 base=v.load(v.ROOT/'population-refinement/certified/population-certificate.json.gz',v.BASE,True);joint=v.load(v.ROOT/'joint-slack/certified/certificate.json',v.JOINT);profile=v.load(v.ROOT/'joint-slack/certified/profile-certificate.json',v.PROFILE);c=json.loads(a.certificate.read_text())
 index=next(i for i,r in enumerate(c['intervals']) if r['mode']=='regional');passed=[]
 def trial(label,change):
  z=dict(c);z['intervals']=list(c['intervals']);z['intervals'][index]=copy.deepcopy(c['intervals'][index]);change(z)
  try:v.verify(z,base,joint,profile,verbose=False)
  except (ValueError,IndexError,KeyError):passed.append(label);print('REJECTED',label,flush=True)
  else:raise ValueError('accepted corruption '+label)
 entry=lambda z:z['intervals'][index]
 weights=lambda z:entry(z)['regions'][0]['weights']
 trial('duplicate projected contribution',lambda z:weights(z).append(copy.deepcopy(weights(z)[0])))
 trial('matrix allocation greater than one',lambda z:weights(z)[0].__setitem__(1,'2'))
 trial('negative matrix allocation',lambda z:weights(z)[0].__setitem__(1,'-1'))
 trial('unverified projection',lambda z:weights(z)[0].__setitem__(0,100000000))
 trial('missing population region',lambda z:entry(z)['regions'].pop())
 trial('overlapping population regions',lambda z:entry(z)['regions'].__setitem__(1,copy.deepcopy(entry(z)['regions'][0])))
 trial('inflated interval polynomial',lambda z:entry(z)['bernstein'].__setitem__(0,'1'))
 trial('double-counted cost interval',lambda z:z['intervals'].append(copy.deepcopy(entry(z))))
 trial('misassigned cost interval',lambda z:entry(z).__setitem__('interval_index',index+1))
 trial('changed original dependency',lambda z:z.__setitem__('base_certificate_sha256','0'*64))
 r={'status':'PASS','actual_certificate_mutations_rejected':len(passed),'tests':passed,'certificate_sha256':v.sha(a.certificate.read_bytes())};a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
