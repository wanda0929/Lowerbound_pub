#!/usr/bin/env python3
"""Exercise actual retained certificates against their independent verifiers."""
import argparse,copy,gzip,hashlib,importlib.util,json,sys
from fractions import Fraction as F
from pathlib import Path
from flint import ctx
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    p=argparse.ArgumentParser();p.add_argument('--parts-dir',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();ctx.prec=384
    iv=module('crossing_independent',ROOT/'interface-population/verify.py')
    pv=module('profile_independent',ROOT/'cost-profile/verify.py')
    raw=gzip.decompress(b''.join((a.parts_dir/f'certificate.json.gz.part-{i:02d}').read_bytes() for i in range(2)))
    assert hashlib.sha256(raw).hexdigest()==iv.v.SOURCE
    source=json.loads(raw);del raw
    bases=json.loads((ROOT/'population-refinement/certified/interface-bases.json').read_text())
    ref=json.loads((ROOT/'population-refinement/certified/subdivision-certificate.json').read_text())
    base=json.loads(gzip.decompress((ROOT/'population-refinement/certified/population-certificate.json.gz').read_bytes()))
    c=json.loads((HERE/'certified/crossing-certificate.json').read_text());r=json.loads((HERE/'certified/profile-certificate.json').read_text());passed=[]
    def reject(name,original,mutation,verify):
        bad=copy.deepcopy(original);mutation(bad)
        try:verify(bad)
        except (ValueError,IndexError,KeyError):passed.append(name);print('REJECTED',name,flush=True);return
        raise ValueError('corruption accepted: '+name)
    check_cross=lambda z:iv.verify(z,source,bases,ref)
    reject('duplicate crossing allocation',c,lambda z:z['crossings'][0]['allocations'].append(copy.deepcopy(z['crossings'][0]['allocations'][0])),check_cross)
    reject('unsafe original-matrix subtraction',c,lambda z:z['records'][0].update(gamma='1000000000000'),check_cross)
    reject('invented population monomial',c,lambda z:z['records'][0].update(population_exponents=[99,0,0,0]),check_cross)
    reject('missing mandatory crossing',c,lambda z:z['crossings'].pop(),check_cross)
    reject('omitted selected matrix coordinate',c,lambda z:z['records'][0].update(active_indices=[]),check_cross)
    check_profile=lambda z:pv.verify(z,base,ref)
    reject('inflated cost-profile coefficient',r,lambda z:z['profiles'][0]['bernstein'].__setitem__(0,str(F(z['profiles'][0]['bernstein'][0])+1)),check_profile)
    reject('wrong cost-interval assignment',r,lambda z:z['profiles'][0].update(interval_index=1),check_profile)
    reject('double-counted cost interval',r,lambda z:z['profiles'].append(copy.deepcopy(z['profiles'][0])),check_profile)
    reject('false inherited occupation penalty',r,lambda z:z.update(base_occupation_slack='0'),check_profile)
    reject('changed original projection certificate',r,lambda z:z.update(base_certificate_sha256='0'*64),check_profile)
    report={'status':'PASS','actual_certificate_mutations_rejected':len(passed),'tests':passed,'source_certificate_sha256':iv.v.SOURCE}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
