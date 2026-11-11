"""Replay every replacement projection, with persistent input-bound evidence.

Source PSD is reused from certificate-bindings.json; this checks matrix order,
not a new Lean proof term. Run after AllocationDataAudit.lean.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import ctx
from bind_allocations import packet, verify_lean_dump
from bind_certificates import LOWER, RAW, need
from bind_regions import module, domination_controls


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--lean-dump', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 384
    data = packet(args.checkout)
    verify_lean_dump(args.checkout, data, args.lean_dump)
    binding_path = Path('certificate-bindings.json')
    binding = json.loads(binding_path.read_text())
    need(binding['lower_raw_sha256'] == RAW and
         binding['lower_psd_replayed'] is True and
         binding['lower_audit']['all_gram_matrices_exactly_positive_semidefinite'] is True,
         'completed original PSD replay')
    raw = gzip.decompress(b''.join((args.checkout / LOWER /
        f'certificate.json.gz.part-{i:02}').read_bytes() for i in range(2)))
    need(hashlib.sha256(raw).hexdigest() == RAW, 'original Gram hash')
    source = json.loads(raw)
    del raw
    metadata = {(m['owner']['cell_index'], m['owner_block_index']): m
                for m in data['source_block_layouts']}
    directory = args.checkout / 'sdp/verification_results/population-refinement'
    sys.path.insert(0, str(directory))
    verifier = module(directory / 'verify_population_slack.py', 'allocation_matrix_verifier')
    controls = domination_controls(verifier)
    records = data['projections']
    cache, blocks, results, previous = {}, set(), [], None
    for rid in sorted(records, key=lambda i: (records[i]['block'], int(i))):
        rec = records[rid]
        key = (rec['cell'], rec['block'])
        if key != previous:
            cache.clear()
            previous = key
        verifier.check_projection(rec, metadata, source, cache)
        blocks.add(key)
        results.append(dict(source_projection=int(rid), cell=key[0], block=key[1],
            record_sha256=hashlib.sha256(json.dumps(rec, sort_keys=True).encode()).hexdigest()))
        if len(results) % 100 == 0:
            print(f'DOMINATION {len(results)}/{len(records)}', flush=True)
    need(len(results) == 1078 and len(blocks) == 626, 'all replacement projections')
    report = dict(status='PASS', projections=len(results), source_blocks=len(blocks),
        precision_bits=ctx.prec, source_sha256=RAW, decoded_sha256=sha(args.lean_dump),
        binding_sha256=sha(binding_path), allocation_sha256=data['allocation_sha256'],
        checker_sha256=sha(Path(__file__)), python_flint=flint.__version__,
        upstream_checkers={p.name: sha(p) for p in
            [directory/'verify_population_slack.py', directory/'verify_projected_slack.py']},
        negative_controls=controls, source_psd_replayed=False, kernel_proof_term=False,
        results=sorted(results, key=lambda r: r['source_projection']))
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: all 1078 replacement projections on 626 source blocks; Arb 384 bits')


if __name__ == '__main__':
    main()
