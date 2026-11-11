"""Replay the agreed Lean + external finite-check acceptance on one snapshot.

Usage: python -B check_unified.py /path/to/Lowerbound_pub
Requires Lake on PATH and python-flint. This does not recompute every historical
numerical report or discharge Appendix E's explicit superposition hypothesis.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

import check_acceptance as acceptance

ROOT = Path(__file__).resolve().parent
PUBLICATION_REV = '139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2'


def snapshot():
    result = acceptance.snapshot()
    extra = list((ROOT / 'appendix-e').glob('*Audit.lean')) + [
        ROOT / 'lake-manifest.json', ROOT / 'appendix-e/lake-manifest.json']
    result.update({str(p.relative_to(ROOT)): acceptance.sha(p) for p in extra})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication', type=Path)
    args = parser.parse_args()
    publication = args.publication.resolve()
    revision = subprocess.check_output(
        ['git', '-C', str(publication), 'rev-parse', 'HEAD'], text=True).strip()
    acceptance.need(revision == PUBLICATION_REV, 'publication revision mismatch')
    dirty = subprocess.check_output(
        ['git', '-C', str(publication), 'status', '--porcelain'], text=True)
    acceptance.need(not dirty, 'publication checkout is not clean')
    sources = snapshot()
    evidence = ROOT / 'unified-evidence'
    evidence.mkdir(exist_ok=True)
    runs = []

    def run(name, command):
        print(f'RUN {name}', flush=True)
        log = evidence / (name + '.txt')
        with log.open('w') as output:
            subprocess.run(command, cwd=ROOT, stdout=output,
                           stderr=subprocess.STDOUT, check=True)
        runs.append(dict(name=name, command=command, exit_code=0,
                         log=str(log.relative_to(ROOT)), sha256=acceptance.sha(log)))

    run('all-libraries', ['lake', 'build', 'LowerBoundCZ', 'RequestProject'])
    run('finite-replay', [sys.executable, '-B', 'check_acceptance.py',
                         '--replay', str(publication), '--write'])
    run('finite-manifest', [sys.executable, '-B', 'check_acceptance.py'])
    run('cli-regressions', [sys.executable, '-B', '-m', 'unittest', '-v', 'test_acceptance'])
    audits = [ROOT / name for name in [
        'NoGoAudit.lean', 'AppendixBDAudit.lean', 'AppendixEAudit.lean',
        'CertificateContractsAudit.lean']]
    audits += sorted((ROOT / 'appendix-e').glob('*Audit.lean'))
    for audit in audits:
        path = str(audit.relative_to(ROOT))
        run(path.replace('/', '-').removesuffix('.lean'),
            ['lake', 'env', 'lean', '-M', '12000', path])
    acceptance.need(sources == snapshot(), 'source drift during unified acceptance')
    acceptance.validate_replay()
    acceptance.validate_reports()
    receipt = dict(
        schema='LowerBoundCZ.unified-acceptance.v1', status='PASS',
        completed_utc=datetime.now(timezone.utc).isoformat(),
        sources=sources, publication_revision=revision, runs=runs,
        acceptance_manifest_sha256=acceptance.sha(ROOT / 'acceptance-manifest.json'),
        acceptance_replay_sha256=acceptance.sha(ROOT / 'acceptance-replay.json'),
        trust_boundary='Lean reasoning plus external finite checks; historical numerical '
                       'reports reused only after exact decoded-input matching; Appendix E '
                       'retains EuclideanCurrentSuperposition as an explicit hypothesis')
    target = ROOT / 'unified-acceptance.json'
    temporary = target.with_suffix('.tmp')
    temporary.write_text(json.dumps(receipt, indent=2) + '\n')
    temporary.replace(target)
    print(f'PASS: {len(audits)} Lean audits; unified receipt saved', flush=True)


if __name__ == '__main__':
    main()
