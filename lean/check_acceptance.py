"""Index first-tier evidence; this is NOT a numerical replay or a Lean proof.

--replay CHECKOUT runs the decoders and binds their outputs to the numerical
reports. --write only assembles a manifest from that completed replay; it
cannot rebind old evidence to changed inputs. No option creates a Lean proof.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads((ROOT / path).read_text())


def fields(file, structure):
    text = (ROOT / 'LowerBoundCZ' / (file+'.lean')).read_text()
    match = re.search(r'^structure '+re.escape(structure)+r'\b[^\n]* where\n', text, re.M)
    need(match is not None, f'missing structure {structure}')
    body = re.split(r'\n(?=\S)', text[match.end():], maxsplit=1)[0]
    return re.findall(r'^  (\w+) :', body, re.M)


def obligations():
    result = {}

    def add(prefix, names, evidence):
        for name in names:
            key = f'{prefix}.{name}' if name else prefix
            need(key not in result, f'duplicate field {key}')
            result[key] = evidence

    archive = ['archive-binding.json', 'acceptance-evidence/archive-lean.txt']
    source = ['source-identities.json']
    tensor = ['allocated-identities.json', 'residual-correspondence.json']
    psd = ['certificate-bindings.json', 'archive-binding.json']
    coverage = ['acceptance-evidence/coverage-lean.txt', 'acceptance-evidence/coverage-binding.txt']
    endpoint = ['acceptance-evidence/prefix-lean.txt', 'acceptance-evidence/prefix-binding.txt',
                'acceptance-evidence/endpoint-binding.txt']
    for family in fields('FixedArchive', 'LayoutChecks'):
        add('layout.'+family, fields('GramBridge', 'RawBlock.Valid'), archive)
    for name in fields('GramBridge', 'MatrixChecks'):
        add('base', [name], psd if name.endswith('_psd') else
            archive if name == 'terminal_identity' else archive+source)
    add('traversal.full', fields('OccupationLedger', 'LayoutChecks'), endpoint)
    add('traversal', ['reached'], endpoint)
    add('bootstrap', fields('MandatoryPrefix', 'EndpointChecks'), endpoint)
    add('endpoint', [''], endpoint)
    add('coverage', fields('OccupationCoverage', 'DataChecks'), coverage)
    for family, module, domination in [
        ('allocation', 'PinnedAllocations', 'LowerBoundCZ/AllocationData/domination.json'),
        ('regional', 'PinnedRegions', 'LowerBoundCZ/RegionalData/domination.json'),
        ('interfaces', 'PinnedInterfaces', 'LowerBoundCZ/InterfaceData.json')]:
        for name in fields(module, 'NumericalChecks'):
            if name == 'blocks':
                for sub in fields('SlackAllocation', 'AllocatedBlock.Checks'):
                    add(f'{family}.blocks', [sub], psd if sub == 'psd' else
                        [domination] if sub == 'domination' else ['allocated-identities.json'])
            else:
                evidence = (psd if name == 'source_psd' else
                    [domination] if name == 'domination' else
                    source if name == 'source_identity' else
                    tensor if name.startswith('tensor_') else ['allocated-identities.json'])
                add(family, [name], evidence)
    add('upper', fields('CertificateContracts', 'NumericalBounds') +
        fields('UpperAD', 'Enclosures'), ['certificate-bindings.json'])
    need(set(fields('FixedArchive', 'Acceptance')) == {k.split('.')[0] for k in result},
         'acceptance top-level fields changed')
    need(fields('MandatoryPrefix', 'LayoutChecks') == ['full', 'reached'], 'traversal schema changed')
    need(len(result) == 65, 'review the changed leaf-field schema')
    return result


def validate_reports():
    base = read('certificate-bindings.json')
    raw = base['lower_raw_sha256']
    need(base['lower_psd_replayed'] and
         base['lower_audit']['all_gram_matrices_exactly_positive_semidefinite'] and
         base['lower_audit']['nonzero_exact_residual_count'] == 0, 'base PSD/identities')
    need(base['generated_lean_sha256'] == sha(ROOT/'LowerBoundCZ/CertificateData.lean'), 'base payload drift')
    need(base['upper_exact_box_inclusion'] and 0 <= Fraction(base['upper_contraction']) < 1 and
         Fraction(base['upper_branch'][1]) < 0 and
         Fraction(base['upper_exposure'][1]) < Fraction('2.935875225844105'), 'upper report bounds')
    for name in ['archive-binding.json', 'LowerBoundCZ/AllocationData/domination.json',
                 'LowerBoundCZ/RegionalData/domination.json']:
        report = read(name)
        need(report['status'] == 'PASS' and report['source_sha256'] == raw, f'archive mismatch {name}')
    for name in ['source-identities.json', 'allocated-identities.json', 'residual-correspondence.json']:
        report = read(name)
        need(report['status'] == 'PASS', f'failed report {name}')
        for key in ['definitions_sha256', 'sha256']:
            for path, digest in report.get(key, {}).items():
                p = Path(path)
                if not p.is_absolute():
                    p = ROOT / p
                elif '/lean/' in path:
                    p = ROOT / path.split('/lean/', 1)[1]
                else:
                    continue  # External dumps and pinned checkout: replay separately.
                # This audit now additionally checks unit row weights. Its
                # output must be byte-identical in a fresh, bound replay before
                # old coefficient reports can be reused. Do not rewrite them.
                if p != ROOT/'InterfaceDataAudit.lean':
                    need(sha(p) == digest, f'stale evidence: {name}: {path}')
    source = read('source-identities.json')['decoded_sha256']
    for family, folder in [('allocation', 'AllocationData'), ('regional', 'RegionalData')]:
        dom = read(f'LowerBoundCZ/{folder}/domination.json')
        need(dom['decoded_sha256'] == source[family] and
             dom['binding_sha256'] == sha(ROOT/'certificate-bindings.json'), 'domination input mismatch')
    for family in ['allocation', 'regional', 'interface']:
        need(read('allocated-identities.json')[family]['decoded_sha256'] == source[family],
             'allocated/source dump mismatch')
    need(read('LowerBoundCZ/InterfaceData.json')['source'] == raw and
         read('LowerBoundCZ/InterfaceData.json')['external_checks']['status'] == 'PASS', 'interface report')
    a = read('archive-binding.json')
    need(a['checker_sha256'] == sha(ROOT/'bind_archive.py') and
         a['nonterminal_blocks'] == 4216 and a['terminal_coefficient_identities'] == 75, 'fixed archive report')


def snapshot():
    paths = set(ROOT.glob('*.lean')) | set(ROOT.glob('*.py'))
    paths |= set((ROOT/'LowerBoundCZ').rglob('*.lean'))
    paths |= set((ROOT/'appendix-e/RequestProject').rglob('*.lean'))
    paths |= {ROOT/'lean-toolchain', ROOT/'lakefile.toml',
              ROOT/'appendix-e/lean-toolchain', ROOT/'appendix-e/lakefile.toml'}
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths) if p.is_file()}


AUDITS = {
    'potential': 'SourceIdentityDataAudit.lean',
    'allocation': 'AllocationDataAudit.lean',
    'regional': 'RegionalDataAudit.lean',
    'interface': 'InterfaceDataAudit.lean',
    'factors': 'ResidualFactorsAudit.lean',
    'archive': 'FixedArchiveAudit.lean',
    'coverage': 'CoverageDataAudit.lean',
    'prefix': 'PrefixDataAudit.lean',
}
BINDERS = ['archive-binding', 'coverage-binding', 'prefix-binding', 'endpoint-binding']


def evidence_paths():
    return sorted({p for values in obligations().values() for p in values} |
                  {f'acceptance-evidence/{name}-lean.txt' for name in AUDITS} |
                  {'acceptance-evidence/build.txt'} |
                  {f'acceptance-evidence/{name}.txt' for name in BINDERS})


def expected_dumps():
    expected = dict(read('source-identities.json')['decoded_sha256'])
    expected['archive'] = read('archive-binding.json')['decoded_sha256']
    hashes = read('residual-correspondence.json')['sha256']
    factors = [v for k,v in hashes.items() if Path(k).name == 'residual-factors.txt']
    need(len(factors) == 1, 'one residual factor input')
    expected['factors'] = factors[0]
    return expected


def validate_replay():
    record = read('acceptance-replay.json')
    need(record['schema'] == 'LowerBoundCZ.decode-replay.v1', 'replay schema')
    need(record['sources'] == snapshot(), 'replay inputs changed; run --replay before --write')
    need(set(record['evidence']) == set(evidence_paths()), 'incomplete replay evidence')
    for p,digest in record['evidence'].items():
        need(sha(ROOT/p) == digest, f'replay evidence changed: {p}')
    need(set(record['runs']) == {'build', *AUDITS, *BINDERS}, 'incomplete replay runs')
    need(all(run['exit_code'] == 0 for run in record['runs'].values()), 'failed replay run')
    need(set(record['dumps']) == {*AUDITS, 'final'}, 'incomplete decoded outputs')
    for name,digest in expected_dumps().items():
        need(record['dumps'][name] == digest, f'replay differs from numerical input: {name}')


def replay(checkout):
    """Produce provenance by executing, never by accepting caller-supplied hashes.

    All expensive numerical reports are reused only with identical decoded
    inputs. Coverage and endpoint binders run again because their older text
    records did not carry input hashes. Publish the receipt only after success.
    """
    sources = snapshot()
    reports = {p: sha(ROOT/p) for p in evidence_paths() if p.endswith('.json')}
    validate_reports()
    expected = expected_dumps()
    runs = {}
    (ROOT/'acceptance-evidence').mkdir(exist_ok=True)

    def run(name, command, log):
        print(f'RUN {name}', flush=True)
        with (ROOT/'acceptance-evidence'/log).open('w') as out:
            subprocess.run(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT, check=True)
        runs[name] = dict(command=command, exit_code=0)

    with tempfile.TemporaryDirectory(prefix='cz-acceptance-') as directory:
        paths = {name: str(Path(directory)/(name+'.txt')) for name in [*AUDITS, 'final']}
        run('build', ['lake', 'build'], 'build.txt')
        for name,audit in AUDITS.items():
            outputs = [paths[name]] + ([paths['final']] if name == 'prefix' else [])
            run(name, ['lake', 'env', 'lean', '-M', '12000', '--run', audit, *outputs], name+'-lean.txt')
            if name in expected:
                need(sha(Path(paths[name])) == expected[name], f'new decoder differs from numerical input: {name}')
        run('archive-binding', [sys.executable, 'bind_archive.py', str(checkout),
            '--lean-dump', paths['archive']], 'archive-binding.txt')
        run('coverage-binding', [sys.executable, 'bind_coverage.py', str(checkout),
            '--lean-dump', paths['coverage']], 'coverage-binding.txt')
        for name,output,extra in [('prefix-binding', 'prefix', []), ('endpoint-binding', 'final', ['--final'])]:
            run(name, [sys.executable, 'bind_prefix.py', str(checkout),
                '--lean-dump', paths[output], *extra], name+'.txt')
        dumps = {name: sha(Path(path)) for name,path in paths.items()}
    need(sources == snapshot(), 'sources changed during replay')
    need(all(sha(ROOT/p) == digest for p,digest in reports.items()), 'numerical reports changed during replay')
    validate_reports()
    record = dict(schema='LowerBoundCZ.decode-replay.v1', sources=sources,
        evidence={p: sha(ROOT/p) for p in evidence_paths()}, dumps=dumps, runs=runs,
        trust_boundary='external decoder execution and exact-input reuse; not kernel proof terms')
    target = ROOT/'acceptance-replay.json'
    temporary = target.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2)+'\n')
    temporary.replace(target)
    validate_replay()
    print('PASS: fresh decoder outputs bound to unchanged numerical reports', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--replay', type=Path, metavar='CHECKOUT')
    args = parser.parse_args()
    expected = obligations()
    path = ROOT/'acceptance-manifest.json'
    if args.replay:
        replay(args.replay.resolve())
        if not args.write:
            return
    validate_replay()
    validate_reports()
    if args.write:
        evidence = evidence_paths() + ['acceptance-replay.json']
        for p in evidence:
            if p.endswith('.txt') and p != 'acceptance-evidence/build.txt':
                need('PASS:' in (ROOT/p).read_text() and 'error:' not in (ROOT/p).read_text(), f'failed log {p}')
        manifest = dict(schema='LowerBoundCZ.first-tier-evidence.v1',
            theorem='LowerBoundCZ.Certification.FixedArchive.lab_window',
            conclusion='2.931287735220 <= labCstar < 2.935875225844105',
            kernel_acceptance_instance=False, numerical_replay_performed_by_this_script=False,
            fields={k: dict(status='external-evidence', evidence=v) for k,v in expected.items()},
            files={**snapshot(), **{p: sha(ROOT/p) for p in evidence}})
        path.write_text(json.dumps(manifest, indent=2)+'\n')
    manifest = read('acceptance-manifest.json')
    need(manifest['fields'] == {k: dict(status='external-evidence', evidence=v) for k,v in expected.items()},
         'missing or changed acceptance field/evidence')
    for p,digest in manifest['files'].items():
        need(sha(ROOT/p) == digest, f'manifest file changed: {p}')
    need(all(manifest['files'].get(p) == digest for p,digest in snapshot().items()), 'unrecorded source file')
    print(f'PASS: {len(expected)} acceptance leaf fields mapped; {len(manifest["files"])} local file hashes match')
    print('Evidence index only: external finite checks remain hypotheses, not kernel proof terms.')


if __name__ == '__main__':
    main()
