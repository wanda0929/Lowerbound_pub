"""CLI regressions against a completed first-tier replay, in disposable copies.

Run after `check_acceptance.py --replay CHECKOUT --write`. No production data
or receipt is changed, and the expensive numerical checks are not rerun here.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import check_acceptance as acceptance


class AcceptanceCLI(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='cz-acceptance-test-')
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        paths = set(acceptance.snapshot()) | set(acceptance.evidence_paths()) | {
            'acceptance-manifest.json', 'acceptance-replay.json'}
        for name in paths:
            target = self.root/name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(acceptance.ROOT/name, target)
        self.manifest = (self.root/'acceptance-manifest.json').read_bytes()

    def cli(self, *args):
        return subprocess.run([sys.executable, '-B', 'check_acceptance.py', *args],
                              cwd=self.root, capture_output=True, text=True)

    def rejected_write(self, reason):
        result = self.cli('--write')
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(reason, result.stderr)
        self.assertEqual((self.root/'acceptance-manifest.json').read_bytes(), self.manifest)

    def test_unchanged_replay_can_refresh_and_verify(self):
        for args in [('--write',), ()]:
            result = self.cli(*args)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('65 acceptance leaf fields mapped', result.stdout)

    def test_negative_terminal_diagonal_cannot_reuse_old_evidence(self):
        path = self.root/'LowerBoundCZ/ArchiveData.lean'
        text = path.read_text()
        start = text.index('"')+1
        stop = text.index(' ', start)
        self.assertNotEqual(text[start:stop], '-1,0')
        path.write_text(text[:start]+'-1,0'+text[stop:])
        self.rejected_write('replay inputs changed')

    def test_changed_interface_weights_cannot_reuse_old_evidence(self):
        path = self.root/'LowerBoundCZ/InterfaceData.lean'
        text = path.read_text()
        self.assertIn('"0:1|1:1|', text)
        path.write_text(text.replace('"0:1|1:1|', '"0:2|1:2|', 1))
        self.rejected_write('replay inputs changed')

    def test_changed_report_cannot_be_rebound(self):
        path = self.root/'archive-binding.json'
        report = json.loads(path.read_text())
        report['decoded_sha256'] = '0'*64
        path.write_text(json.dumps(report))
        self.rejected_write('replay evidence changed')

    def test_missing_replay_cannot_be_recreated_by_write(self):
        (self.root/'acceptance-replay.json').unlink()
        self.rejected_write('acceptance-replay.json')


if __name__ == '__main__':
    unittest.main()
