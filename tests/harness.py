#!/usr/bin/env python3
"""Local harness regressions; no Mirage builds, network, vmnet, or HVF needed."""
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]


class Harness(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def run_cmd(self, args, **kwargs):
        return subprocess.run(args, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=12, **kwargs)

    def assert_dead(self, pid):
        for _ in range(50):
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return
            time.sleep(.02)
        self.fail(f'process {pid} survived supervisor cleanup')

    def test_timeout_and_status(self):
        wrapper = ['perl', str(ROOT / 'run-with-timeout.pl')]
        self.assertEqual(self.run_cmd(wrapper + ['2', 'sh', '-c', 'exit 7']).returncode, 7)
        self.assertEqual(self.run_cmd(wrapper + ['.1', 'true']).returncode, 255)
        self.assertEqual(self.run_cmd(wrapper + ['0.1', 'sleep', '5']).returncode, 124)

    def test_descendant_cleanup(self):
        for mode in ('exit', 'timeout', 'signal'):
            with self.subTest(mode=mode):
                pids = self.root / f'{mode}.pids'
                script = f'sleep 60 & echo $$ $! > "{pids}"; '
                script += 'exit 0' if mode == 'exit' else 'wait'
                proc = subprocess.Popen(['perl', str(ROOT / 'run-with-timeout.pl'),
                                         '0.2' if mode == 'timeout' else '5',
                                         'sh', '-c', script])
                self.addCleanup(lambda p=proc: p.poll() is None and p.kill())
                for _ in range(100):
                    if pids.exists():
                        break
                    time.sleep(.01)
                self.assertTrue(pids.exists())
                if mode == 'signal':
                    proc.send_signal(signal.SIGTERM)
                self.assertEqual(proc.wait(timeout=5), {'exit': 0, 'timeout': 124, 'signal': 143}[mode])
                for pid in map(int, pids.read_text().split()):
                    self.assert_dead(pid)

    def test_timeout_escalates(self):
        result = self.run_cmd(['perl', str(ROOT / 'run-with-timeout.pl'), '0.1',
                               'perl', '-e', '$SIG{TERM}="IGNORE"; sleep 60'])
        self.assertEqual(result.returncode, 124, result.stdout)

    def test_no_network_and_entropy_order(self):
        for name in ('run-matrix.sh', 'run-with-timeout.pl'):
            shutil.copy(ROOT / name, self.root)
        skeleton = self.root / 'skeleton'
        skeleton.mkdir()
        subprocess.run(['git', 'init', '-q', str(skeleton)], check=True)
        subprocess.run(['git', '-C', str(skeleton), '-c', 'user.name=Test',
                        '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture', '--allow-empty'], check=True)
        rev = subprocess.check_output(['git', '-C', str(skeleton), 'rev-parse', 'HEAD'], text=True).strip()
        bindir = self.root / 'bin'
        bindir.mkdir()
        tender = bindir / 'solo5-hvt'
        tender.write_text('#!/bin/sh\ncase "$*" in\n*--no-random*) echo "solo5_random unavailable";;\n*) echo "entropy sources: [1] rdrand, [7] solo5-host, [2] timer";;\nesac\n')
        tender.chmod(0o755)
        for name in ('mirage', 'opam'):
            tool = bindir / name
            tool.write_text('#!/bin/sh\nexit 99\n')
            tool.chmod(0o755)
        env = dict(os.environ, PATH=f'{bindir}:/usr/bin:/bin', SKELETON_REV=rev)
        result = self.run_cmd(['sh', str(self.root / 'run-matrix.sh'), '--no-build', '--no-network', 'entropy'], env=env)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('2 passed, 0 failed', result.stdout)
        env['SKELETON_REV'] = '0' * 40
        result = self.run_cmd(['sh', str(self.root / 'run-matrix.sh'), '--no-build', '--no-network', 'entropy'], env=env)
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn('expected ' + '0' * 40, result.stdout)

    def test_extraction_check_preserves_outputs(self):
        source = ROOT / 'unikernels/gradual'
        dest = self.root / 'gradual'
        dest.mkdir()
        for name in ('extract.sh', 'gradual_prog.v', 'gradual_prog.ml', 'gradual_prog.mli'):
            shutil.copy(source / name, dest)
        rocq = self.root / 'rocq'
        rocq.write_text('#!/bin/sh\ncp "$MOCK_SOURCE/gradual_prog.ml" .\ncp "$MOCK_SOURCE/gradual_prog.mli" .\n[ "${MOCK_STALE:-0}" = 0 ] || echo stale >> gradual_prog.ml\ntouch gradual_prog.vo\n')
        rocq.chmod(0o755)
        env = dict(os.environ, ROCQ=str(rocq), MOCK_SOURCE=str(source))
        result = self.run_cmd(['sh', str(dest / 'extract.sh'), '--check'], env=env)
        self.assertEqual(result.returncode, 0, result.stdout)
        env['MOCK_STALE'] = '1'
        result = self.run_cmd(['sh', str(dest / 'extract.sh'), '--check'], env=env)
        self.assertEqual(result.returncode, 1, result.stdout)
        for name in ('gradual_prog.ml', 'gradual_prog.mli'):
            self.assertEqual((dest / name).read_bytes(), (source / name).read_bytes())
        self.assertFalse((dest / 'gradual_prog.vo').exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
