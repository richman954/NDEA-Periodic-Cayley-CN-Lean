"""Subprocess lookup regression tests with fake executables, NOT Lean proofs."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from replay_environment import PINNED_TOOLCHAIN, pinned_replay_environment


class ReplayEnvironmentTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.sysroot = root / 'pinned toolchain'
        self.bin = self.sysroot / 'bin'
        self.bin.mkdir(parents=True)
        self.lean = self.bin / 'lean'
        self.lean.write_text('#!' + sys.executable + '\nimport sys\n'
                             'assert sys.argv[1:] == ["--print-prefix"]\n'
                             'print(' + repr(str(self.sysroot)) + ')\n')
        self.lean.chmod(0o755)
        self.digest = hashlib.sha256(self.lean.read_bytes()).hexdigest()
        shimdir = root / 'unconfigured-elan'
        shimdir.mkdir()
        shim = shimdir / 'lean'
        shim.write_text('#!' + sys.executable + '\nimport sys\n'
                        'sys.stderr.write("error: no default toolchain configured\\n")\n'
                        'sys.exit(1)\n')
        shim.chmod(0o755)
        self.scratch = root / 'scratch'
        self.scratch.mkdir()
        self.env = {'PATH': str(shimdir), 'LEAN_PATH': '/isolated/project:/pinned/libraries',
                    'LEAN_SYSROOT': '/incorrect/root', 'LEAN_SRC_PATH': '/incorrect/source',
                    'ELAN_TOOLCHAIN': 'wrong/toolchain:stable'}

    def fixed(self):
        return pinned_replay_environment(self.lean, self.env, self.digest, PINNED_TOOLCHAIN)

    def test_reproduces_unconfigured_proxy_failure(self):
        proc = subprocess.run(['lean', '--print-prefix'], cwd=self.scratch, env=self.env,
                              text=True, capture_output=True, timeout=10)
        self.assertEqual(proc.returncode, 1)
        self.assertIn('no default toolchain configured', proc.stderr)

    def test_pinned_lookup_succeeds_without_project_toolchain_file(self):
        self.assertFalse((self.scratch / 'lean-toolchain').exists())
        proc = subprocess.run(['lean', '--print-prefix'], cwd=self.scratch, env=self.fixed(),
                              text=True, capture_output=True, timeout=10, check=True)
        self.assertEqual(Path(proc.stdout.strip()), self.sysroot)

    def test_nested_checker_subprocess_uses_pinned_lean(self):
        # Simulates findSysroot's nested process invocation, not kernel replay.
        program = ('import subprocess, json, os; '
                   'print(json.dumps({"root":subprocess.check_output('
                   '["lean","--print-prefix"],text=True).strip(),'
                   '"toolchain":os.environ["ELAN_TOOLCHAIN"]}))')
        proc = subprocess.run([sys.executable, '-c', program], cwd=self.scratch,
                              env=self.fixed(), text=True, capture_output=True,
                              timeout=10, check=True)
        self.assertEqual(json.loads(proc.stdout),
                         {'root': str(self.sysroot), 'toolchain': PINNED_TOOLCHAIN})

    def test_child_overrides_do_not_mutate_parent_or_import_path(self):
        before = dict(self.env)
        fixed = self.fixed()
        self.assertEqual(self.env, before)
        self.assertEqual(fixed['LEAN_PATH'], before['LEAN_PATH'])
        self.assertNotIn('LEAN_SYSROOT', fixed)
        self.assertNotIn('LEAN_SRC_PATH', fixed)
        self.assertEqual(fixed['ELAN_TOOLCHAIN'], PINNED_TOOLCHAIN)

    def test_compiler_hash_mismatch_rejected(self):
        with self.assertRaisesRegex(ValueError, 'SHA-256 mismatch'):
            pinned_replay_environment(self.lean, self.env, '0'*64, PINNED_TOOLCHAIN)

    def test_toolchain_change_rejected(self):
        with self.assertRaisesRegex(ValueError, 'toolchain pin'):
            pinned_replay_environment(self.lean, self.env, self.digest, 'leanprover/lean4:stable')

    def test_nonexecutable_compiler_rejected(self):
        self.lean.chmod(0o644)
        with self.assertRaisesRegex(ValueError, 'executable'):
            self.fixed()

    def test_missing_path_still_selects_pinned_compiler(self):
        env = pinned_replay_environment(self.lean, {}, self.digest, PINNED_TOOLCHAIN)
        proc = subprocess.run(['lean', '--print-prefix'], cwd=self.scratch, env=env,
                              text=True, capture_output=True, timeout=10, check=True)
        self.assertEqual(Path(proc.stdout.strip()), self.sysroot)


if __name__ == '__main__':
    unittest.main()
