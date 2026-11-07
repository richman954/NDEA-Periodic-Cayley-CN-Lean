"""Offline tests of the checker. Passing does not mean any Lean proof passed."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('check_initial_error_transfer.py')
spec = importlib.util.spec_from_file_location('checker', SCRIPT)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)

class CheckerTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        text = '/- import Fake /- sorry -/ -/\nimport Mathlib.Data.Real.Basic -- admit\n#check "axiom"\n'
        self.assertEqual(checker.imports(text), ['Mathlib.Data.Real.Basic'])

    def test_multiple_imports(self):
        self.assertEqual(checker.imports('import Alpha Beta\n'), ['Alpha', 'Beta'])

    def test_forbidden_tokens(self):
        for word in ('sorry', 'admit', 'axiom', 'native_decide'):
            with self.subTest(word=word), self.assertRaises(ValueError):
                checker.imports('theorem bad : True := by ' + word)

    def test_unterminated_comment(self):
        with self.assertRaises(ValueError): checker.imports('/- unfinished')

    def test_unterminated_string(self):
        with self.assertRaises(ValueError): checker.imports('#check "unfinished')

    def put(self, root, exp, module, text):
        path = root / 'NDEA_Evolve_offruntime' / exp / 'lean' / (module + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_topological_closure(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.put(root, 'exp016', checker.TARGET, 'import Helper\n')
            self.put(root, 'exp015', 'Helper', 'import Mathlib\n')
            self.assertEqual([x['module'] for x in checker.resolve(root)], ['Helper', checker.TARGET])

    def test_missing_dependency_is_not_a_pass(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.put(root, 'exp016', checker.TARGET, 'import Missing\n')
            with self.assertRaisesRegex(ValueError, 'Missing project source'):
                checker.resolve(root)

    def test_conflicting_modules_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.put(root, 'exp016', checker.TARGET, 'import Helper\n')
            self.put(root, 'exp015', 'Helper', 'import Mathlib\n')
            self.put(root, 'exp014', 'Helper', 'import Mathlib.Data.Real.Basic\n')
            with self.assertRaisesRegex(ValueError, 'Conflicting project module'):
                checker.resolve(root)

    def test_identical_copies_allowed(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.put(root, 'exp016', checker.TARGET, 'import Helper\n')
            self.put(root, 'exp015', 'Helper', 'import Mathlib\n')
            self.put(root, 'exp014', 'Helper', 'import Mathlib\n')
            self.assertEqual(len(checker.resolve(root)), 2)

    def test_cycle_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.put(root, 'exp016', checker.TARGET, 'import Helper\n')
            self.put(root, 'exp015', 'Helper', 'import InitialErrorTransfer\n')
            with self.assertRaisesRegex(ValueError, 'Import cycle'):
                checker.resolve(root)

    def test_existing_output_untouched(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / 'repo'; root.mkdir()
            out = Path(folder) / 'out'; out.mkdir()
            result = out / 'result.json'; result.write_text('preserve me')
            proc = subprocess.run([sys.executable, str(SCRIPT), 'prepare', '--repo', str(root), '--output', str(out)], capture_output=True)
            self.assertNotEqual(proc.returncode, 0)
            self.assertEqual(result.read_text(), 'preserve me')

    def test_in_checkout_output_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            proc = subprocess.run([sys.executable, str(SCRIPT), 'prepare', '--repo', str(root), '--output', str(root/'out')], capture_output=True)
            self.assertNotEqual(proc.returncode, 0)
            self.assertFalse((root/'out').exists())

if __name__ == '__main__': unittest.main()
