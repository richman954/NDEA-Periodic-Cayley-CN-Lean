"""The retained builder audits InitialErrorTransfer; expanded audits run separately."""
import tempfile
import unittest
from pathlib import Path
import evidence_audit as audit
from run_assurance import ROOT, load_builder

class BuilderAdapterTests(unittest.TestCase):
    def fixture(self, root, declarations):
        path = root / ROOT / 'verification_initial_error/check_initial_error_transfer.py'
        path.parent.mkdir(parents=True)
        path.write_text('DECLARATIONS = ' + repr(tuple(declarations)) + '\n')

    def test_retained_import_keeps_initial_declarations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root, audit.INITIAL)
            builder = load_builder(root)
            self.assertEqual(builder.TARGET, 'UniformGridTimeConvergence')
            self.assertEqual(tuple(builder.DECLARATIONS), tuple(audit.INITIAL))
            self.assertNotEqual(tuple(builder.DECLARATIONS), tuple(audit.HORIZON))

    def test_changed_retained_audit_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root, audit.HORIZON)
            with self.assertRaisesRegex(ValueError, 'Retained builder audit changed'):
                load_builder(root)

if __name__ == '__main__': unittest.main()
