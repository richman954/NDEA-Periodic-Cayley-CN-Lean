"""Synthetic evidence tests only. None of these tests establishes a Lean theorem."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import evidence_audit as audit

class AxiomParserTests(unittest.TestCase):
    name = 'NDEAEvolve.Exp016.test'
    def text(self, values='propext, Classical.choice, Quot.sound'):
        return "'" + self.name + "' depends on axioms: [" + values + "]\n"
    def test_standard(self):
        self.assertEqual(len(audit.parse_axioms(self.text(), [self.name])[self.name]), 3)
    def test_multiline(self):
        self.assertEqual(len(audit.parse_axioms(self.text('propext,\n Classical.choice,\n Quot.sound'), [self.name])[self.name]), 3)
    def test_no_axioms(self):
        self.assertEqual(audit.parse_axioms("'" + self.name + "' does not depend on any axioms\n", [self.name])[self.name], [])
    def test_missing(self):
        with self.assertRaisesRegex(ValueError, 'Missing'): audit.parse_axioms('', [self.name])
    def test_duplicate(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate'): audit.parse_axioms(self.text()*2, [self.name])
    def test_suffix_spoof(self):
        with self.assertRaisesRegex(ValueError, 'Missing'): audit.parse_axioms(self.text().replace(self.name, 'Fake.'+self.name), [self.name])
    def test_log_prefix_spoof(self):
        with self.assertRaisesRegex(ValueError, 'Missing'): audit.parse_axioms('pretend '+self.text(), [self.name])
    def test_sorry_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Disallowed'): audit.parse_axioms(self.text('sorryAx'), [self.name])
    def test_custom_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Disallowed'): audit.parse_axioms(self.text('BadAssumption'), [self.name])
    def test_native_trust_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Disallowed'): audit.parse_axioms(self.text('Lean.trustCompiler'), [self.name])
    def test_missing_second_target(self):
        with self.assertRaisesRegex(ValueError, 'Missing'): audit.parse_axioms(self.text(), [self.name, 'Missing'])

class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root/'repo'; self.repo.mkdir()
        self.out = self.root/'out'; self.out.mkdir()
        self.put(self.repo, 'lean-toolchain', 'synthetic fixture, not Lean\n')
        sources, records = [], []
        names = [f'Fixture{i}' for i in range(80)] + ['UniformGridTimeConvergence']
        for i, name in enumerate(names):
            path = f'project/{name}.lean'
            self.put(self.repo, path, '-- synthetic source\n')
            self.put(self.out, f'sources/{name}.lean', '-- synthetic source\n')
            self.put(self.out, f'olean/{name}.olean', 'synthetic object, not executable proof\n')
            self.put(self.out, f'{i:03}_{name}.log', 'synthetic compiler log\n')
            row = {'module': name, 'path': path, 'sha256': audit.digest(self.repo/path)}
            sources.append(row)
            records.append({**row, 'command': ['synthetic-lean', '-o', str(self.out/f'olean/{name}.olean'), str(self.out/f'sources/{name}.lean')],
                            'log_sha256': audit.digest(self.out/f'{i:03}_{name}.log'),
                            'olean_sha256': audit.digest(self.out/f'olean/{name}.olean')})
        def git(*args):
            return subprocess.check_output(['git', '-C', str(self.repo), *args], stderr=subprocess.DEVNULL, text=True).strip()
        git('init'); git('add', '.')
        git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'synthetic fixture')
        self.commit = git('rev-parse', 'HEAD')
        self.write_json('plan.json', {'commit': self.commit, 'sources': sources, 'pins': {'lean-toolchain': audit.digest(self.repo/'lean-toolchain')}})
        self.write_json('compiled.json', {'complete': True, 'modules': records})
        self.write_json('result.json', {'status': 'TARGET_COMPILE_AND_AXIOM_AUDIT_PASS'})
        self.write_json('verification.json', {'status': 'SCOPED_CHECKS_PASS', 'commit': self.commit, 'independent_kernel': False, 'exp016_sealed': False})
        self.put(self.out, 'target-axioms.log', ''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in audit.EXPECTED))
        self.put(self.out, 'kernel-replay.log', 'replaying VerificationContracts with --fresh\n')
        self.write_json('kernel-replay.json', {'exit_code': 0, 'command': ['synthetic-checker', '--fresh', '--verbose', 'VerificationContracts'], 'log_sha256': audit.digest(self.out/'kernel-replay.log')})
        self.put(self.out, 'contract.log', 'synthetic contract log\n')
        self.put(self.out, 'sources/VerificationContracts.lean', '-- synthetic contract\n')
        self.put(self.out, 'olean/VerificationContracts.olean', 'synthetic contract object\n')
        controls = {}
        for name in audit.CONTROL_NAMES:
            declaration = 'FixtureBad'
            text = "'FixtureBad' depends on axioms: [sorryAx]\n" if name == 'sorry_axiom_rejected' else "'FixtureBad' depends on axioms: [Injected]\n"
            self.put(self.out, name+'.log', text)
            controls[name] = {'passed': True, 'declaration': declaration, 'exit_code': 1 if name in ('false_statement_rejected','missing_module_rejected') else 0,
                              'log': name+'.log', 'log_sha256': audit.digest(self.out/(name+'.log'))}
        self.write_json('controls.json', controls)
        self.seal()
    def put(self, root, path, text):
        dest = root/path; dest.parent.mkdir(parents=True, exist_ok=True); dest.write_text(text)
    def write_json(self, name, data): self.put(self.out, name, json.dumps(data))
    def change(self, name, mutation):
        data = json.loads((self.out/name).read_text()); mutation(data); self.write_json(name, data)
    def seal(self):
        self.write_json('EVIDENCE_MANIFEST.json', {'files': {str(p.relative_to(self.out)): audit.digest(p) for p in self.out.rglob('*') if p.is_file() and p.name != 'EVIDENCE_MANIFEST.json'}})
    def test_synthetic_valid_evidence_format(self): self.assertEqual(audit.audit(self.repo,self.out)['status'], 'EVIDENCE_AUDIT_PASS')
    def test_hash_tampering(self):
        self.put(self.out,'target-axioms.log','changed')
        with self.assertRaisesRegex(ValueError,'hash mismatch'): audit.audit(self.repo,self.out)
    def test_forged_pass_with_missing_proof(self):
        (self.out/'olean/UniformGridTimeConvergence.olean').unlink()
        with self.assertRaises(ValueError): audit.audit(self.repo,self.out)
    def test_wrong_commit(self):
        self.change('verification.json',lambda d:d.update(commit='0'*40)); self.seal()
        with self.assertRaisesRegex(ValueError,'Commit mismatch'): audit.audit(self.repo,self.out)
    def test_incomplete_compile(self):
        self.change('compiled.json',lambda d:d.update(complete=False)); self.seal()
        with self.assertRaisesRegex(ValueError,'incomplete'): audit.audit(self.repo,self.out)
    def test_missing_target_after_rehash(self):
        self.put(self.out,'target-axioms.log',''); self.seal()
        with self.assertRaisesRegex(ValueError,'Missing axiom'): audit.audit(self.repo,self.out)
    def test_replay_failure_after_rehash(self):
        self.change('kernel-replay.json',lambda d:d.update(exit_code=1)); self.seal()
        with self.assertRaisesRegex(ValueError,'replay failed'): audit.audit(self.repo,self.out)
    def test_claiming_independent_kernel(self):
        self.change('verification.json',lambda d:d.update(independent_kernel=True)); self.seal()
        with self.assertRaisesRegex(ValueError,'independent-kernel'): audit.audit(self.repo,self.out)
    def test_unsafe_path(self):
        with self.assertRaisesRegex(ValueError,'Unsafe'): audit.safe_file(self.out,'../outside')
    def test_changed_repository_source(self):
        self.put(self.repo,'project/Fixture0.lean','changed\n')
        with self.assertRaisesRegex(ValueError,'committed bytes'): audit.audit(self.repo,self.out)

if __name__ == '__main__': unittest.main()
