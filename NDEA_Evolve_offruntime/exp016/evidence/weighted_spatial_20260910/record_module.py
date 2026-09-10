"""Validate finished weighted-spatial modules against the frozen continuation state."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ACTIVE = HERE.parents[1]
RECOVERY = Path('/home/richman954/NDEA_Recovery')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
name = sys.argv[1]
rp = Path(sys.argv[2])
r = read(rp)
expected_counts = {'AliasWeights': 11, 'WeightedSampledPotential': 7}
assert name in expected_counts
source = ACTIVE / 'lean' / (name + '.lean')
artifact = ACTIVE / 'build/lib/lean' / (name + '.olean')
assert r['source'] == str(source) and r['exit_code'] == 0 and r['sources_unchanged']
assert sha(source) == r['source_sha256_before'] == r['source_sha256_after']
start = read(HERE / 'START_STATE.json')
assert r['lean_binary_sha256'] == start['compiler_sha256'] == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert r['mathlib_commit'] == 'fabf563a7c95a166b8d7b6efca11c8b4dc9d911f'
assert sha(ACTIVE / 'run_lean.py') == r['runner_sha256'] == start['runner_sha256']
assert sha(artifact) == r['output_sha256'][str(artifact)]
log = Path(r['log'])
assert sha(log) == r['log_sha256']
text = log.read_text()
assert 'error:' not in text and 'sorryAx' not in text
warning_lines = re.findall(r'warning: (.*)', text)
expected_warnings = ([] if name == 'AliasWeights' else [
    '`ContinuousLinearMap.zero_apply` has been deprecated: Use `zero_apply` instead'])
assert warning_lines == expected_warnings
audits = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S))
for decl in re.findall(r"'([^']+)' does not depend on any axioms", text):
    assert decl not in audits
    audits[decl] = ''
decls = re.findall(r'^theorem\s+(\w+)', source.read_text(), re.M)
assert set(audits) == {'NDEAEvolve.Exp016.' + n for n in decls}
assert len(audits) == expected_counts[name]
assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for a in audits.values())
for old, e in start['accepted_modules'].items():
    assert sha(ACTIVE / 'lean' / (old + '.lean')) == e['source_sha256'], old
    assert sha(e['receipt']) == e['receipt_sha256'] and sha(e['log']) == e['log_sha256'], old
    assert sha(ACTIVE / 'build/lib/lean' / (old + '.olean')) == e['artifact_sha256'], old
for rel, digest in start['project_import_artifacts'].items():
    assert sha(ACTIVE.parent / rel) == digest, rel
if name == 'WeightedSampledPotential':
    previous = read(HERE / 'AliasWeights_ACCEPTED.json')
    for key in ['source', 'artifact', 'receipt', 'log']:
        assert sha(previous[key]) == previous[key + '_sha256'], key
utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
report = {
    'utc': utc, 'passed': True, 'module': name,
    'source': str(source), 'source_sha256': sha(source),
    'artifact': str(artifact), 'artifact_sha256': sha(artifact),
    'receipt': str(rp), 'receipt_sha256': sha(rp),
    'log': str(log), 'log_sha256': sha(log),
    'compiler_exit': 0, 'elapsed_seconds': r['elapsed_seconds'],
    'explicit_axiom_reports': len(audits), 'axiom_dependencies': audits,
    'warnings': len(warning_lines), 'warning_messages': warning_lines, 'errors': 0,
    'warning_review': None if not warning_lines else {
        'classification': 'Deprecated name for the same proved lemma; retained warning-only success.',
        'pinned_mathlib_source': 'Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean:343',
        'declaration': '@[deprecated (since := "2026-05-20")] protected alias zero_apply := _root_.zero_apply',
        'proof_source_changed_after_check': False,
    },
    'previous_accepted_modules_unchanged': len(start['accepted_modules']),
    'preexisting_import_artifacts_unchanged': len(start['project_import_artifacts']),
    'qualification': 'Modular pinned development acceptance; no combined or fresh independent qualification.',
    'sealed': False, 'comparator_run': False, 'additional_independent_kernel_run': False,
}
target = HERE / (name + '_ACCEPTED.json')
with target.open('x') as f:
    f.write(json.dumps(report, indent=2) + '\n')
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
s = read(RECOVERY / 'TASK_STATE.json')
assert name not in s['accepted_active_modules']
s['accepted_active_modules'].append(name)
s['accepted_active_module_receipts'][name] = str(rp)
s['latest_development_milestone'] = str(target)
s['recovery']['current_check'] = {
    'module': name, 'status': 'passed; source, artifact, log and transitive axiom dependencies checked',
    'receipt': str(rp), 'source_sha256': sha(source),
    'pending_module': 'WeightedSampledPotential' if name == 'AliasWeights' else None,
}
s['continuation']['current_status'] = str(len(s['accepted_active_modules'])) + ' accepted development modules. ' + (
    'Alias minimization and actual DFT weighted mode bounds passed; finite-cutoff sampled-potential consumer is next.'
    if name == 'AliasWeights' else
    'Actual finite-cutoff sampled multiplication has a mesh-independent weighted DFT bound. Actual Cayley weighted propagation and spatial refinement remain open. Exp016 remains unsealed.')
s['continuation']['utc'] = utc
s['updated_utc'] = utc
c.atomic_bytes(RECOVERY / 'TASK_STATE.json', c.json_bytes(s))
print(json.dumps(report, indent=2))
