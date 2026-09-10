"""Source-bound modular acceptance, retaining the recovered 59-module baseline."""
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
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
name, receipt = sys.argv[1], Path(sys.argv[2])
counts = {'WeightedSlabSpatialBudget': 6, 'SpatialScalarRefinement': 8, 'SmoothCutoffConvergence': 3}
assert name in counts
source = ACTIVE / 'lean' / (name + '.lean')
artifact = ACTIVE / 'build/lib/lean' / (name + '.olean')
r = read(receipt)
start = read(ACTIVE / 'evidence/recovery_20260910T0220/START_STATE.json')
assert r['exit_code'] == 0 and r['sources_unchanged'] and r['source'] == str(source)
assert sha(source) == r['source_sha256_before'] == r['source_sha256_after']
assert r['lean_binary_sha256'] == start['compiler_sha256']
assert sha(ACTIVE / 'run_lean.py') == r['runner_sha256'] == start['runner_sha256']
assert r['mathlib_commit'] == start['mathlib_commit']
assert sha(artifact) == r['output_sha256'][str(artifact)]
log = Path(r['log'])
assert sha(log) == r['log_sha256']
text = log.read_text()
assert 'error:' not in text and 'sorryAx' not in text
warnings = re.findall(r'warning: (.*)', text)
assert warnings == [], warnings
audits = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S))
for decl in re.findall(r"'([^']+)' does not depend on any axioms", text):
    assert decl not in audits
    audits[decl] = ''
decls = re.findall(r'^theorem\s+(\w+)', source.read_text(), re.M)
assert set(audits) == {'NDEAEvolve.Exp016.' + d for d in decls}
assert len(audits) == counts[name]
assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for a in audits.values())
for old, e in start['accepted_modules'].items():
    assert sha(ACTIVE / 'lean' / (old + '.lean')) == e['source_sha256'], old
    assert sha(ACTIVE / 'build/lib/lean' / (old + '.olean')) == e['artifact_sha256'], old
    for kind in ['receipt', 'log']:
        assert sha(e[kind]) == e[kind + '_sha256'], (old, kind)
for rel, digest in start['project_import_artifacts'].items():
    assert sha(ACTIVE.parent / rel) == digest, rel
new_accepted = {}
for p in HERE.glob('*_ACCEPTED.json'):
    e = read(p)
    assert e['passed'] and e['compiler_exit'] == 0
    for kind in ['source', 'artifact', 'receipt', 'log']:
        assert sha(e[kind]) == e[kind + '_sha256'], (e['module'], kind)
    new_accepted[e['module']] = e
task = read(RECOVERY / 'TASK_STATE.json')
assert set(task['accepted_active_modules']) == set(start['accepted_modules']) | set(new_accepted)
assert name not in task['accepted_active_modules']
report = {'utc': c.utc(), 'passed': True, 'module': name, 'compiler_exit': 0,
    'source': str(source), 'source_sha256': sha(source),
    'artifact': str(artifact), 'artifact_sha256': sha(artifact),
    'receipt': str(receipt), 'receipt_sha256': sha(receipt),
    'log': str(log), 'log_sha256': sha(log),
    'explicit_axiom_reports': len(audits), 'axiom_dependencies': audits,
    'errors': 0, 'warnings': warnings, 'elapsed_seconds': r['elapsed_seconds'],
    'previous_accepted_modules_unchanged': len(task['accepted_active_modules']),
    'recovered_project_import_artifacts_unchanged': len(start['project_import_artifacts']),
    'accepted_new_imports_unchanged': sorted(new_accepted),
    'qualification': 'Pinned modular development acceptance; not combined or fresh independent qualification.',
    'combined_qualification': False, 'fresh_independent_qualification': False,
    'comparator_run': False, 'additional_independent_kernel_run': False, 'sealed': False,
    'validator': str(Path(__file__)), 'validator_sha256': sha(__file__)}
target = HERE / (name + '_ACCEPTED.json')
with target.open('x') as f:
    f.write(json.dumps(report, indent=2) + '\n')
task['accepted_active_modules'].append(name)
task['accepted_active_module_receipts'][name] = str(receipt)
task['latest_development_milestone'] = str(target)
task['recovery']['current_durable_off_device_backup_verified'] = False
task['recovery']['current_check'] = {'module': name, 'status': 'passed and source/dependency/axiom audited',
    'receipt': str(receipt), 'source_sha256': sha(source), 'log': str(log)}
for job in task.get('job_register', []):
    if job.get('receipt') == str(receipt):
        job.update({'status': 'completed; compiler exit 0, source-bound development acceptance passed',
            'observed_utc': c.utc(), 'elapsed_seconds': r['elapsed_seconds']})
task['continuation']['current_status'] = str(len(task['accepted_active_modules'])) + \
    ' accepted development modules; latest ' + name + '. Exp016 unsealed; current ledger tracks remaining obligations.'
task['continuation']['utc'] = c.utc()
task['updated_utc'] = c.utc()
c.atomic_bytes(RECOVERY / 'TASK_STATE.json', c.json_bytes(task))
print(json.dumps(report, indent=2))
