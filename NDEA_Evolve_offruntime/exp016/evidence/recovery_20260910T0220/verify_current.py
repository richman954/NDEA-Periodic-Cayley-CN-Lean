"""Read-only byte reconciliation, not a rerun or promotion of proof acceptance."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
ACTIVE = HERE.parents[1]
RECOVERY = Path('/home/richman954/NDEA_Recovery')
read = lambda p: json.loads(Path(p).read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
task = read(RECOVERY / 'TASK_STATE.json')
assert task['active_experiment'] == str(ACTIVE)
previous = read(ACTIVE / 'evidence/initial_weighted_20260910/START_STATE.json')
accepted = previous['accepted_modules'].copy()
artifacts = previous['project_import_artifacts'].copy()
for name in ['InitialWeightedCutoff', 'WeightedSpatialMoments']:
    e = read(ACTIVE / 'evidence/initial_weighted_20260910' / (name + '_ACCEPTED.json'))
    accepted[name] = {k: e[k] for k in ['source_sha256', 'artifact_sha256',
        'receipt', 'receipt_sha256', 'log', 'log_sha256']}
    artifacts['exp016/build/lib/lean/' + name + '.olean'] = e['artifact_sha256']
assert set(accepted) == set(task['accepted_active_modules'])
assert {p.stem for p in (ACTIVE / 'lean').glob('*.lean')} == set(accepted)
for name, e in accepted.items():
    assert sha(ACTIVE / 'lean' / (name + '.lean')) == e['source_sha256'], name
    assert sha(ACTIVE / 'build/lib/lean' / (name + '.olean')) == e['artifact_sha256'], name
    for kind in ['receipt', 'log']:
        assert sha(e[kind]) == e[kind + '_sha256'], (name, kind)
    r = read(e['receipt'])
    assert r['exit_code'] == 0, name
    assert r['source_sha256_before'] == r['source_sha256_after'] == e['source_sha256'], name
for rel, digest in artifacts.items():
    assert sha(ACTIVE.parent / rel) == digest, rel
sealed = 0
for name, e in read(ACTIVE / 'BASELINE.json')['experiments'].items():
    root = ACTIVE.parent / name
    for rel, digest in e['payload_sha256'].items():
        assert sha(root / rel) == digest, (name, rel)
        sealed += 1
    rp = root / 'evidence/FINAL_PACKET_RECEIPT.json'
    assert sha(rp) == e['final_packet_receipt_sha256']
    r = read(rp)
    assert sha(r['archive']) == r['archive_sha256'] == e['archive_sha256']
compiler = Path('/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean')
assert sha(compiler) == previous['compiler_sha256']
assert sha(ACTIVE / 'run_lean.py') == previous['runner_sha256']
mathlib = Path('/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages/mathlib')
mr = subprocess.run(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, capture_output=True)
assert mr.returncode == 0 and mr.stdout.strip() == previous['mathlib_commit']
checkpoint = read(RECOVERY / 'LATEST_CHECKPOINT.json')
assert sha(checkpoint['receipt']) == checkpoint['receipt_sha256']
verified = c.verify_archive(Path(checkpoint['archive']), checkpoint['archive_sha256'])
with zipfile.ZipFile(checkpoint['archive']) as z:
    for name, e in accepted.items():
        for p in [ACTIVE / 'lean' / (name + '.lean'), Path(e['receipt']), Path(e['log'])]:
            assert z.read(str(p.relative_to(RECOVERY.parent))) == p.read_bytes(), str(p)
    assert z.read('NDEA_Recovery/TASK_STATE.json') == (RECOVERY / 'TASK_STATE.json').read_bytes()
report = {
    'utc': c.utc(), 'passed': True, 'qualification': 'Byte reconciliation only; no accepted Lean check rerun.',
    'accepted_modules': accepted, 'project_import_artifacts': artifacts,
    'compiler_sha256': sha(compiler), 'runner_sha256': sha(ACTIVE / 'run_lean.py'),
    'mathlib_commit': mr.stdout.strip(), 'sealed_predecessor_payloads_unchanged': sealed,
    'checkpoint': checkpoint, 'archive_payloads_verified': verified['payload_files_verified'],
    'production_sources_without_acceptance': [],
    'latest_sealed_experiment': 'exp015', 'active_experiment_sealed': False,
    'new_work': 'Actual quadratic slab spatial estimate, then scheduled spatial refinement.',
    'validator_sha256': sha(__file__),
}
with (HERE / 'START_STATE.json').open('x') as f:
    f.write(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ['accepted_modules', 'project_import_artifacts']}, indent=2))
print('UNCHANGED:', len(accepted), 'accepted sources/receipts/logs/artifacts;', len(artifacts),
      'project imports;', sealed, 'sealed predecessor payloads plus packets.')
