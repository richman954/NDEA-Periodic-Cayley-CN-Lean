"""Bind the accepted weighted Cayley milestone and update its recovery state."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ACTIVE = HERE.parents[1]
RECOVERY = Path('/home/richman954/NDEA_Recovery')
read = lambda p: json.loads(Path(p).read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
start = read(HERE / 'START_STATE.json')
modules = {}
for name in ['WeightedGridStages', 'WeightedCayleyPropagation']:
    p = HERE / (name + '_ACCEPTED.json')
    e = read(p)
    assert e['passed'] and e['compiler_exit'] == 0 and e['errors'] == 0
    for kind in ['source', 'artifact', 'receipt', 'log']:
        assert sha(e[kind]) == e[kind + '_sha256'], (name, kind)
    modules[name] = {**e, 'acceptance_wrapper': str(p), 'acceptance_wrapper_sha256': sha(p)}
for name, e in start['accepted_modules'].items():
    for kind in ['receipt', 'log']:
        assert sha(e[kind]) == e[kind + '_sha256'], (name, kind)
    assert sha(ACTIVE / 'lean' / (name + '.lean')) == e['source_sha256'], name
    assert sha(ACTIVE / 'build/lib/lean' / (name + '.olean')) == e['artifact_sha256'], name
for rel, digest in start['project_import_artifacts'].items():
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
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
s = read(RECOVERY / 'TASK_STATE.json')
assert len(s['accepted_active_modules']) == 57
assert set(s['accepted_active_modules']) == set(start['accepted_modules']) | set(modules)
next_step = ('Prove a mesh-independent initial W_2 bound for actual samples of fixed finite '
    'Exp014 initial-data cutoffs; feed scheduledCayley_cutoff_fourierWeightedNorm_eventually_le, '
    'then derive actual fourth moments/tails and scheduledSpatialSum vanishing.')
utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
report = {
    'utc': utc, 'passed': True, 'modules': modules, 'accepted_module_count': 57,
    'new_axiom_reports': sum(e['explicit_axiom_reports'] for e in modules.values()),
    'standard_axioms_only': True, 'warnings': 2, 'errors': 0,
    'warning_scope': 'One deprecated alias and one tactic-style linter; exact accepted sources retained.',
    'previous_accepted_modules_unchanged': len(start['accepted_modules']),
    'preexisting_import_artifacts_unchanged': len(start['project_import_artifacts']),
    'sealed_predecessor_payloads_unchanged': sealed,
    'actual_A_weighted_preservation_proved': True,
    'actual_B_weighted_bound_includes_minus_Z': True,
    'actual_weighted_cayley_propagation_proved': True,
    'eventual_schedule_step_restriction_proved': True,
    'all_actual_prefixes_up_to_time_one_proved': True,
    'growth_bound': 'W_p(y_j) <= exp(2*K_B*sum_{i<j}|k_i|)*W_p(y_0), with |k_i|*K_B<=1.',
    'scope': 'Fixed finite Hermitian potential cutoff; original normalized complex-spinor DFT. Arbitrary initial grid family; its weighted amplitude is explicit. No R<=M or invariant solution band assumption.',
    'uniform_initial_weighted_bound_proved': False,
    'spatial_sum_vanishing_proved': False, 'solver_convergence_proved': False,
    'combined_qualification': False, 'fresh_independent_qualification': False,
    'comparator_run': False, 'additional_independent_kernel_run': False, 'sealed': False,
    'failed_attempts_this_milestone': [],
    'validator': str(HERE / 'record_module.py'), 'validator_sha256': sha(HERE / 'record_module.py'),
    'milestone_validator': str(Path(__file__)), 'milestone_validator_sha256': sha(__file__),
    'design': str(ACTIVE / 'design/WEIGHTED_CAYLEY_MILESTONE.md'),
    'design_sha256': sha(ACTIVE / 'design/WEIGHTED_CAYLEY_MILESTONE.md'),
    'next_step': next_step,
}
target = ACTIVE / 'evidence/WEIGHTED_CAYLEY_MILESTONE_LOCAL.json'
with target.open('xb') as f:
    f.write(c.json_bytes(report))
s['latest_development_milestone'] = str(target)
s['next_mathematical_consumer'] = next_step
s['continuum_milestone']['next_obligation'] = next_step
s['remaining_steps'] = [next_step,
    'Discharge the baseline potential/initial-data approximation quantifiers with accepted stability. Quadratic partial-slab transfer/refinement remains separate.',
    'Complete final statement/dependency review and controls, isolated combined and fresh independent qualification, transfer validation and finalizer/sealing gates.']
s['recovery']['current_check'] = {'status': 'Both weighted Cayley modules passed; no Lean job remains running.',
    'receipt': str(target), 'receipt_sha256': sha(target), 'pending_module': None}
s['recovery']['qualification'] = ('57 accepted development modules. Actual weighted Cayley propagation '
    'and eventual schedule restrictions proved; 23 new standard-axiom reports, two reviewed warnings, '
    'zero errors. Uniform initial weighted bounds, spatial refinement and full qualification remain open.')
s['recovery']['current_durable_off_device_backup_verified'] = False
s['continuation']['current_status'] = s['recovery']['qualification']
s['continuation']['utc'] = utc
s['updated_utc'] = utc
c.atomic_bytes(RECOVERY / 'TASK_STATE.json', c.json_bytes(s))
print(json.dumps({k: v for k, v in report.items() if k != 'modules'}, indent=2))
