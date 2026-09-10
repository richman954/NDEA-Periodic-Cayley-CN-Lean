"""Bind the three accepted spatial-refinement modules and refresh continuation."""
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ACTIVE = HERE.parents[1]
RECOVERY = Path('/home/richman954/NDEA_Recovery')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
task = read(RECOVERY / 'TASK_STATE.json')
assert len(task['accepted_active_modules']) == 62
start = read(ACTIVE / 'evidence/recovery_20260910T0220/START_STATE.json')
modules = {}
for name in ['WeightedSlabSpatialBudget', 'SpatialScalarRefinement', 'SmoothCutoffConvergence']:
    wp = HERE / (name + '_ACCEPTED.json')
    e = read(wp)
    assert e['passed'] and e['compiler_exit'] == 0 and not e['warnings']
    for kind in ['source', 'artifact', 'receipt', 'log']:
        p = Path(e[kind])
        p = p if p.is_absolute() else ACTIVE / p
        assert sha(p) == e[kind + '_sha256']
        e[kind] = str(p)
    modules[name] = {**e, 'original_acceptance_wrapper': str(wp), 'original_acceptance_wrapper_sha256': sha(wp)}
for name, e in start['accepted_modules'].items():
    assert sha(ACTIVE / 'lean' / (name + '.lean')) == e['source_sha256'], name
    assert sha(ACTIVE / 'build/lib/lean' / (name + '.olean')) == e['artifact_sha256'], name
    for kind in ['receipt', 'log']:
        assert sha(e[kind]) == e[kind + '_sha256'], (name, kind)
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
next_step = ('Check InitialErrorTransfer, then BaselineTimeOneConvergence. Continue the explicit '
    'finite-horizon schedule, complete spatial/prefix certificate and finite maximum grid-time '
    'error theorem. All are preserved drafts; retain the original target and qualification gates.')
report = {'utc': c.utc(), 'passed': True, 'accepted_module_count': 62, 'modules': modules,
    'new_production_axiom_reports': 17, 'successful_small_probe_reports': 2,
    'standard_axioms_only': True, 'errors': 0, 'warnings': 0,
    'recovered_accepted_bindings_unchanged': 59, 'recovered_import_artifacts_unchanged': 132,
    'sealed_predecessor_payloads_unchanged': sealed,
    'actual_quadratic_slab_spatial_bound': True, 'actual_scheduled_spatial_sum_vanishing': True,
    'actual_fixed_double_cutoff_time_one_solver_convergence': True,
    'original_data_approximation_quantifiers_discharged': False,
    'uniform_grid_time_convergence': False, 'all_fixed_finite_horizons_proved': False,
    'continuous_time_reconstruction_convergence': False,
    'combined_qualification': False, 'fresh_independent_qualification': False,
    'comparator_run': False, 'additional_independent_kernel_run': False, 'sealed': False,
    'scope': 'Actual odd-grid samples and ordered A-half/B-full/A-half iterates; fixed finite initial and Hermitian potential cutoffs; exact time 1. No extra regularity for the original Exp014 class or assumed residual-smallness.',
    'next_step': next_step, 'validator': str(Path(__file__)), 'validator_sha256': sha(__file__),
    'rejected_attempts': ['attempts/weighted_slab_spatial_r1', 'attempts/spatial_scalar_refinement_r1', 'attempts/smooth_cutoff_convergence_r1'],
    'recovery_incident': 'Unsupported .diff review filename rejected by checkpoint guard; bytes preserved as .diff.txt; watcher 27367 stopped and 9546 restarted with verified advancing snapshots.',
}
rp = ACTIVE / 'evidence/SPATIAL_REFINEMENT_MILESTONE_LOCAL.json'
with rp.open('x') as f:
    f.write(json.dumps(report, indent=2) + '\n')
body = '''# Actual spatial residual refinement — September 10, 2026 KST

62 Exp016 modules are development-accepted. WeightedSlabSpatialBudget,
SpatialScalarRefinement and SmoothCutoffConvergence passed 17 transitive
standard-axiom reports, with zero warnings/errors. The exact receipt is
../evidence/SPATIAL_REFINEMENT_MILESTONE_LOCAL.json. Two small normalization
probes passed separately. No combined or fresh independent qualification,
Comparator acceptance, additional kernel check or sealing is claimed.

The actual quadratic mean, velocity and generator-velocity now feed the
complete spatial budget:
`B_slab <= C_sp*(1+k*K_G/8)*(W_2(y_j)+W_2(y_{j+1}))`,
where `K_G=4/h^2+K_V`; the accepted actual generator decomposition cancels Z.
The sum uses every actual ordered step to time 1. With L=floor(M/2), both
cutoffs expand, the potential tails vanish under the original second-moment
condition, and k*K_G tends to zero on J=N^4. These estimates prove the actual
scheduledSpatialSum vanishes for each fixed initial/potential cutoff. The
existing Exp015/Exp014 certificate then proves actual solver convergence at
exact time 1 for those fixed approximants.

The missing spatial-residual limit for the smooth approximants is removed.
The next consumer is the initial-data stability transfer: actual samples of
a-a_S have a physical norm controlled by the omitted Fourier tail, and the
existing numerical/continuum stability estimates transfer the error. Then
remove the potential cutoff. Those approximation quantifiers remain drafts.
The finite-horizon k=T/J schedule and maximum error over all grid times are
also drafted in dependency order, with T fixed before the refinement limit.
Continuous-time quadratic reconstruction refinement remains separate.

No invariant finite solution band, stronger original-data regularity, free
residual-smallness field, easier recurrence, or changed norm is used. The
original 59 accepted bindings, 132 imported artifacts and 789 sealed Exp013–015
payloads/packet hashes remain unchanged. Rejected drafts and full logs remain
under attempts/; they are not production acceptance. Main and pins are intact.

Watcher 9546 now produces verified advancing minute snapshots. A review diff
briefly stopped watcher 27367 because .diff was not an allowed Git-evidence
suffix; the bytes are preserved as .diff.txt without changing checkpoint policy.
Read WATCHER_STOP_0251.json, WATCHER_RESTART_0254.json and
WATCHER_ADVANCING_0258.json in evidence/spatial_refinement_20260910.
All new accepted work and further drafts are local until curated Git readback.
'''
(ACTIVE / 'design/SPATIAL_REFINEMENT_MILESTONE.md').write_text(body)
report['design'] = str(ACTIVE / 'design/SPATIAL_REFINEMENT_MILESTONE.md')
# The sealed-style receipt above is not rewritten; design and receipt are linked by current task state.
task['latest_development_milestone'] = str(rp)
task['next_mathematical_consumer'] = next_step
task['continuum_milestone']['next_obligation'] = next_step
task['remaining_steps'] = [next_step, 'Review/control and qualify the complete target: isolated combined and fresh independent runtime, transfers/finalizer/sealing.', 'Continuous-time reconstruction refinement and executable bounds remain explicitly separate.']
task['blocker_ledger'][1].update({'status': 'resolved for fixed cutoffs at time 1 by accepted actual spatial-sum and solver-error consumers', 'acceptance': str(rp)})
task['blocker_ledger'][2]['next_attack'] = next_step
task['draft_sources'] = [str(p.relative_to(ACTIVE)) for p in sorted((ACTIVE / 'lean').glob('*.lean')) if p.stem not in task['accepted_active_modules']]
task['recovery']['qualification'] = '62 modular development acceptances; actual fixed-cutoff spatial residual and time-1 solver convergence proved. Approximation/uniform horizon drafts and full qualification pending; unsealed.'
task['recovery']['current_check'] = {'status': 'three spatial-refinement modules accepted; next initial-data transfer check', 'receipt': str(rp), 'receipt_sha256': sha(rp)}
task['recovery']['current_durable_off_device_backup_verified'] = False
task['continuation']['current_status'] = task['recovery']['qualification']
task['continuation']['utc'] = c.utc()
task['updated_utc'] = c.utc()
c.atomic_bytes(RECOVERY / 'TASK_STATE.json', c.json_bytes(task))
header = ('Current frontier (2026-09-10 KST): 62 development-accepted Exp016 modules. '
    'The complete actual spatial residual sum and actual fixed-cutoff time-1 solver error now tend to zero. '
    'Read exp016/design/SPATIAL_REFINEMENT_MILESTONE.md and its original source-bound receipts. '
    'Initial-data/potential approximation and uniform finite-horizon grid-time convergence are preserved drafts. '
    'Exp016 is unsealed. TASK_STATE.json identifies current jobs; watcher 9546 is advancing.\n\n')
diffs = []
for fn in ['RESUME_STATUS.md', 'WORKING_ROADMAP.md']:
    p = ACTIVE.parent / fn
    old = p.read_text()
    new = header + old[old.index('\n\n') + 2:]
    p.write_text(new)
    diffs.extend(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=str(p)+' before', tofile=str(p), n=1))
p = ACTIVE / 'PLAN.md'
old = p.read_text()
a, b = old.index('Current continuation ('), old.index('## Chosen architecture')
new = old[:a] + header + next_step + '\n\n' + old[b:]
p.write_text(new)
diffs.extend(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=str(p)+' before', tofile=str(p), n=1))
for fn in ['NEXT_STEPS.md', 'design/NEXT_SPATIAL_ROUTE.md', 'design/CURRENT_SPATIAL_DRIVE.md']:
    p = ACTIVE / fn
    old = p.read_text()
    new = '# Current Exp016 continuation\n\n' + header + next_step + '''

Read design/SPATIAL_REFINEMENT_MILESTONE.md for accepted scope and the exact
local receipt. Current accepted/draft lists and live jobs are in TASK_STATE.
The initial-data transfer uses existing stability with zero potential
difference, then removes the actual omitted coefficient tail. Preserve the
order: fix an approximant, refine the grid, remove the approximation.

The full target is every fixed T>0 and the finite maximum over all actual
grid times. FiniteHorizonSchedule/Spatial/Certificate and
UniformGridTimeConvergence are drafts for that target. The earlier time-1
prefix sketch is preserved under design/alternatives and is not imported.
Continuous-time quadratic reconstruction, independent reviews/controls,
combined/fresh independent qualification, transfer and finalizer gates remain
explicit. Do not change sealed predecessors, main, pins or accepted sources.
Watcher 9546 is verified advancing; no reboot autostart exists. Local manual
checkpoints and curated dev/variable-potential backups protect milestones.
'''
    p.write_text(new)
    diffs.extend(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=str(p)+' before', tofile=str(p), n=1))
(HERE / 'MILESTONE_NOTES.diff.txt').write_text(''.join(diffs))
print(json.dumps({k: v for k, v in report.items() if k != 'modules'}, indent=2))
print('Receipt SHA-256:', sha(rp))
print('Full mutable note diffs:', HERE / 'MILESTONE_NOTES.diff.txt')
