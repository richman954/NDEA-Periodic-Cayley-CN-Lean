"""Update current notes only after both new modules have accepted receipts."""
import datetime
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ACTIVE = HERE.parents[1]
BASE = ACTIVE.parent
names = ['InitialWeightedCutoff', 'WeightedSpatialMoments']
records = [json.loads((HERE / (n + '_ACCEPTED.json')).read_text()) for n in names]
assert all(r['passed'] and r['compiler_exit'] == 0 and r['warnings'] == 0 for r in records)
assert sum(r['explicit_axiom_reports'] for r in records) == 19
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M UTC')

def replace_file(p, after):
    before = p.read_text()
    p.write_text(after)
    print(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
        fromfile=str(p) + ' (before)', tofile=str(p), n=2)))

p = ACTIVE / 'design/INITIAL_WEIGHTED_MILESTONE.md'
before = p.read_text()
assert before.count('Check status: pending. This draft is not evidence of acceptance.') == 1
status = ('Accepted ' + stamp + ': InitialWeightedCutoff and WeightedSpatialMoments.\n'
    'Exp016 now has 59 accepted development modules. The two successful checks\n'
    'have 19 transitive standard-axiom reports, zero warnings and zero errors.\n'
    'Exp016 remains unsealed; combined/fresh independent qualification is pending.')
after = before.replace('Check status: pending. This draft is not evidence of acceptance.', status)
after = after.replace('## Barrier removed by the proposed local statements', '## Barrier removed')
after = after.replace('the target is\n', 'the proved bound is\n')
table = '\n| Module | Source SHA-256 | Accepted receipt / seconds |\n|---|---|---|\n'
for r in records:
    table += '| ' + r['module'] + ' | `' + r['source_sha256'] + '` | [receipt](../evidence/' + Path(r['receipt']).name + '), ' + str(round(r['elapsed_seconds'], 3)) + ' |\n'
table += ('\nEvery public theorem has a transitive axiom report containing only propext,\n'
    'Classical.choice and Quot.sound; no accepted theorem uses sorryAx. The\n'
    '[local milestone receipt](../evidence/INITIAL_WEIGHTED_MILESTONE_LOCAL.json)\n'
    'binds both original checks and all 57 previous source/receipt/log/artifact\n'
    'bindings, 130 import artifacts and 789 sealed Exp013–015 payloads/packets.\n')
after = after.replace('The first InitialWeightedCutoff attempt omitted', table + '\nThe first InitialWeightedCutoff attempt omitted')
replace_file(p, after)

header = '''## Current Exp016 continuation — initial weights and spatial moments, September 10, 2026 UTC

Resume all 59 accepted development modules in TASK_STATE. InitialWeightedCutoff
and WeightedSpatialMoments passed the unchanged Lean 4.31.0/Mathlib pins with
19 transitive standard-axiom reports, zero warnings and zero errors. Read
exp016/design/INITIAL_WEIGHTED_MILESTONE.md and
exp016/evidence/INITIAL_WEIGHTED_MILESTONE_LOCAL.json for exact source bindings.

Actual samples of fixed finite Exp014 initial-data cutoffs now have a uniform
weighted DFT bound, without a grid-resolution hypothesis. The actual ordered
trajectory inherits a fixed bound for every prefix to time 1, eventually on
the saved schedule. The fourth l2 moment and low/high coefficient sums now
feed the existing complete stencil-plus-alias spatial budget. The endpoint
consumer retains its explicit spatial coefficient and original L2 constants.
No stronger regularity for the full Exp014 class or invariant band is assumed.

Next: bound the actual quadratic mean, velocity and generator-velocity in W_2;
substitute into sampledSpatialStageBudget, then prove the scalar spatial
coefficient and scheduledSpatialSum vanish. The baseline approximation
quantifiers, between-grid-time transfer and full qualification remain pending.
Exp016 is unsealed. Read exp016/design/NEXT_SPATIAL_ROUTE.md.

All 57 earlier accepted bindings, 130 existing import artifacts and 789 sealed
Exp013–015 payloads/packet hashes remain unchanged. The first initial-cutoff
attempt is preserved separately as rejected evidence; no theorem assumption
was changed to repair it. All Lean checks completed. Only watcher session
27367 continues minute snapshots, without reboot autostart. Main and pins
remain unchanged. New Git coverage is pending readback; the prior 57-module
coverage at ba14346ad7d391487630ec9d4fef46f7df211485 remains verified.
Historical entries below describe earlier states and then-pending work.

'''
for name in ['RESUME_STATUS.md', 'WORKING_ROADMAP.md']:
    p = BASE / name
    assert not p.read_text().startswith(header.splitlines()[0])
    replace_file(p, header + p.read_text())

p = ACTIVE / 'PLAN.md'
old = p.read_text(); a = old.index('Current continuation ('); b = old.index('## Chosen architecture', a)
new = ('Current continuation (' + stamp + '''): 59 accepted development modules.
InitialWeightedCutoff supplies an actual finite-cutoff initial weighted bound
and its scheduled numerical trajectory consumer. WeightedSpatialMoments bounds
the fourth moment, low/high sums and actual spatial-defect budget by W_2,
retaining an explicit scalar coefficient. Both passed 19 standard-axiom reports
with no warnings or errors. Read design/INITIAL_WEIGHTED_MILESTONE.md.
Next: the actual quadratic mean/velocity/generator-velocity spatial estimates,
then scalar-coefficient and scheduledSpatialSum vanishing; see
design/NEXT_SPATIAL_ROUTE.md. No Lean job remains. Exp016 is unsealed;
approximation quantifiers, full qualification and solver convergence are pending.

''')
replace_file(p, old[:a] + new + old[b:])

p = ACTIVE / 'NEXT_STEPS.md'
replace_file(p, '''# Exp016 continuation after initial weights and spatial moments

Resume 59 accepted development modules. Preserve all source/receipt bindings,
Exp013–015, main and dependency pins. PLAN.md retains the actual reconstruction,
ordered recurrence and qualification gates. Read INITIAL_WEIGHTED_MILESTONE.md
in design/ and its exact local receipt. The two new successful checks have
19 standard-axiom reports, zero warnings and zero errors. The failed first
initial-cutoff attempt remains separate rejected evidence.

Actual samples of fixed finite initial cutoffs have a grid-independent W_p
bound, which feeds the ordered trajectory propagation theorem. Fourth l2
moments and low/high l1 sums now control the existing complete spatial-defect
budget, with a consumer at every actual trajectory endpoint to time 1.

1. Bound the actual quadratic mean, velocity and generator-velocity in W_2.
   Use the accepted triangle/scalar properties and actual kinetic coefficient
   bound; retain all h-dependent constants. Substitute into the existing
   sampledSpatialStageBudget, including k/2 and k^2/8 exactly.
2. Prove the explicit spatial scalar coefficient tends to zero, for example
   using low cutoff floor(M/2), and control k*h^(-2) on the saved schedule.
   Sum the actual slab bounds to prove scheduledSpatialSum vanishing for each
   fixed initial-data/potential cutoff. Then discharge the baseline approximation
   quantifiers with the accepted stability/initialization machinery.
3. Complete statement/dependency review, required controls, isolated combined
   and fresh independent qualification, transfer validation and sealing gates.

Quadratic between-grid-time transfer/refinement remains separate. The endpoint
budget estimate is not a proof of solver convergence; no spatial term may be
removed or assumed to vanish. Exp014's original data class remains unchanged.

No Lean job remains running. Verify advancing watcher snapshots and keep manual
milestone checkpoints. Use dev/variable-potential for reviewed curated backups
with actual remote readback. Google Drive remains canceled.
''')

p = ACTIVE / 'design/NEXT_SPATIAL_ROUTE.md'
replace_file(p, '''# Next spatial obligation: actual quadratic slab estimates

Current accepted state: 59 development modules. InitialWeightedCutoff and
WeightedSpatialMoments close the finite initial weighted bound and the fourth
moment/tail-to-spatial-budget bridge. Read INITIAL_WEIGHTED_MILESTONE.md and
its source-bound receipt. All previous numerical and continuum definitions,
sealed predecessors, pins and qualification gates are preserved.

## Accepted inputs and immediate consumer

For each fixed initial-data and Hermitian potential cutoff, actual samples
initialize an actual ordered Cayley trajectory whose W_2 is uniformly bounded
at every prefix to time 1, eventually on the saved schedule. The complete
sampledSpatialDefectBudget at an arbitrary grid state y is at most C_sp*W_2(y),
where the explicit spatialFourthWeightCoefficient is

`sqrt(2*pi)*h^2 + 2*sqrt(2*pi)*(T_v(M-L)+A_v/(1+L)^4)`.

The physical mesh, full normalized complex-spinor DFT, strict tail and inclusive
low cutoff L<=M are unchanged. The initial cutoff need not be resolved by M.
Higher initial moments are finite only after the explicit cutoff.

## Recommended next proof

The remaining actual sampledSpatialStageBudget in TemporalBudget.lean is
`B_sp(mean)+(k/2)*B_sp(velocity)+(k^2/8)*B_sp(G*velocity)`.
Here mean=(y+y3)/2, velocity=(y3-y)/k, and G=op A+op B for the actual ordered
endpoint y3. Keep k>0 explicit and use the accepted weighted triangle/scalar
identities to bound W_2(mean) and k*W_2(velocity) by the endpoint weights.

For G, KineticSymbolBound.fourierCoefficient_gridKinetic_norm_le already gives
the actual kinetic coefficient bound 4/h^2. Sum it against the nonnegative
weights and combine with WeightedSampledPotential's finite-cutoff bound.
SampledPotential.sampledSplit_sum proves cancellation of the actual Z terms:
the sum is gridKinetic plus sampledBlock of V_R. This should yield the explicit
weighted G bound 4/h^2+K_V, without proving a new surrogate operator estimate.

Substituting these bounds should give
`B_stage <= C_sp*(1+k*K_G/8)*(W_2(y)+W_2(y3))`.
This is a proposed next theorem, not an accepted estimate. Then consume the
accepted uniform endpoint bound and the actual sum of step sizes, exactly 1.
This route reuses the existing certificate and requires no extra smooth gluing
or stronger continuum regularity theorem.

## Refinement and next barrier

Choose, for example, L=floor(M/2), and prove L and M-L tend to infinity.
The accepted potential tail estimate uses exactly the original second moment;
it controls T_v(M-L). Prove C_sp tends to zero and k*K_G remains controlled
on M=q+1, h=2*pi/(2M+1), J=(2M+1)^4, k=1/J. Then prove the actual
scheduledSpatialSum tends to zero for fixed cutoffs and feed scheduledCayley_error_le.

Only after this smooth-cutoff convergence proof can the baseline theorem's
potential and initial-data approximation quantifiers be discharged. Finite
potential support does not imply an invariant solution band. Temporal or
endpoint spatial estimates alone are not full solver convergence. Quadratic
between-grid-time transfer and full independent qualification remain separate.
''')
