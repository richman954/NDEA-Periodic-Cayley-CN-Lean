## Current Exp016 continuation — weighted sampled-potential control, September 10, 2026 UTC

Resume all 55 accepted development modules in TASK_STATE. AliasWeights and
WeightedSampledPotential passed the unchanged Lean 4.31.0/Mathlib environment
with 18 transitive standard-axiom reports, zero errors and one reviewed
deprecated-name warning. Read exp016/design/WEIGHTED_SPATIAL_MILESTONE.md and
exp016/evidence/WEIGHTED_SPATIAL_MILESTONE_LOCAL.json for exact source bindings.

The centered alias cannot increase absolute frequency or its weight. Actual
sampled multiplication by each fixed finite potential cutoff now satisfies
W_p(P_(V_R)y) <= K_(p,R,v)*W_p(y), with the original normalized DFT and no grid
factor or R<=M restriction. p=2 is the fourth weight. Grid states are arbitrary;
no invariant solution band or fourth moment for the full Exp014 class is assumed.

Next: actual A/Z weighted preservation using sealed Exp008's mode intertwiner,
then B weighted growth including the -Z term and actual denominator equation.
Propagate the ordered trajectory, derive the spatial moments/tails and discharge
refinement/approximation quantifiers. Read exp016/design/NEXT_SPATIAL_ROUTE.md.
The actual time-1 error certificate still retains its spatial sum; full solver
convergence, combined/fresh independent qualification and sealing are pending.

The original 53 accepted source/evidence/artifact bindings, 126 import artifacts
and sealed predecessors are preserved. The failed first alias attempt remains
separate rejected evidence. All Lean sessions have completed; only automatic
watcher session 27367 continues minute snapshots. No dependency pin, main or
sealed predecessor changed. Use dated local/Git readback receipts for exact
backup coverage; a new Git checkpoint follows the local milestone.
Historical entries below describe earlier accepted states and pending work.

## Current Exp016 continuation — actual temporal refinement, September 10, 2026 UTC

Resume all 53 accepted development modules in TASK_STATE. TemporalBudget and
TemporalRefinement passed the unchanged Lean 4.31.0/Mathlib environment with
24 transitive standard-axiom reports, zero warnings and zero errors.
Read exp016/design/TEMPORAL_MILESTONE.md and
exp016/evidence/TEMPORAL_MILESTONE_LOCAL.json for exact source/receipt bindings.

The actual temporal sum is bounded by rho*C(h,v)*sum(k_j^3), using concrete
A/B bounds and unitarity. On M=q+1, N=2M+1, h=2*pi/N, J=N^4, k=1/J, the actual
final time is exactly 1 and the temporal contribution tends to zero.
The actual time-1 PDE error is bounded by initialization error, a proved
vanishing temporal bound, and the unchanged computed spatial sum. The first
two terms together tend to zero; spatial refinement and solver convergence
remain unproved. Exp016 is unsealed, with full qualification still pending.

Next: prove the centered alias frequency/weight inequality, then a
mesh-independent weighted sampled-potential multiplication bound and actual
Cayley stage propagation for fixed Fourier cutoffs. Read
exp016/design/NEXT_SPATIAL_ROUTE.md. This is a proposed route; finite input
support does not imply an invariant solution band, and the full Exp014 class
is not silently strengthened to fourth moments.

All 51 prior accepted module bindings, 124 preexisting project artifacts and
789 sealed Exp013–015 payloads remain unchanged. The failed first refinement
attempt is preserved separately. No Lean or Colab proof job remains running.
Watcher session 27367 continues minute snapshots; it has no reboot autostart.
Use the latest dated manual checkpoint and Git readback receipt for exact
coverage. No dependency pin, main, or sealed predecessor was changed.
Git `342ca89e6ba9ca7e2073db8870e54674cef465fa` now protects the frozen
00:39:55 UTC temporal milestone on dev/variable-potential. Fresh readback matched
all 758 tree files and 53 source/receipt/log bindings. Main/archive heads remain
unchanged. Read NDEA_Recovery/github_evidence/EXP016_TEMPORAL_GIT_BINDING.json.
The watcher interval published at 00:43:07 UTC was verified with all 53 sources.
Only automatic watcher session 27367 remains running; all proof and Git jobs
have completed. The final dated manual checkpoint captures this later metadata.
Historical entries below record earlier milestones, not current pending work.

## Current Exp016 continuation — physical-grid kinetic assembly, September 10, 2026 UTC

51 source-bound development modules are accepted. KineticAssembly closes
`||op(sampledSplitA (2*M) h)|| <= 4/h^2+1` for `(2*M+1)*h=2*pi`, `h>0`.
The concrete sampled potential bound is also already accepted. Next substitute
both into the actual temporal certificate and prove the explicit temporal
budget tends to zero for the recorded N, h, J, k refinement family.

The next analytical barrier is evolved smooth-core spatial consistency/tails;
finite Fourier inputs and L2 stability alone do not close it. Reuse the accepted
paired continuum/numerical potential-cutoff comparison. Preserve quadratic
slabs, actual ordered recurrence, initialization mismatch and all defect terms.

Read exp016/design/KINETIC_ASSEMBLY_MILESTONE.md and the source-bound local receipt.
Two new standard-axiom reports passed with no warnings/errors. All 50 previous
accepted source/evidence/artifact bindings remain unchanged. Exp016 remains
unsealed; full combined/fresh independent qualification and convergence are pending.

The restart recovered the exact 1,298-payload checkpoint and all 789 sealed
Exp013–015 payloads. The watcher is producing minute snapshots after manual
restart. Latest dated checkpoint/Git readback receipts determine exact coverage.
The pinned external transfer already removes the continuum/DFT coefficient
identification gap and is consumed by WeightedCoefficientBridge. No further
upstream port is justified for the current barrier; Comparator was not run.
Git `a68a567cbef7a9d3ded041e565fe38d9697cd788` is fully read back: 740 tree
files and all 51 accepted source/receipt/log bindings match the frozen milestone.
Main/archive heads remain unchanged. Read EXP016_REBOOT_GIT_BINDING.json in
NDEA_Recovery/github_evidence; this is backup coverage, not proof qualification.
Historical milestone entries below are retained for continuity.

## Historical Exp016 continuation — continuum/cutoff transfer, September 9, 2026

Resume all 49 accepted source-matched development modules from TASK_STATE.
SpatialL2Operator, ContinuumPotentialStability and PotentialErrorTransfer are
new: exact residual (W-V)u_W, physical L2 conservation, coefficient-one
continuum potential comparison with arbitrary initial mismatch, and actual
ordered sampled-solver/PDE cutoff error transfer. For nonnegative steps at
actual grid time T, E_v<=E_cutoff+2T*sqrt(2*pi)||a||*tail_v(R), with the explicit
weighted tail bound W_v/(1+R)^2 and no grid-size factor or R<=M requirement.
The cutoff solver error remains an actual unresolved quantity, not an assumed
refinement result. No global variable-potential convergence is claimed.

Read exp016/design/CONTINUUM_MILESTONE.md and
exp016/evidence/CONTINUUM_MILESTONE_LOCAL.json. The three new accepted checks
have 11 standard-axiom reports, two style warnings and zero errors; all source,
import, artifact and received-evidence hashes match. Previous 46 source bytes
and all 789 sealed Exp013–015 payloads/packets remain unchanged. Exp016 remains
unsealed; combined/fresh-independent qualification and final gates are pending.
No compiler job remains running at this milestone.

Next: concrete induced kinetic bound ||A_h||<=4/h^2+1 and explicit temporal
refinement budget; then justified smooth-core spatial consistency/evolved tail
control. Finite potential support does not preserve finite solution support.
The unchanged pinned CPU runtime survived a proxy-binding expiry: same boot
and exact accepted archive checked after connection refresh, no proof rerun.
Local minute snapshots continued during that interruption. The manual milestone
archive passed all 49 source-byte checks. Dev commit c8b15ce8aecc27c2091ce17ab58c542021ec9438
is fresh-clone verified: all 709 tree files and 49 source/receipt bindings match.
Main and sealed archives remain unchanged. Git backup is distinct from proof qualification.

## Current Exp016 continuation — potential stability, September 9, 2026

Resume all46 accepted source-matched development modules in TASK_STATE. The four
new modules prove mesh-independent sampled block norms, generic ordered Cayley
potential perturbation, symmetric cutoff tail bounds and the actual sampled
trajectory/Fourier L2 consumer. Grid-time discrepancy is bounded by physical
initial mismatch plus total absolute step length times potential discrepancy
times the second initial physical norm. Exact samples yield the uniform
sqrt(2*pi)||a|| amplitude. Potential cutoff R gives tail T_v(R)<=W_v/(1+R)^2.
No R<=M restriction is needed. The actual A-half/B-full/A-half order is retained.

Read exp016/design/POTENTIAL_STABILITY_MILESTONE.md and its source-bound receipt
catalog. Four new checks passed with28 standard-axiom reports,4 retained harmless
style warnings and0 errors; source/import/log/artifact/transfer hashes match.
No compiler jobs remain running. Exp013–015 and earlier accepted sources remain
immutable. Exp016 is unsealed; combined/fresh independent qualification and
final gates remain pending. Grid-time stability does not assert the same bound
for quadratic paths between grid times or prove solver convergence.

Next: continuum two-potential L2 comparison from Exp015, then actual smooth-core
spatial consistency/evolved tail control. The concrete kinetic operator bound
is also still needed. Initial L2 stability alone does not control derivatives.
## Current Exp016 initialization milestone — September 9, 2026

Actual sampling/interpolation tail and weighted rate, uniform sampled initial
physical norm, arbitrary initialization perturbation and actual certificate
substitution are development-accepted. Exact-sample initialization convergence
is proved for expanding full odd grids; solver convergence remains open.
Read exp016/PLAN.md and evidence/INITIAL_SAMPLING_MILESTONE_LOCAL.json.
Next: explicit sampled potential/operator perturbation bounds, then numerical
evolved-tail/moment control or justified smooth-core uniform stability.
Exp016 remains unsealed; full combined/independent qualification is pending.

## Current Exp016 alias milestone — September 9, 2026

Actual potential-sampling alias formula, summability, full continuum discrepancy
low/high tail bound and weighted potential-tail estimate are development-accepted.
The actual ordered Cayley grid/partial certificate consumes these and the stencil
fourth-moment estimate. A nonzero five-node resolved-support control passes.
See exp016/PLAN.md for the single defect/refinement table and actual receipts in
exp016/evidence/ALIAS_MILESTONE_LOCAL.json. Exp016 remains unsealed.
Next: sampling/initialization and potential perturbation bridges, followed by
numerical evolved-tail/regularity or justified smooth-core uniform stability.
No mesh convergence or computable floating-point certification is claimed.

Current update 2026-09-09T13:53:12.412656+00:00: 30 Exp016 development modules accepted. See RESUME_STATUS and exact TASK_STATE receipts. Next: actual potential alias/tail control; independent qualification and refinement remain pending. Main/predecessors unchanged.

## Current Exp016 continuation — 2026-09-09T13:03:08.311527+00:00

Resume the accepted working state, not historical startup obligations below.
Exp013–015 are sealed and byte-unchanged. Exp016 remains UNSEALED, with full
isolated/independent qualification and refinement still pending.

Accepted development results now include actual sampled-potential finite and
partial-slab trajectory certificates, exact Fourier reconstruction/regularity/L2
normalization, and a nonzero cosine-potential control. FourierCoefficientBridge
also proves normalized continuum coefficient extraction for the actual DFT
reconstruction and off-band zero. Read the exact receipts listed in TASK_STATE.
No residual-vanishing or numerical convergence theorem is claimed.

The external release is pinned at 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538
outside NDEA. Compact manifests, ranked reuse decisions and Apache attribution
are in exp016/design/external_reference. Only a small proof-pattern adapter via
pinned Mathlib was adopted. No upstream build, Comparator or extra kernel ran.

Colab's existing VM/files were recovered after proxy loss; a cache-helper lock
required a Python-kernel reset. Readback preserved42 prior source/artifact files;
AddCircle cache artifacts matched local pins; the final new theorem check passed.
There are no pending compiler jobs. Failed and interrupted attempts are evidence,
not accepted results. Do not restart/bootstrap/rerun old work unnecessarily.

Git dev/variable-potential is freshly read back at
2288a4d6625c903efdbf38b968cc21f1f0103e7f through the accepted transfer and
sampled certificate: all489 files and22 source/receipt bindings matched.
Read TASK_STATE and EXP016_TRANSFER_GIT_BINDING.json for exact coverage.
Main and archival history are unchanged. The local minute watcher is producing
verified archives (559 payloads at13:01:47 UTC); it does not restart after reboot.

Next: expose separate stencil/potential alias defects and stronger ordered-stage
graph-norm bounds, then complete review/controls and the unchanged qualification
gates. Mesh-uniform refinement remains a separate explicit mathematical burden.

# Current experiment: Exp016

Exp016 is authorized and active. Its design comparison and proposed certificate
endpoint are recorded in exp016/PLAN.md and exp016/design/. Choose full odd-grid
Fourier synthesis/norm fidelity and quadratic reconstruction on time slabs,
with an immediate actual symmetric A-half/B-full/A-half Cayley consumer.
Five startup modules have local acceptance (39 public declarations): affine
regularity, ordered Cayley defects, spatial L2 rules, full odd-grid Fourier
inversion/periodicity, and quadratic time endpoint/derivative/residual identities.
No compiler jobs remain running. No Exp016 combined/independent
qualification or completion is claimed. Full spatial
aliasing/high-frequency/refinement convergence is the next natural boundary.
The active recovery watcher has been restarted and observed advancing.
Exp013–015 and their packets are immutable; main remains unchanged.

# Project goal and the current extension

## Current proof map and development architecture — September 9, 2026 UTC

The user explicitly reaffirmed the objective: a machine-checked guarantee that
the actual numerical method converges to the unique PDE solution, with explicit
assumptions and error bounds. The selection principle is **maximum useful
proof-space opened per rigorous, verifiable step**. Prefer shared bottleneck
lemmas and concrete reusable interfaces; require an actual intended consumer
and do not generalize beyond what the proof supports. Report each major
milestone as barrier removed, doors opened, best next move, next barrier and
recovery state. The terminal observability policy is preserved in
`../NDEA_Recovery/RECOVERY_POLICY.md`.

### Established foundation versus the active extension

- **Exp012 already closed a scoped numerical convergence chain.** The actual
  Exp011 grid reconstruction converges uniformly to the unique classical
  solution of the earlier two-component, constant-matrix-potential equation,
  under its stated weighted Fourier data, exact initialization and refinement
  schedule. This concerns the formal exact-arithmetic recurrence. It does not
  certify the roundoff or implementation semantics of arbitrary executable code.
- **Exp013 removed model-specific dependence of the energy/uniqueness proof.**
  It derives actual energy balance and uniqueness for classical solutions with
  arbitrary complex Hilbert fibers, positive periods, common space/time
  selfadjoint potentials and forcing. It supplies a reusable conditional PDE
  interface, not generic existence.
- **Exp014 removed the existence gap for a broader regular static potential
  class.** It constructs an infinite-mode global classical solution with
  second weighted absolute Fourier moments for both data and operator-valued
  potential, with Hermitian coefficient symmetry, on period 2*pi. Uniqueness
  compares all solutions in the specified classical class. Weighted
  convolution, Fourier synthesis, strong differentiation and all-real-time
  interaction-picture evolution are reusable infrastructure. Exp014 is sealed:
  143 audits passed locally and on a distinct fresh Colab runtime.
- **Exp015 removes the quantitative residual-to-error gap.** Its production
  modules have accepted exact-source modular receipts for the coefficient-one
  L2 estimate: error at t <= initial error + time integral of forcing difference
  (or actual PDE residual). It handles zero error and preserves initial mismatch.
  Generic forcing-difference continuity is explicitly global joint continuity;
  the bound is used on finite intervals. The Exp014 specialization retains its
  original assumptions. Exp015 is now sealed: all seven modules and 50 audits passed locally and
  independently; source freeze, review, transfer and finalizer gates passed.
  The accepted packet SHA-256 is
  b65a2f2c48c4a1c86e3dd32baff8f89a248916b82fd1c330b71634cb4ced9e71.

### Best next mathematical move, proposed rather than authorized new scope

Exp015 qualification is complete. The strongest well-supported next
candidate is a **reusable reconstruction and discrete-defect interface**,
with an immediate instance of the actual numerical recurrence. The existing
Exp011 piecewise-constant field does not satisfy Exp015 classical regularity;
one must construct a suitable regular comparison field and prove its relation
to the actual numerical output.

One previously constrained path is initialization: Exp011's uniform estimate
uses exact sampled initialization and an inverse grid-to-point norm estimate.
Exp015 preserves an arbitrary initial L2 mismatch. With a proved stable
reconstruction, this opens a route to inexact initialization in L2 without
assuming the older pointwise inverse-norm step. Uniform pointwise convergence
would still need additional control. A bridge from the current continuous-field
integral norm to Mathlib's L2 interfaces may support that shared norm/synthesis
infrastructure; establish its concrete consumer and feasibility before widening
the next experiment to a general weak-solution theory.

Use finite time slabs with globally defined polynomial time extensions and
smooth periodic spatial synthesis. Apply Exp015 on each slab, prove the needed
spatial L2 triangle inequality, and accumulate actual value jumps at interfaces.
Matching endpoint values remove those jump terms. Time-derivative jumps do not
need a distributional argument when estimates are applied slab by slab.

At the algebraic core, relate a discrete generator A_h, a synthesis S and the
continuum A=-partial_xx+V through the exact mismatch S A_h - A S. Separate the
actual time-stepping defect, spatial derivative mismatch, sampled-potential
product/aliasing mismatch and any certified solve defect. Preserve the precise
grid norm normalization, frequency convention and endpoint rules. A generic
defect premise alone is not the numerical theorem: derive it from the actual
Cayley/CN factors and ordering. The split Cayley recurrence is not automatically
the unsplit CN recurrence; its splitting defect must be proved and bounded.

Affine reconstruction is a realistic first exact identity. A quadratic
reconstruction may avoid an avoidable loss of temporal order. Prove its exact
identity before promising a second-order rate: such a rate still needs suitable
uniform higher graph norms/regularity. Do not silently infer those assumptions
from Exp014's second weighted absolute moment. First numerical instantiation
should retain the existing finite fiber (such as C^2); realizing an arbitrary
infinite-dimensional Hilbert fiber computationally needs a further approximation.

This move serves variable potentials, alternate reconstructions, nonuniform
time steps, inexact solves and later error certificates through a common
interface. It can reuse and potentially simplify earlier concrete proofs while
their original sealed versions remain unchanged. A broad nonlinear existence
theory would open a different branch but would leave this shared numerical
bottleneck in place. A one-off extra example has lower reuse value. A sweeping
weak-solution theory is premature when finite smooth slabs suffice.

### Remaining barriers and the next end-to-end threshold

The broader branch becomes end-to-end when a final Lean theorem starts from
the actual scheme/data/mesh definitions, constructs its reconstruction, proves
regularity and all defect bounds, identifies the unique Exp014 PDE solution,
and proves a stated total error bound tends to zero along an explicit refinement
schedule. Residual smallness must be derived, not supplied as the central
unproved assumption. L2 convergence is the natural first common norm; uniform
pointwise convergence needs further estimates and is not implied by L2 alone.

Beyond the exact recurrence, implemented numerical certificates need verified
linear-solve, arithmetic, quadrature, coefficient-tail and data-approximation
bounds, tied to actual stored output. Higher rates may require stronger explicit
regularity or a smoothing/density argument. Rough L2 data need a different
solution-space construction. Time-dependent potentials need an existence
extension even though the generic stability theorem already admits them.
Other boundaries require boundary-flux control; other PDEs require their own
energy/coercivity identities. Nonlinear equations require local or global
existence and nonlinear stability estimates, with possible blow-up limitations.
Higher dimension, long-time behavior and infinite fiber discretization each
have separate analytic and numerical obligations.

Realistic doors after the first broader theorem include regular scalar and
matrix-valued variable potentials; finite-difference, spectral or other schemes
with proved synthesis/defect adapters; adaptive and inexact solves; certified
run-specific errors; and more systematic extensions of the earlier examples.
These are prospects, not established results or automatic consequences.

### Verification and recovery are part of the proof infrastructure

Modular proofs localize failures and expose reusable APIs. Formal controls check
signs, coefficients, nonzero cases and necessary assumptions. Exact combined
source reconstruction and complete theorem catalogs bind checks to the intended
statement set. Fresh-runtime checks excluding project build artifacts reduce
stale-environment dependence. Source, compiler, dependency, log and transfer
hashes tie evidence together. Tested finalizer gates prevent partial or mismatched
evidence from being called sealed. The trusted Lean/compiler and compatible
library artifacts remain explicit; a second runtime is not a second proof logic
or a proof of compiler-source-to-binary correspondence.

Active recovery snapshots are verified local copies, not proof qualification.
The tracked watcher takes snapshots about every60seconds, for up to12hours,
with explicit saves before long work and after milestones. It is not a reboot
service. Sealed Exp001-015 packets complement the local snapshots. The watcher stopped
normally after capturing the Exp015 final receipt; explicit milestone saves
continue. Initial GitHub source and archive branches passed fresh remote
readback through Exp014 plus the historical Exp015 work-in-progress checkpoint.
The sealed Exp015 source/archive/development refresh passed readback. Consult the external
GitHub receipt for the exact uploaded-and-readback-verified generation. Local
minute snapshots do not automatically push to GitHub.

### Git/GitHub architecture — backup now authorized, preserve history

The connected account has an existing public repository,
`richman954/NDEA-Periodic-Cayley-CN-Lean`, whose main branch ends at the August30
milestone (commit15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c). It is a plausible
home for the continuing PDE line. The two additive backup branches now cover current source and exact archives;
read the GitHub backup receipt for the verified generation. Existing clean nested Exp002-005 local repositories contain
history worth preserving; do not reinitialize, flatten or force-push them.

Propose an additive branch based on the existing remote history, with explicit
history mappings for the nested predecessors. Preserve original path layout
and bytes initially so verifier hash/path assumptions remain reviewable. Track
Lean sources, exact-source generators, Python verification/finalization tools,
meaningful tests/controls, dependency/toolchain pins, roadmap and portable state,
recovery scripts and policy, compact release manifests and receipts. Separate
portable task status from ephemeral machine/session credentials and local paths.

Exclude compiled libraries/build caches, toolchains, virtual environments,
temporary uploads, duplicated full source bundles and frequent checkpoint ZIPs
from normal Git history. Keep full accepted logs/evidence and sealed packets as
release assets; they cannot be replaced by a manifest alone. Credentials,
authentication/session tokens, chat history and unrelated user data must not be
included. Do not sanitize a sealed packet in place: either its original contents
are appropriate for the chosen visibility or it remains private/local with an
explicit separately hashed derivative if needed.

Bind a clean source commit C to an external verification statement containing C,
the canonical source SHA-256 map, toolchain/dependency pins, actual accepted
result hashes, and final packet/manifest/receipt hashes. Do not try to embed a
commit's own hash inside itself. For legacy packets use an external migration
mapping that proves the imported source bytes match the old accepted source;
never rewrite or backdate the original receipts. Tag exp014-verified-v1 and
exp015-verified-v1 only at appropriate accepted source commits. Ordinary Git
tags are mutable; use protected rules and GitHub immutable releases where
enabled, with all assets attached before publication. GitHub's release
attestation can bind commit/tag/assets, but does not prove Lean acceptance.

After an authorized push/release, perform a fresh readback/clone and independently
verify source and asset hashes before recording off-device protection. Protection
then covers only uploaded and verified content. A clone does not include release
assets; preserve those separately alongside local Git bundles and recovery copies.
The user authorized this existing public repository as an additional destination.
Both backup branches have been published and read back; main remains unchanged.
The curated dev/variable-potential branch is published and readback-verified for Lean,
tooling, tests, pins, derivations and meaningful compact receipts. No verified
tag or GitHub release has been created. Existing historical notes below do not
override the current receipts.

Official documentation checked for this proposal:
[immutable releases](https://docs.github.com/en/code-security/concepts/supply-chain-security/immutable-releases),
[repository backups](https://docs.github.com/en/repositories/archiving-a-github-repository/backing-up-a-repository),
[large files](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github).

## Historical progression

This file records the working direction as of September 9, 2026 UTC. It is outside
the sealed experiment packets and can be revised when the user clarifies the
ultimate scope.

The clearest explicit historical goal is in
[NDEA_BREAK_STATUS_20260830.txt](../NDEA/NDEA_BREAK_STATUS_20260830.txt):
a kernel-checked consistency, stability and convergence chain for the periodic
one-dimensional spatial operator and Cayley/Crank–Nicolson time stepping.
The [lab notebook](../NDEA/NDEA_LAB_NOTEBOOK.txt) records completion of that
scoped finite periodic milestone. Experiments 006–012 are later extensions.

The Evolve experiment plans describe reusable audited noncommutative numerical
machinery. Experiments 007–010 now cover a concrete noncommuting spinor split,
finite and infinite Fourier references, growing-cutoff sampled convergence,
and classical derivatives under a second weighted absolute coefficient moment.
The [Experiment 010 report](exp010/COMPLETION_REPORT.md) states the exact
accepted scope and its independently verified evidence.

The working longer-term target for this PDE branch is an end-to-end statement
that the actual numerical fields converge to the continuous PDE solution in a
common function-space sense, with explicit data, mesh and step assumptions,
error estimates, and reproducible independent checks. This is a synthesis of
the saved plans, not a newly discovered frozen specification for all future
research.

Experiment 011 has completed that reconstruction milestone: the space-time
field from actual grid iterates converges uniformly to the classical solution
on `[0,1] × [0,2π]`, using exact sampled initialization and the existing proved
refinement schedule. All 44 new audits passed locally and on a distinct fresh
Colab VM; transferred evidence and the sealed review packet were verified.
Read the [completion report](exp011/COMPLETION_REPORT.md) and
[saved-file guide](exp011/SAVED_FILES.md).

Experiment 012 has now closed the classical uniqueness gap. Any two functions
in the unchanged classical periodic solution class that agree at one real
time agree for all real times and positions. The proof derives conserved
energy from the actual PDE and periodic boundaries, without assuming a
Fourier representation for the competing solution. For regular Fourier data,
there exists exactly one such solution, and the established reconstructed
numerical fields converge uniformly to it on the same closed rectangle.
All 46 new audits passed locally and on a distinct fresh Colab VM. See the
[completion report](exp012/COMPLETION_REPORT.md) and
[saved-file guide](exp012/SAVED_FILES.md).

The scoped PDE branch now connects construction, classical PDE validity,
uniqueness, and uniform numerical reconstruction. Variable spatial potentials,
weaker data classes, other boundaries, and sharper rates are further research
extensions. No additional theorem is needed to complete the accepted
Experiment 012 milestone. The local backup and restart arrangements are complete in
`/home/richman954/NDEA_Recovery/`; the user selected local Chromebook copies
and canceled Google Drive work. Experiment 013 now generalizes the energy
argument to arbitrary complex Hilbert fibers, positive periods, and space/time
Hermitian potentials, with an exact forcing-work balance and same-forcing
uniqueness. This provides a reusable analytic interface for later variable-
potential and residual-estimate work. Experiment 013 is complete: all 64 audits
passed locally and on a distinct fresh replacement Colab VM; the downloaded
evidence and sealed 313-payload packet were verified. Read
`exp013/COMPLETION_REPORT.md`. General variable-potential existence and
numerical convergence remain future extensions.

Older intake notes also mention a separate inverse-integrator mission. Its
complete frozen search, accuracy and resource specification was not located in
the bounded goal review. The user has been asked which branch should define
the ultimate endpoint; ordinary progress on the current PDE branch continues
while that clarification is pending.

## Experiment 014: global variable-potential existence

The user has now explicitly selected broader PDE existence as the next target.
Experiment 014 constructs a global classical solution of
`i u_t = -u_xx + V(x)u` on period `2*pi`, for arbitrary complex Hilbert fibers.
Initial coefficients and operator-valued potential coefficients have finite
second weighted absolute Fourier moments. Hermitian symmetry gives a
selfadjoint potential; Experiment 013 then supplies uniqueness among all
classical periodic solutions with the same initial field.

The construction retains infinitely many modes. A weighted Fourier Banach
space and an interaction-picture Dyson evolution avoid assuming operator-norm
continuity of the free Schrödinger group. The generic all-real-time evolution
and strong-operator product rule have passed their modular Lean checks. The
PDE synthesis, derivative closure, controls and final independent qualification
have passed; inspect `exp014/COMPLETION_REPORT.md` and actual evidence receipts.

This target closes existence for the stated regular linear periodic class.
Rough data, nonlinear equations, time-dependent potentials, and numerical
convergence for the enlarged class remain distinct extensions. Quantitative
forcing/residual stability remains a useful later bridge to numerical error.


## Experiment 014 complete; proposed bridge to variable-potential numerical convergence

Experiment 014 closes global classical existence and uniqueness for the regular
static variable-potential class described in its accepted report. This expands
the PDE reference class beyond the concrete spinor model of Experiments 010–012.
The historical finite periodic consistency/stability/convergence goal and the
later concrete reconstruction milestone remain complete. The broader working
goal is still to connect actual numerical iterates, reconstructed fields and
the unique PDE solution in a common function-space norm, under explicit data,
initialization, mesh and time-step assumptions.

The proposed next step is a reusable quantitative forcing/residual estimate
from Exp013's energy identity: control the L2 distance between classical
fields by their initial distance and the time integral of the L2 norm of their
forcing difference. Treat a sufficiently regular approximate field's PDE defect
as that forcing. Then adapt the preserved Cayley/Crank–Nicolson consistency and
stability machinery to the Exp014 variable-potential class, specifying the
spatial discretization and reconstruction, and prove that their residual and
initialization errors vanish under a stated refinement schedule. Any stronger
regularity needed for a claimed rate or uniform convergence must be established
explicitly. This is a proposed continuation; no new theorem, rate, convergence
result or follow-on experiment is claimed or started here.


## Active Experiment015 — quantitative forcing and residual stability

The user authorized this next milestone on 2026-09-09T02:25:54.274413+00:00.
Read `exp015/PLAN.md` and `exp015/MATHEMATICAL_DERIVATION.md` for the fixed
current scope. The target is a coefficient-one spatial L2 error bound with
full initial error, for classical periodic Hilbert-valued fields with a common
pointwise selfadjoint potential and jointly continuous forcing difference.
An actual-derivative residual interface and a specialization to Exp014
connect the estimate to the constructed regular variable-potential solution.
All seven module drafts are present; inspect actual module/combined receipts
before claiming their acceptance. ScalarSqrtEstimate, SpatialL2 and
ResidualField have passed; full endpoint/control and final independent
qualification are in progress. The later discrete reconstruction, consistency
and refinement argument has not been started by this milestone.

Authorization update: the user has approved backing up to the existing public
NDEA GitHub repository alongside local Chromebook copies. The earlier inspection-
only restriction above is superseded for this destination. Additive integration
and exact asset review are in progress; no verified remote backup receipt exists
yet. All seven Exp015 modules now pass separately (50newpublictheorems); final
combined/fresh-runtime qualification remains pending.
## Current Exp016 continuation — kinetic symbol/operator bound, September 9, 2026

KineticSymbolBound now proves the actual centered kinetic operator bound
`||op(gridKinetic)|| <= 4/h^2` by exact Fourier diagonalization and discrete
Parseval. The fixed Z factor remains an explicit triangle step for the planned
`||A_h|| <= 4/h^2 + 1` bound. Temporal constants can now be substituted with
their real mesh dependence. This does not control evolved fourth moments or
prove spatial consistency; those remain the principal refinement obstacle.
