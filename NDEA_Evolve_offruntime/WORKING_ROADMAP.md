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
  original assumptions. Exp015 remains unsealed until controls, source freeze,
  review, local combined and fresh-runtime combined checks, evidence transfer
  and finalizer gates all pass. Read current receipts for changing control status.

### Best next mathematical move, proposed rather than authorized new scope

Finish Exp015 qualification first. Then the strongest well-supported next
candidate is a **reusable reconstruction and discrete-defect interface**,
with an immediate instance of the actual numerical recurrence. The existing
Exp011 piecewise-constant field does not satisfy Exp015 classical regularity;
one must construct a suitable regular comparison field and prove its relation
to the actual numerical output.

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
service. Sealed Exp001-014 packets and the latest verified Downloads milestone
copy complement the active Exp015 snapshots. Neither a local duplicate nor a
temporary Colab copy supplies durable device-loss protection. At this review,
current progress has no verified durable off-device backup.

### Git/GitHub architecture — backup now authorized, preserve history

The connected account has an existing public repository,
`richman954/NDEA-Periodic-Cayley-CN-Lean`, whose main branch ends at the August30
milestone (commit15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c). It is a plausible
home for the continuing PDE line. Current Exp006-015 and recovery files are not
covered there. Existing clean nested Exp002-005 local repositories contain
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
No Git commits, pushes, repository restructuring or releases were performed in
this inspection. Because the current repository is public, publication/visibility
must be explicitly settled before uploading current project files.

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
