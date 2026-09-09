# Experiment 009 mathematical and verification review

The reviewed error argument has no blocking mathematical scope issue. It
compares the actual full-grid Cayley trajectory with the complete absolutely
summable Fourier reference, and retains both endpoint truncation errors.
Local and fresh independent combined checks passed all 70 public audits.
The receiving check accepted all 91 evidence-file hashes, 9,868 matching
library artifacts, six bootstrap input files, and 57 completed bootstrap
commands. The compiler and transfer receipts are the underlying acceptance
evidence; this review does not replace them.

## Mathematical scope

`InfiniteReference.lean` uses `Summable (fun m => norm (a m))` to construct the
vector-valued Fourier sums. Norm preservation of every continuum mode gives
summability at every time and position. Continuous coordinate projections
identify the grid sum with samples of that reference. The tail estimate uses
the triangle inequality and the norm of each sampled mode. It remains valid
for aliased frequencies and uses no infinite discrete Parseval identity.

`InfiniteClosure.lean` bounds the final full-reference error by a finite-band
error plus the terminal sample tail. The finite-band initial discrepancy is
bounded by the entire initial discrepancy from the full reference plus the
initial sample tail. Thus the coefficient `2` multiplying the tail is required
by this argument. The finite-band coefficient l2 norm is bounded by the total
coefficient l1 mass. Arbitrary initial grid vectors remain allowed, and zero
steps retain their entire initial error. The argument assumes the band and
step restrictions of the already verified finite-band theorem.

The general convergence endpoint requires the cutoff to tend to infinity,
the frequency-dependent consistency budget to tend to zero, and the full
initial error to tend to zero. It does not silently hold the cutoff-dependent
constants fixed. `CutoffSchedule.lean` supplies a concrete admissible schedule:
with `M=q+1`, grid size `8M^3`, step count `6M^4`, and step `1/(6M^4)`, the
terminal time is exactly one and the consistency budget tends to zero.
`ScheduleClosure.lean` applies that schedule both to arbitrary convergent
initialization and to exact full sampled initialization.

`WeightedTail.lean` and `WeightedClosure.lean` replace the tail by a bound from
a summable natural-order weighted coefficient moment. The denominator is
positive, and the nonnegative factors are retained when this estimate is
inserted in the global error bound.

The infinite reference is a Fourier evolution for the same constant,
noncommuting spinor split as Experiment 008. These files do not prove
classical time and second-space differentiability of the infinite series
under the sole l1 assumption. They do not address spatially varying potentials
that mix Fourier frequencies, interpolation convergence, or convergence
from general l2 data without a sampling hypothesis.

## Controls and diagnostics

The exact control datum in `Controls.lean` has coefficient
`(1/2)^encode(m)` times an existing unit spinor. Its norm sum is summable by
the injective encoding form of the geometric-series theorem, and every
integer coefficient is nonzero. The support is therefore infinite; each
finite-cutoff tail is positive while these tails tend to zero. This makes
the infinite-support class concrete without identifying it with the
separate numerical datum.

The complete `Controls.lean` module passed its first full local elaboration:
exit 0, 112.561 seconds, ten public declarations, and source unchanged.
The receipt is `evidence/20260908T090807.153691Z_Controls.json` and its checked
source SHA-256 is
`1bd7122751b4ba8ceb36a55e3d66bba7b552959ab631d4d0d7e73f9d7a2bce54`.
The earlier isolated geometric-series probe also passed and is retained as
development evidence. All ten controls are included in the 70 declarations
audited successfully in both final combined checks.

The coherent-alias control uses two equal coefficients at frequencies `d`
and `2d`. These sample as the constant mode, producing strictly more sampled
energy than the naive coefficient l2 formula predicts. Both frequencies
lie above every cutoff smaller than `d`. This complements the cancellation
control retained from Experiment 008.

The floating-point script uses a different, genuinely infinite signed
geometric datum with both spinor components active. It evaluates the full
initial sample by closed geometric alias sums and records an analytic bound
on the omitted terminal-reference tail. This is a truncation bound in exact
arithmetic, not a floating-point interval certificate. All twelve trajectory
cases, twelve endpoint-tail checks, two wrapped-grid cases, and three aliasing
cases passed locally. See `NUMERICAL_DIAGNOSTICS.md` for the interpretation of
the refinement orders and `evidence/numerical_checks.json` for the data.

## Verification design

The bounded review covered `make_combined.py`, `verify_combined.py`,
`remote_check/start_final.py`, `remote_check/export_evidence.py`,
`remote_check/check_download.py`, and `check_predecessors.py`.

The combined generator pins the entire Experiment 008 foundation by its
accepted SHA-256, explicitly lists the seven new modules, removes project
imports, and emits public axiom audits from the new source declarations.
Independent inventory using the policy scanner's comment-stripped source
agreed with its catalog: 18/8/22/7/1/4/10 declarations in the seven modules,
70 total at review time. The inventory includes helpers and controls; it is
not a count of 70 independent mathematical endpoints. The declaration
collector is tailored to the formatting of these current files and is not
a general Lean parser.

The shared `Controls.lean` basename does not contaminate the final check:
the combined source re-elaborates the frozen foundation and all new source
bodies, and the new declarations use `NDEAEvolve.Exp009.Controls`. Its import
path contains only copied external-library artifacts and the compiler's core
library. The generator permits project imports only from the listed modules
and the explicitly embedded foundation coverage.

The combined checker reconstructs exact source bytes and the complete input
catalog, pins compiler/checker/dependency-walker hashes, verifies library
source revisions, records the copied dependency artifact map, checks every
expected axiom declaration against the compiler log, and compares source
and artifact hashes before and after elaboration.

The receiver compares the remote transfer request and every transferred
verification input with the current local files. It requires successful
local and remote results, the same reconstructed source catalog and hashes,
the exact remote compiler command and isolated import path, validated axiom
logs, and equal full external-artifact hash maps. Archive contents have exact
manifest coverage, and receiving extraction rejects duplicate, unsafe, and
noncanonical names. The predecessor checker includes pinned manifests for
the earlier proof/evidence snapshots, the original Experiment 008 packet,
and its subsequent fresh-VM recheck; it hashes their actual current contents.

Two small launcher/checker hardening repairs were completed and inspected
during review. The upload extractor now rejects noncanonical member paths
immediately, preventing differently spelled archive names from targeting the
same extracted file. The supplementary project-cache exclusion check now
derives the new project module names from the source manifest, includes the
current combined artifact and embedded finite-band dependency name, and
rejects their `.olean`, `.ilean`, and `.ir` files while permitting legitimate
external root modules. The receiver also pins its axiom parser and compares
the accepted verifier's hash against the current transferred verifier.

The final independent environment is the replacement
`exp009-independent-check` allocation, VM `m-s-kkb-usc1a1-d4w1b6hb9jym`, with
boot ID `99a6359d-eedf-49db-be73-d9b65de3bf31`. It independently downloads its
own pinned compiler and library inputs below `/content/exp009_check`.
The earlier runtime receipt is retained under `remote_check/lost_runtime/`
and is excluded from acceptance of the replacement runtime.

The receiving checker now binds the matching fresh initialization receipt,
distinct allocation and boot metadata, exact bootstrap worker, all six
bootstrap input files, their original delivery archive, and the bootstrap
launch pins. It requires successful bootstrap completion with the same
compiler and dependency revisions used by the final proof. Every bootstrap
command must have exit code zero, a finite nonnegative duration, a canonical
log path below the bootstrap directory, and its matching log hash. The
download and Git command vectors are reconstructed from the pinned inputs;
cache-client compiler paths and the final library-cache request are checked
against the intended sources and proof imports. All this evidence is bound
into the receiving receipt's accepted file maps.

Chronology is checked between the initialization, bootstrap, and proof
receipts produced on the same VM. The local allocation receipt's timestamp
is validated separately: it records when that metadata was saved locally
and must not be mistaken for a synchronized VM creation timestamp. An
independent schema review caught the same distinction. The actual exported
bootstrap evidence passed, including all 57 command logs, and 21 targeted
in-memory mutations were rejected for their intended reasons. These checks
cover altered pins, failed commands, invalid log paths and hashes, changed
download and checkout commands, forged revision output, cache mismatches,
altered launch and worker data, and missing or unclaimed logs. They do not
alter the accepted files. Outcomes are recorded in
`evidence/RECEIVER_BOOTSTRAP_VALIDATION.json` and `evidence/REVIEW_CHECK.json`.

The trust boundary remains the pinned Lean compiler, its core library, and
compatible compiled external libraries. Recorded source revisions and
artifact agreement do not prove source-to-artifact correspondence or rebuild
Lean and Mathlib themselves. The receiver validates retained evidence; it
does not rerun Lean.
