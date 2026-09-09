# Experiment 010 source and verification review

No blocking issue was found within the stated classical periodic spinor scope.
The review covers all five new modules, their complete public theorem catalog,
the numerical diagnostic, and the verification and preservation workflow.
The exact reviewed source and tool versions are recorded in
[REVIEW_CHECK.json](evidence/REVIEW_CHECK.json).

## Mathematical result

`Regular a` is the summability condition
`Σ_m (1+|m|)² ‖a_m‖ < ∞`. Its weight is positive and at least one, so it
implies absolute coefficient summability. The scalar bounds for `|m|`, `m²`,
and `m²+2` give summable majorants for the first spatial, second spatial,
and time derivatives, uniformly for all real time and position.

`ClassicalSolution.lean` applies the infinite-series differentiation theorem
to the actual mode functions. It establishes time and first spatial
`HasDerivAt` statements before identifying their `deriv` values. For the
second derivative, the already established first derivative is rewritten as
its series and differentiated again using the second-moment bound. This step
does not assume an exchange of derivatives and summation or a fourth moment.
The PDE follows by summing the mode identity with the established summability
facts and the continuous linear potential operator.

The equation has the intended signs:
`i Ut = -Uxx + (Z+X)U`, with split generators `A=-∂xx+Z` and `B=X`.
The spatial derivative factors are `im` and `-m²`, including negative
frequencies. Joint continuity of the solution and all three derivatives uses
the same global summable bounds. `IsClassicalPeriodicSolution` explicitly
requires existence of each derivative, in addition to continuity, periodicity,
and the PDE. Its use of Lean's totalized `deriv` therefore does not weaken the
intended classical-solution assertion.

`ClassicalClosure.lean` identifies the existing infinite grid reference with
pointwise samples of the actual solution. The error is the mesh-weighted norm
of the actual split Cayley iterate minus these samples at time `Nk`.
The error-bound endpoint supplies both the classical-solution predicate and
the inherited bound, including both coefficient tails. It retains every
cutoff, grid, time-step, and horizon restriction. The growing-cutoff endpoint
reaches time one exactly and gives convergence when sampled initial error
tends to zero; exact sampled initialization is also proved.

The 18 exact controls include an explicitly regular coefficient sequence
nonzero at every signed frequency, infinite support, and positive tails at
every finite cutoff. They also check zero and single-frequency data and
signed derivative identities. The public catalog contains 65 new theorems:
19 regularity, 11 derivative/PDE, 10 continuity/classical, 7 grid closure,
and 18 control declarations. The catalog was compared with the complete
production sources rather than selected endpoint names.

## Numerical evidence

The separate signed geometric diagnostic datum has coefficient norm mass 3
and second weighted moment 23. These values and all 15 recorded geometric
moment-tail formula values were independently checked with exact rational
arithmetic. The saved diagnostic's script hash and summary counts agree with
its source and detailed rows.

The mode evolution, generator action, signed derivative factors, and centered
difference formulas match the equation. Independent closed geometric formulas
at time zero and decreasing finite-difference errors supplement the algebraic
PDE residual calculation. The omitted-tail comparisons include the reference
sum's own truncation bound. The 36 wrong-equation controls detect a reversed
time sign, reversed Laplacian sign, or missing potential. Analytic truncation
bounds evaluated in floating point do not certify rounding error. The formal
encoded geometric datum and this diagnostic datum are clearly distinguished.

## Verification and preservation

The generator pins the exact frozen Experiment 009 foundation, embeds project
sources, and reconstructs the combined source and full public audit catalog.
The final checker permits only external imports, copies their artifact
closure into an isolated directory, and checks compiler, source, dependency,
and audit hashes. The fresh-VM bootstrap binds the actual combined source to
its dependency request, including `Mathlib.Analysis.Calculus.SmoothSeries`.
The receiving validator binds the new environment, bootstrap inputs, every
completed command log, final source, both compiler audit logs, and matching
external artifact manifests. The bounded offline adaptation suite passed
16 checks; its transformed predecessor evidence is explicitly a protocol
fixture, not an Experiment 010 proof run.

The finalizer rechecks accepted evidence bytes, modular receipts, current
source reconstruction, review hashes, and predecessor preservation before
packaging. It refuses existing sealed outputs, reads every ZIP member back,
and verifies the exact manifest bytes. The final packet receipt stays outside
the ZIP to avoid a self-hash cycle. A numerical receipt key mismatch found
during review was corrected to `script_sha256` before finalization.

This review does not itself rerun Lean. Accepted local and independent
compiler runs and their qualification are recorded separately in
[FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). The compiler and
compatible external library artifacts remain trusted inputs. Re-elaboration
covers the predecessor proof bodies retained in the frozen foundation.

No uniqueness, variable spatial potentials, interpolation convergence,
rough-data extension, or universal second-order rate for arbitrary infinite
coefficient data is established by this milestone.
