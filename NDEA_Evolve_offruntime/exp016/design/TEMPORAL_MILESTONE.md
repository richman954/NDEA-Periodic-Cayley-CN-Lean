# Actual temporal refinement — development milestone

Accepted September 10, 2026 UTC. Exp016 has 53 accepted development modules.
Full combined/fresh independent qualification and sealing remain pending.

## Barrier removed

[TemporalBudget.lean](../lean/TemporalBudget.lean) replaces the abstract induced
operator norms in the existing actual grid-time PDE certificate by the proved
physical-grid and sampled-potential bounds. Write

`F(a,b) = a*(a+2*b)^2/16 + (a+b)^3/8`,
`A(h) = 4/h^2+1`, `B(v) = sum_ell ||v_ell||+1`,
`C(h,v) = F(A(h),B(v))`, and `rho = sqrt(h)*||y_initial||`.

For the actual Hermitian A-half/B-full/A-half trajectory and nonnegative
variable steps, `sampledTemporalSum_le_physical` proves

`actual temporal sum <= rho * C(h,v) * sum_j k_j^3`.

The source derives this sum from the existing `sampledQuantitativeBudget` by
an exact identity. It uses the actual certificate's 1/16 and 1/8 constants;
it does not substitute the separately available integrated 1/12 constant.
The spatial mean, velocity and generator-velocity terms are unchanged, as is
the arbitrary initial mismatch in the general certificate.

[TemporalRefinement.lean](../lean/TemporalRefinement.lean) uses the already
recorded `M=q+1`, `N=2M+1`, `h=2*pi/N`, `J=N^4`, `k=1/J` schedule and proves
that its actual final time is exactly 1. The accumulated cubes equal `k^2`.
The exact normalization theorem, for real `n != 0`, is

`(n^4)^(-2) * C(2*pi/n,v)`
`= n^(-2) * F(pi^(-2)+n^(-2), B(v)*n^(-2))`.

This identity and the polynomial limit prove `k^2*C(h,v) -> 0`. The existing
uniform bound on actual sampled initial data then proves that
`scheduledSampledTemporalSum_tendsto_zero` applies to the actual numerical
trajectory, not merely to a proposed majorant.

## Doors opened and actual consumer

`scheduledCayley_error_le` proves the actual time-1 error certificate

`error_q <= scheduledInitialError_q + scheduledTemporalBound_q + scheduledSpatialSum_q`.

`scheduledNonspatialBudget_tendsto_zero` proves that the first two terms tend
to zero, reusing the accepted initialization limit. The exact raw Fourier
target, actual ordered recurrence, point-sampled Exp014 data, physical L2 norm
and Exp014 solution remain in the theorem. The actual-limit and error theorems
require the existing regular Hermitian Fourier potential assumptions.
Algebraic coefficient-limit lemmas alone do not assert operator bounds for an
irregular potential.

## Best next move and next barrier

The outstanding term is the actual accumulated spatial sum. The recommended
first lemma is that centered odd-grid alias folding cannot increase absolute
frequency, followed by a weighted sampled-potential multiplication bound.
See [the comparison and proposed numerical weighted-norm route](NEXT_SPATIAL_ROUTE.md).
Propagated fourth moments, spatial-sum vanishing, approximation quantifiers,
and the broader solver convergence theorem remain unproved. No residual-to-zero
assumption was introduced. The new scheduled consumer is at time 1; no new
uniform between-grid-time refinement theorem is claimed.

## Checks and recovery

Both modules passed the pinned Lean 4.31.0 environment with Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The accepted checks have 24 explicit
transitive axiom reports, zero warnings and zero errors; every report contains
only `propext`, `Classical.choice` and `Quot.sound`.

| Module | Source SHA-256 | Accepted check |
|---|---|---|
| TemporalBudget | `3b3424eef3246e0686e50a854efff123e48d733e105fc714c57aa9b2d470a5d3` | [receipt](../evidence/20260910T002106.832927Z_TemporalBudget.json), 254.885 seconds |
| TemporalRefinement | `5f2c5c7260b6d8bb8c5ec51726b53aa331792bb2b58eff7ea3f70d65c8982b98` | [receipt](../evidence/20260910T003342.122048Z_TemporalRefinement.json), 189.601 seconds |

The [local milestone receipt](../evidence/TEMPORAL_MILESTONE_LOCAL.json) binds
the source, compiler log, artifact and original result receipts. All 51 prior
accepted module bindings and 124 preexisting project artifacts remain unchanged.
The failed first refinement attempt is preserved separately, including its two
wrapper errors and warning; it is not accepted evidence.

Reproduce each module through the existing `run_lean.py` in dependency order,
after verifying imported project artifacts against their source-bound receipts.
No old proof was rerun. No Colab runtime, Comparator, additional kernel, dependency
upgrade or sealed-predecessor edit was required. Ordinary modular acceptance is
distinct from the still-pending combined and fresh independent qualification.

Manual verified checkpoints precede each long check and follow this milestone.
Watcher session 27367 continues minute snapshots. The dated Git readback and
local recovery receipts identify the exact later backup coverage; main and
sealed archival branches remain unchanged.
