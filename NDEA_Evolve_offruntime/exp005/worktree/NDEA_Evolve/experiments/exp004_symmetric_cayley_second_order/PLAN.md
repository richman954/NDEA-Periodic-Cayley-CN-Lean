# Experiment 004 — symmetric Cayley splitting

## Authorization and predecessor

The user accepted the proposed symmetric-splitting campaign with “proceedx”,
then confirmed “nope, carry on” after a brief experiment-numbering check.
The earlier four-hour authorization applied only to Experiment 003 Step 4;
no new four-hour budget is inferred here.

The immutable mathematical predecessor is Experiment 003 Step 5 commit
`3a5078a02bbc1423a302016d4e14c78f874f021f`, tagged
`exp003-step5-continuous-exponential-comparison-verified-final-20260907`.
This campaign uses a separate release-bundle clone at
`NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve`, on branch
`exp004-symmetric-cayley-second-order`. No predecessor production module,
historical evidence, release archive, manifest, or dependency pin is edited.

## Frozen mathematical specification

Let A and B be arbitrary complex Hermitian n-by-n matrices, including n=0.
Use the established `operatorOf` and `Chat` representations, with every norm
the induced norm on `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`.
Write M = ‖operatorOf A‖ + ‖operatorOf B‖ and define, for every real h,

`S_h = Chat A (h/4) * Chat B (h/2) * Chat A (h/4)`.

The fractions follow the existing Cayley convention
`Chat H α = (I - iαHhat)(I + iαHhat)⁻¹`; the exact physical-time step is
`exp((-i*h) • operatorOf (A+B)) = exactStepHat (A+B) (h/2)`.

1. Establish exact noncommutative cancellation through quadratic order in
   the symmetric product. A and B need not commute.
2. Prove a local cubic bound
   `‖S_h - exactStepHat (A+B) (h/2)‖ ≤ 1000 |h|³ M³`
   whenever `2 |h| M ≤ 1`.
3. Prove unconditional unitarity of S_h, and use Experiment 003 Step 4's
   telescoping estimate to prove, for every natural N including zero,
   `‖S_h^N - exactStepHat (A+B) (h/2)^N‖ ≤ N * 1000 |h|³ M³`
   under the same local condition.
4. For every real t and positive N with `2 |t| M ≤ N`, prove
   `‖S_(t/N)^N - exp((-i*t) • operatorOf (A+B))‖`
   `≤ 1000 |t|³ M³ / N²`.
5. Deduce operator-norm convergence for every fixed t, A, and B, since the
   explicit step condition holds eventually as N tends to infinity.

The constant 1000 is deliberately conservative; no optimality or sharpness
claim is made. “Second order” means this upper rate, not a universal nonzero
leading coefficient. Zero/negative times, zero generators, and dimension zero
are included. Fixed-time division formulas requiring N>0 are distinct from
the all-N power estimate. No assertion ‖unitary‖=1 is made in dimension zero.

## Verification and controls

Use the existing pinned Lean 4.31.0/Mathlib installation and compatible cache.
Use the inherited import-only narrow shadows for the first two predecessors,
verify their provenance, and retain the predecessor proof bodies unchanged.
The separate disposable cache is `/tmp/exp004_build`; this is an ordinary
temporary-filesystem build, not a claim that tmpfs was used.
Only one Lean/Lake job may run at a time, with the established shared lock,
one worker, and bounded command timeouts (default 900 seconds).

No `sorry`, `admit`, custom axioms, `unsafe`, or `native_decide` in proof source.
Audit principal and control declarations for only the accepted standard
axioms `propext`, `Classical.choice`, and `Quot.sound`.
Check zero time, zero generators, zero dimension, zero powers, and negative
time; retain compiled exact witnesses for the half-step convention and for
distinctions between the symmetric method, nonsymmetric splitting, and exact
finite-step evolution. Witnesses must test actual mathematics, not rejected
syntax or an incorrectly characterized weaker upper bound.

Run both a fresh modular verification and a generated combined-source
verification, preserving full commands, source/output hashes, logs, and
receipts for all attempts. Use separate immutable status snapshots. Audit
the final source and predecessor preservation; freeze a manifest; commit/tag
and package the source archive and Git bundle with fresh recovery checks.
No remote publication is authorized or planned.

## Scope boundary

This campaign concerns fixed finite-dimensional generators and the symmetric
integrator. It does not prove uniform estimates under spatial mesh refinement,
an unbounded-operator/PDE limit, PDE well-posedness, or higher-order splitting.
Stop after verified Experiment 004 closure; the PDE connection is later work.
