# Experiment 003 Step 5 — plan and specification

Accepted user instruction: “plan step 5, then proceed”, 2026-09-07.
This is the newly authorized continuous-exponential stage. The earlier four-hour
authorization applied to Step 4; it is not represented as a new time budget here.

## Predecessor and isolation

The immutable predecessor is Step 4 commit
`902a5d44c222254a443a01aebf563df72b8154d5`, tagged
`exp003-step4-finite-n-telescoping-global-bound-verified-final-20260907`.
Development uses a separate clone of its release bundle and branch
`exp003-step5-continuous-exponential-comparison`.
All new production and evidence files belong to Step 5. Prior production,
evidence, archives, manifests, dependency pins, and toolchain are preserved.

## Mathematical target

For Hermitian finite complex matrices A and B, set H = A+B and use the induced
operator norm on `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`.
The existing convention is C(H,α) = (I-iαH)(I+iαH)⁻¹. Thus a physical time step
h corresponds to α=h/2 and exact evolution exp(-ihH), with negative sign.

1. Prove a Banach-algebra exponential remainder estimate:
   `‖exp Z - (1 + Z + (1/2) • Z²)‖ ≤ 2‖Z‖³` when `‖Z‖ ≤ 1/2`.
2. Prove the exact quadratic Cayley remainder using the Step 1 contractive
   resolvent. Deduce local error `≤18|α|³‖Hhat‖³` provided
   `4|α|‖Hhat‖ ≤ 1`.
3. Use exponential unitarity, `exp(N • Z)=(exp Z)^N`, and Step 4's fan theorem
   to bound the unsplit N-step error by `18N|α|³‖Hhat‖³`.
4. Add Step 4's split-versus-unsplit error. For every real t, N>0, and
   `2|t|‖Hhat‖ ≤ N`, prove

   `‖(Chat A (t/(2N)) * Chat B (t/(2N)))^N - exp((-i*t) • Hhat)‖`
   `≤ (t²/N)‖Ahat‖‖Bhat‖ + (9/4)|t|³‖Hhat‖³/N²`.

5. Prove that the split evolution converges in induced operator norm to
   `exp((-i*t) • Hhat)` as N tends to infinity, for every real t and every
   finite dimension, including dimension zero.

These constants are sufficient bounds; no optimality claim is made. The finite
rate has an explicit small-step condition, eventually satisfied for any fixed
matrices and time. A finite-N zero-step-count identity will be kept distinct
from fixed-time formulas requiring N>0. No assertion of norm one is made in
dimension zero.

## Controls and verification

Check zero time, negative time, zero generators, and dimension zero; retain
compiled controls for the Cayley sign and factor-of-two convention and for
the distinction between approximation and finite-step equality.
Use the existing pinned Lean 4.31/Mathlib installation with narrow imports,
bounded subprocess timeouts, and at most one Lean job at a time.
Reuse the established import-only predecessor shadows with explicit provenance.
Run both module-by-module and combined verification of final source and controls.
Audit principal declarations for only the standard dependencies
`propext`, `Classical.choice`, and `Quot.sound`; reject prohibited shortcuts.
Save exact commands, source hashes, logs, receipts, a final evaluation,
manifest, commit/tag, and recoverable release archive and Git bundle.

## Execution order

Freeze this target; implement analytic remainder and algebraic comparison in
parallel while preparing the serial build runner; compile and repair; prove
the fixed-time limit; compile focused controls; perform final assurance and
package the verified release. Development failures remain historical evidence.
