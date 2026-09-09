# Experiment 003 Step 4 final evaluation

## Verdict

The Step 4 mathematical mission is verified. For arbitrary finite-dimensional
complex Hermitian matrices, every real step, and every natural step count
including zero, Lean proves the requested ordered telescoping identity and
global induced operator-norm bound.

Two requested intermediate/control phrases required precise corrections:

- unconditional operator norm equality to one is false in matrix dimension
  zero; the proof instead uses unconditional unitary left/right norm
  invariance, which proves the same bound in every dimension;
- an `N^2` upper bound is weaker than the verified linear bound for `N >= 1`
  and therefore is not false. The release proves that implication and treats
  the requested strict example correctly as a non-sharpness witness.

## Assurance summary

- The arbitrary-ring identity is proved through an exact finite telescoping
  sum with no commutativity assumption.
- Cayley unitarity is transported to continuous linear maps, and unitary powers
  are stripped exactly from both sides of every local-defect summand.
- Step 3's local bound is substituted only after the fan estimate
  `‖S^N-U^N‖ <= N‖S-U‖` is established.
- An independent combined Lean run and a qualifying module-by-module Lean run
  both exited 0 under bounded timeouts with one Lean job.
- All seven emitted principal-theorem/control axiom audits list exactly
  `[propext, Classical.choice, Quot.sound]`.
- Policy scans found no `sorry`, `admit`, custom axioms, `unsafe`, or
  `native_decide`.
- The non-unitary `S=2I`, `U=I`, `N=2` witness compiles with `3 > 2`.
- The strict-slack witness compiles with local error `1/10`, two-step error
  `19/100`, and quadratic allowance `2/5`.
- The Step 3 release commit/tag, production/evidence files, release material,
  and pinned project manifests remain unchanged.

The tmpfs workaround and import-only shadow provenance are disclosed in the
evidence directory. Development failures are retained separately and excluded
from qualifying evidence.

## Scope closure

This report closes Experiment 003 Step 4 only. No continuous-exponential work
was performed.
