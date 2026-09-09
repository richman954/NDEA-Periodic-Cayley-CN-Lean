# Experiment 003 Step 3 final evaluation

## Verdict

The Step 3 mathematical mission is verified. For arbitrary finite-dimensional
complex Hermitian matrices and every real step, including zero and negative
steps, the requested exact split-versus-unsplit Cayley identity and induced
operator-norm estimate hold.

One requested negative control was internally inconsistent: no small-step
counterexample can refute the estimate obtained by replacing `alpha^2` with
`|alpha|`, because `alpha^2 <= |alpha|` whenever `|alpha| <= 1`. The release
does not fabricate that witness. It instead contains a compiled theorem proving
the impossibility and a compiled counterexample to the globally quantified
linear-scaling claim at `alpha = 10`.

## Assurance summary

- Julia 1.12.6 constructed and checked exact Gaussian-rational examples and a
  free noncommutative algebra expansion, then emitted the canonical JSON
  certificate and receipt.
- Python 3.11.2 independently reconstructed the certificate with exact
  `Fraction` arithmetic and passed 407 strict checks.
- Lean proves the identity universally through an arbitrary-ring
  noncommutative core, then transports it through `Matrix.toEuclideanCLM`.
- The norm proof uses only the triangle inequality, continuous-linear-map
  submultiplicativity, scalar norm simplification, and the Step 1 resolvent
  contraction theorem.
- A combined Lean run and a qualifying module-by-module Lean run both exited 0
  under bounded timeouts with one Lean job.
- The public identity, public norm theorem, and controls depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Policy scans found no `sorry`, `admit`, custom axioms, `unsafe`, or
  `native_decide`.
- The Step 2 release commit/tag, its production and evidence files, and pinned
  project manifests remain unchanged.

The RAM workaround and import-only shadow provenance are disclosed in the
evidence directory. Warnings in Lean logs are non-failing linter/tactic
suggestions; the qualifying logs contain neither `error:` nor `sorryAx`.

## Scope closure

This report closes Experiment 003 Step 3 only. No telescoping or
continuous-exponential project was performed.
