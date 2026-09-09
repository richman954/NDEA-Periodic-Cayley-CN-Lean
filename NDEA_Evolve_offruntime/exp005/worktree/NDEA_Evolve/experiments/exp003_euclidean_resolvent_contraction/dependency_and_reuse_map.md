# Dependency and reuse map

## Inherited from immutable Experiment 002

- `NDEAEvolve.Exp002.cayleyD_mul_cayleyR`: supplies the right-inverse law for a
  Hermitian generator and a real parameter.
- `NDEAEvolve.Exp002.cayley_affine_of_right_inverse`: supplies the exact algebraic
  identity `(1-X)R = 2R-I` from `(1+X)R=I`.
- `NDEAEvolve.Exp002.cayley_preserves_norm`: supplies Euclidean norm preservation
  for the Cayley factor.
- Definitions `cayleyD`, `cayleyR`, and `cayley` are reused unchanged.

The Experiment 002 source, release commit, annotated tag, archive, Git bundle, and
dependency pins are predecessor evidence. They are not rerun or relabeled as new
Step-1 results.

## Newly proved in Experiment 003 Step 1

- the exact matrix resolvent averaging identity;
- its transport through `Matrix.toEuclideanCLM`;
- pointwise Euclidean nonexpansiveness;
- the induced Euclidean continuous-linear-map operator-norm bound;
- exact focused witnesses for the sharp non-strict boundary and failure without
  Hermiticity.

## Trusted boundary

Lean rechecks the new universal statements against the pinned Mathlib kernel and the
imported Experiment 002 declarations. No Boolean or generated certificate is trusted
as a proof. The local delivery verifier checks bytes, manifests, Git objects, and
preserved diagnostic classifications; unless separately stated, fresh extraction
verification is not a new kernel proof replay.

## Not executed

There is no fresh Julia execution because Julia is absent locally and installation is
outside this Step-1 authorization. Campaign Steps 2–5, Verso work, inverse-integrator
work, and QGI work are not started.
