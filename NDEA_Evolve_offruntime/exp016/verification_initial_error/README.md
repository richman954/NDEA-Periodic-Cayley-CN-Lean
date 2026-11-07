# Bounded InitialErrorTransfer verification

Status: verification tooling prepared; no new theorem acceptance is claimed.

## Scope and source boundary

The authorized task is to check the existing `lean/InitialErrorTransfer.lean`
draft, not to seal Exp016 or extend the finite-horizon or potential-cutoff work.
The baseline is commit `7607efb7bc8d3feaf8a582f2554b69ebd8f910de` on
`dev/variable-potential`. The candidate Git blob is
`32e149dda788b429d77db9fe15ef4cd07543cde3`.

This branch preserves the candidate, all accepted Lean sources, all sealed
predecessors, and the root toolchain/dependency pins. It does not change main.

## Mathematical review

The draft proves the actual sampled Cayley solver error is at most the error
for the initial Fourier cutoff plus

`2 * sqrt(2*pi) * frequencyNormTail (Exp014.coefficient a) S`.

The two contributions are distinct: numerical initial-data perturbation and
continuum initial-data perturbation. Both use existing stability at zero
potential difference. The final triangle inequality must retain both costs.
The coefficient tail is independent of numerical grid and step sequence.
No additional regularity of the original Exp014 datum is asserted.

This is an error-transfer estimate, not by itself convergence for the original
datum, arbitrary L2 data, an arbitrary horizon, or continuous-time reconstruction.
Those further results require their own checks; BaselineTimeOneConvergence is
not part of this bounded verification run.

## Ordered verification plan

1. Check the original candidate's exact Git blob and unchanged pinned inputs.
2. Resolve its actual local import closure from retained source files. Missing,
   conflicting, cyclic, or unsupported imports stop the check.
3. Provision the already-pinned Lean 4.31.0 and Mathlib revision without editing
   the dependency lock. Verify the compiler binary SHA-256 and package commits.
4. Compile every required project module from source into a new directory,
   without importing historical project object files or the user's local caches.
5. Compile the target and require explicit axiom reports for all eight public
   declarations. Allow only propext, Classical.choice, and Quot.sound.
6. Recheck source hashes and preserve commands, logs, and output hashes.
7. Report only the resulting scope. A successful target check is NOT the
   combined-source, independent fresh-runtime, controls/review, transfer, or
   finalizer qualification for Exp016. No automatic acceptance or merge occurs.

## Execution

Run the Python self-tests before preparing the source closure:

```sh
python3 -m unittest discover -s NDEA_Evolve_offruntime/exp016/verification_initial_error -p 'test_*.py' -v
python3 NDEA_Evolve_offruntime/exp016/verification_initial_error/check_initial_error_transfer.py prepare --repo "$PWD" --output /absolute/new/output
```

Preparation copies the unchanged Lake configuration to `output/deps`. Provision
that project's pinned compiler and external library cache, then run:

```sh
python3 NDEA_Evolve_offruntime/exp016/verification_initial_error/check_initial_error_transfer.py run --repo "$PWD" --output /absolute/new/output
```

The output must be outside the checkout. Preparation refuses an existing output
directory. Do not run the historical single-use finalizers or modify their
receipts. External compiler/library artifacts remain part of the trusted base;
this check does not prove library source-to-artifact correspondence.

## Evidence available when prepared

The checker passed 12 offline Python tests covering import parsing, nested
comments, forbidden proof escapes, source ordering, missing/conflicting imports,
cycles, and output non-overwrite guards. These tests did not run Lean.
The authoring environment had no Lean/Lake executable and could not fetch
GitHub content directly. The GitHub connector was used for source inspection.
The repository's README explicitly says its historical Exp016 runners depend
on omitted, machine-specific caches; this tooling does not silently reuse them.
