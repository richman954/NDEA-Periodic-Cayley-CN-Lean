# Exp016 convergence assurance

Status at creation: tooling and additive specification controls prepared; new Lean results are pending. No acceptance ledger, sealed predecessor, existing mathematical source, main branch, or dependency pin is modified.

## Verified starting evidence

The previous run 42343169545 at commit adfe4b4d1abbadaecaed4fd80c1dc6c7b05eebaf completed successfully. Its full job log records 12 Python tests, 86 rebuilt project modules, InitialErrorTransfer compilation, eight target axiom reports using only propext/Classical.choice/Quot.sound, and TARGET_COMPILE_AND_AXIOM_AUDIT_PASS. Its artifact ID is 13561694530 and the upload log reports ZIP SHA-256 bfbc9f80ecfb2a4f60134eec3ba6722b28bbeb24c2455cfb6f1050367d17e467. This readback does not claim a separate local download/re-hash of that historical ZIP.

## Exact next claims

This branch checks the unchanged InitialErrorTransfer, BaselineTimeOneConvergence, and UniformGridTimeConvergence source files, including the latter's complete transitive project-source closure. These are preserved existing drafts, not newly invented replacement mathematics.

The original datum remains in Exp014.FourierState and the potential remains RegularPotential with HermitianFourierPotential symmetry. Time-one convergence uses the saved mesh/time schedule. The finite-horizon result fixes each T>0 and takes the maximum over all numerical times, including initialization and the final endpoint. This does NOT assert arbitrary L2 data, arbitrary discretizations, a second-order convergence rate, uniformity over unbounded time, or convergence between time steps.

VerificationContracts.lean independently writes out the actual sampled trajectory minus the actual continuum solution, without approximation cutoffs, and checks that the target theorems inhabit those types. Two additional controls require initialization and the endpoint to be included in the maximum. These contracts improve specification checking but are not an independent human mathematical review.

## Assurance layers

1. Byte identity: reviewed target Git blobs; source SHA-256 values; committed source versus compiled source; unchanged original pins.
2. Fresh project build: compile every required project module from retained sources in a new output directory, without historical project object files.
3. Specification and axiom audit: 23 named declarations, including four contracts/controls, must have complete, nonduplicate, exact-name reports and only the three allowed standard axioms.
4. Negative controls: a false proof and missing module must fail; intentionally admitted and custom-axiom fixtures must be rejected by the axiom policy even though Lean can elaborate them. These fixtures exist only in separate scratch files, not in trusted imports.
5. Kernel replay: the bundled pinned-toolchain leanchecker --fresh --verbose VerificationContracts replays imported and local declarations from an empty environment. This is the SAME Lean kernel, not an independently implemented verifier.
6. Evidence audit: a separate program re-hashes the saved source/object/log bundle, compares source bytes against Git, checks the exact targets and commands, and rejects missing controls or incomplete receipts. It verifies consistency of evidence, not mathematical truth on its own.
7. Reproduction: two separate hosted jobs repeat these checks; a third job downloads both artifacts, re-audits each and compares committed sources, pins, executable hashes and theorem coverage.

## Testing and remaining trust

The 21 new Python tests passed in the authoring container. The existing 12 builder tests are also rerun in CI. Synthetic fixture bytes in the Python tests are deliberately NOT Lean proof objects. Passing those tests means the evidence checker detects the tested faults, not that any theorem passed.

The authoring container has Python/Git but no Lean installation and could not resolve GitHub hosts directly. GitHub's connected tools and hosted Actions provide the source readback and real Lean execution. No local Lean compilation is claimed.

Remaining trusted base: the specified logic/axioms, the pinned Lean kernel and runtime binaries, cached external library artifacts, operating system/hardware, GitHub's execution/artifact reporting, and the correctness of the intended mathematical model. Hashes establish identity relative to their anchor, not truth or authenticity by themselves. Two runs with the same software do not eliminate shared bugs. This workflow does not establish external library source-to-artifact correspondence, an independently implemented kernel result, an independent semantic review, or the project's complete Exp016 qualification/sealing gates.

Official pinned checker implementation: https://github.com/leanprover/lean4/blob/v4.31.0/src/LeanChecker.lean
Lean proof-validation guidance: https://lean-lang.org/doc/reference/latest/ValidatingProofs/

## Reproduction

From a checkout of the exact tested commit, choose a new absolute output path outside the checkout:

```sh
python3 -m unittest discover -s NDEA_Evolve_offruntime/exp016/verification_initial_error -p 'test_*.py' -v
python3 -m unittest discover -s NDEA_Evolve_offruntime/exp016/verification_convergence -p 'test_*.py' -v
python3 NDEA_Evolve_offruntime/exp016/verification_convergence/run_assurance.py prepare --repo "$PWD" --output /absolute/new/output
# Provision the unchanged output/deps Lean toolchain and pinned external package cache.
python3 NDEA_Evolve_offruntime/exp016/verification_convergence/run_assurance.py run --repo "$PWD" --output /absolute/new/output
python3 NDEA_Evolve_offruntime/exp016/verification_convergence/evidence_audit.py --repo "$PWD" --output /absolute/new/output
```

## After these gates

Read actual completed logs and receipts before promoting any claim. Reconcile the source-bound results with historical local acceptance records; do not overwrite them. Next are broader nontrivial finite-horizon controls, the canonical combined-source qualification, an independent review/checker where compatible with the immutable pins, the continuous-time interpolation obligation when claimed, and the existing transfer/finalizer gates. No automatic merge or seal occurs here.
