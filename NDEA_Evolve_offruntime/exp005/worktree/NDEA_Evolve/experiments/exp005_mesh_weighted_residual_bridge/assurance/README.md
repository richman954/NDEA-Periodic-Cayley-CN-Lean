# Experiment 005 verification

`run_verification.py` runs the pinned Lean 4.31.0 executable with one worker,
a bounded per-command timeout, and a shared nonblocking job lock. It records
UTC start/end times, exact command arguments, source and output SHA-256 hashes,
exit status, and complete output in separate timestamped receipts and logs.
Failed, timed-out, and interrupted attempts remain in the evidence directory.

Run from this directory, or give the full script path:

```sh
python3 run_verification.py bootstrap
python3 run_verification.py prepare
python3 run_verification.py predecessors
python3 run_verification.py probe --path /absolute/path/to/Probe.lean --timeout 300
python3 run_verification.py module --path /absolute/path/to/MeshWeightedStability.lean
python3 run_verification.py production
python3 run_verification.py controls
python3 run_verification.py combined-controls
```

`bootstrap` is a development shortcut. It copies compatible package artifacts
from `/tmp/exp004_build`, matching each against the pinned package cache and
recording source/destination SHA-256 hashes. Ten predecessor project artifacts
are copied only after matching their current sources and output hashes to the
final Exp004 serial run `20260908T002534.597869Z_2`. The bootstrap receipt is
marked development; the original cache and source tree remain untouched.

`prepare` copies the existing cached import closure into
`/tmp/exp005_build/lib/lean`; it does not run Lean or download dependencies.
It includes external imports found in existing predecessor, production, control,
and optional `--path` sources. Use `--extra-import MODULE` for an additional
dependency. Repeat preparation after changing imports. Explicit `--source-root`
and `--artifact-root` options override package roots. `--cache-root PATH` selects
another shadow build location, including an authorized tmpfs directory.

Preparation is a separate stage. Every later command must use the same cache
root. `production` and `controls` compile all predecessors and Experiment 005 modules
afresh in dependency order. `predecessors` compiles only the predecessor chain.
Without `--skip-existing`, these stages first move every active project cache
artifact to a run-specific retired directory outside `LEAN_PATH`. The fresh
controls chain therefore rebuilds all ten predecessors and three new modules,
then checks controls: fourteen serial Lean invocations. The retirement is
recoverable and recorded; it changes only the disposable Exp005 cache.
`module` compiles its specified repository module and writes an `.olean`;
`probe` checks its specified file without writing an `.olean`. They assume their
required dependencies have already been compiled.

`--skip-existing` is an explicit development convenience and marks the run's
receipts as development. It must not be used as evidence of a fresh qualifying
build. Successful qualifying module verification requires `production` or
`controls` without that flag. `combined` and `combined-controls` generate a
single fresh source containing the entire predecessor and Experiment 005 chain, with
per-source hashes, and compile it without project `.olean` dependencies.
The exact generated combined source is retained under `evidence/generated`
and included in the final selected-evidence manifest.

The first two predecessors use the existing Step-2 narrow-import shadow sources;
all later modules use their repository production sources. No predecessor file
is rewritten by these scripts. Sources that change during a command invalidate
that attempt even if Lean exits successfully.

After both final verification routes pass, run `audit_release.py` with an
explicit `--modular-run-prefix` (the run ID of a complete `controls` invocation),
`--combined-receipt` (its successful combined-controls Lean receipt), and a new
`--output` JSON path. Optional `--manifest` creates a selected source/evidence
SHA-256 manifest only after the audit passes. The audit checks every tracked
predecessor file against Experiment 004, narrow-import shadow provenance, source policy,
current source hashes in successful receipts, log integrity, complete modular
dependency order, and the compiled principal axiom rows. It runs no Lean jobs.
It also verifies the pinned Lean executable hash, receipt binary identities,
the clean pinned Mathlib checkout, and the original/inherited raw predecessor
tag objects as well as their mathematical commit.
Audit and manifest paths must be new; historical files are never overwritten.
The audit requires ten weighted-stability, residual, and mesh-convergence
endpoints explicitly. The source contract requests 15, 11, and 3 production
axiom audits plus 11 controls, totaling 40. Each public named production and
control theorem must be covered. It also verifies that the qualifying modular run reset the
active project cache before any compilation, so bootstrap reuse cannot be
mistaken for fresh final verification.

Once the full `evidence/FINAL_SHA256SUMS` manifest and final sources/evidence
are committed and tagged, `package_delivery.py --commit FULL_COMMIT --tag TAG
--require-manifest` creates a new external release directory. It verifies a
clean source branch and tag, writes a Git source archive and recoverable bundle,
extracts the archive and clones the bundle into a fresh `/tmp` directory, and
checks the full manifest in both recovered copies. `DELIVERY_RECEIPT.json`
records commands, timestamps, commit/tag identity, file counts, hashes, and
recovery results outside the final repository. It does not run Lean, commit,
tag, or publish. Existing release directories are refused, and temporary
recovery copies are retained with their path in the receipt.
The bundle includes all refs in the isolated release repository to preserve
earlier release tags. Recovery also verifies that the pinned Experiment 004 tag resolves
to `956ce8acac594c45cf576b66972a082c89190bf8`.

## Release command sequence

From this assurance directory, after final source changes have stopped:

```sh
python3 -B run_verification.py controls
python3 -B run_verification.py combined-controls
python3 -B audit_release.py --modular-run-prefix MODULAR_RUN_ID --combined-receipt COMBINED_LEAN_RECEIPT_PATH --output ../evidence/FINAL_ASSURANCE_AUDIT.json --manifest ../evidence/SELECTED_EVIDENCE_SHA256SUMS
```

Use the run ID without its command counter and the successful combined Lean
receipt, not the source-generation receipt. Audit and manifest paths must not
already exist; use distinct candidate paths for preliminary audits. Complete
the final report and intended documentation, then stage the deliverable files:

```sh
git -C ../../.. add -- NDEAEvolve/Experiments/Exp005 experiments/exp005_mesh_weighted_residual_bridge
python3 -B freeze_manifest.py
git -C ../../.. add -- experiments/exp005_mesh_weighted_residual_bridge/evidence/FINAL_SHA256SUMS
```

Create the intended final commit and release tag, confirm the source tree is
clean, and run the external recovery packager with their concrete identities:

```sh
python3 -B package_delivery.py --commit FULL_FINAL_COMMIT --tag FINAL_RELEASE_TAG --require-manifest
```

The packager writes only to the new external release directory and fresh
temporary recovery paths. It does not create the commit or tag. Its default
release directory is `exp005/releases/20260907_verified_final`; pass an explicit
new `--release-dir` if a different release date or candidate directory is needed.
