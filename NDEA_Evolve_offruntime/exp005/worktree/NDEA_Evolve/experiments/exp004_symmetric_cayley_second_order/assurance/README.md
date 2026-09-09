# Experiment 004 verification

`run_verification.py` runs the pinned Lean 4.31.0 executable with one worker,
a bounded per-command timeout, and a shared nonblocking job lock. It records
UTC start/end times, exact command arguments, source and output SHA-256 hashes,
exit status, and complete output in separate timestamped receipts and logs.
Failed, timed-out, and interrupted attempts remain in the evidence directory.

Run from this directory, or give the full script path:

```sh
python3 run_verification.py prepare
python3 run_verification.py predecessors
python3 run_verification.py probe --path /absolute/path/to/Probe.lean --timeout 300
python3 run_verification.py module --path /absolute/path/to/SymmetricCayleyLocal.lean
python3 run_verification.py production
python3 run_verification.py controls
python3 run_verification.py combined-controls
```

`prepare` copies the existing cached import closure into
`/tmp/exp004_build/lib/lean`; it does not run Lean or download dependencies.
It includes external imports found in existing predecessor, production, control,
and optional `--path` sources. Use `--extra-import MODULE` for an additional
dependency. Repeat preparation after changing imports. Explicit `--source-root`
and `--artifact-root` options override package roots. `--cache-root PATH` selects
another shadow build location, including an authorized tmpfs directory.

Preparation is a separate stage. Every later command must use the same cache
root. `production` and `controls` compile all predecessors and Experiment 004 modules
afresh in dependency order. `predecessors` compiles only the predecessor chain.
`module` compiles its specified repository module and writes an `.olean`;
`probe` checks its specified file without writing an `.olean`. They assume their
required dependencies have already been compiled.

`--skip-existing` is an explicit development convenience and marks the run's
receipts as development. It must not be used as evidence of a fresh qualifying
build. Successful qualifying module verification requires `production` or
`controls` without that flag. `combined` and `combined-controls` generate a
single fresh source containing the entire predecessor and Experiment 004 chain, with
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
predecessor file against Step 5, narrow-import shadow provenance, source policy,
current source hashes in successful receipts, log integrity, complete modular
dependency order, and the compiled principal axiom rows. It runs no Lean jobs.
It also verifies the pinned Lean executable hash, receipt binary identities,
the clean pinned Mathlib checkout, and the original/inherited raw predecessor
tag objects as well as their mathematical commit.
Audit and manifest paths must be new; historical files are never overwritten.
The audit requires the local cubic bound, fixed-time inverse-square bound, and
convergence endpoint explicitly. Every new production/control file must have
named axiom audits, and each public named control theorem must be included.

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
earlier release tags. Recovery also verifies that the pinned Step-5 tag resolves
to `3a5078a02bbc1423a302016d4e14c78f874f021f`.
