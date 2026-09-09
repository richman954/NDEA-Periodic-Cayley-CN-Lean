# Reproduce Experiment 010

Use a separate copy of this directory for reruns. The sealed packet's sources,
logs and receipts must remain unchanged. Build artifacts are deliberately
excluded from the packet.

## Preserved compiler and dependency pins

Lean is `4.31.0`; its binary SHA-256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib is pinned to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
The full dependency lock is
`remote_check/bootstrap_inputs/lake-manifest.json`.

The final independent check used a new CPU VM with no preexisting project
directories. `remote_check/VM_ALLOCATION.json` identifies it;
`remote_check/ENVIRONMENT_EXPECTED.json` pins its initial environment record.
The bootstrap tools download the compiler, check out every pinned package,
compile the cache client, and download compatible external library artifacts.
They do not rebuild the compiler or Mathlib from source.

## Combined proof check

The combined source in `lean/Exp010Combined.lean` contains the frozen
predecessor proof bodies followed by all five new modules and the complete new
public theorem/control axiom catalog. It imports only external libraries.
`make_combined.py` reconstructs it deterministically and records all component
source hashes in `evidence/FINAL_INPUTS.json`.

In a working copy, with the pinned compiler and package trees available, run:

```sh
python3 -B verify_combined.py \
  --root /path/to/exp010-working-copy \
  --lean /path/to/lean-4.31.0-linux/bin/lean \
  --mathlib /path/to/mathlib \
  --other-packages /path/to/mathlib/.lake/packages \
  --output /path/to/new-verification-output
```

The output directory must not exist. The checker validates compiler and source
pins, exact combined reconstruction, the public audit catalog, and clean pinned
dependency checkouts. It copies the required external artifact closure into a
new directory, uses only that directory and compiler core in `LEAN_PATH`, and
checks the source and dependency artifact hashes again after compilation.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in audit output.

The local development runner `run_lean.py` uses recorded local paths and
predecessor project artifacts for individual module checks. It is not the
independent source-only project check. Final combined verification rechecks
the predecessor bodies retained in the frozen foundation.

## Fresh VM delivery and evidence validation

The exact bootstrap bundle is `remote_check/bootstrap_inputs.tar.gz`, pinned
by `remote_check/BOOTSTRAP_INPUTS.json`. The source bundle and its destination are named in
`remote_check/FINAL_UPLOAD.json`. `remote_check/start_bootstrap.py` and
`remote_check/start_final.py`
verify those deliveries before starting their corresponding checks. They use
fixed paths under `/content/exp010_check` and refuse existing work directories;
use an empty runtime when repeating them. The VM should first run
`remote_check/initialize.py`.

After completion, `remote_check/export_evidence.py` packages source, bootstrap
inputs and logs, compiler logs, and artifact manifests. The export checksum is
recorded in `remote_check/EXPORT_RECEIPT.json`. The receiving validator compares
this evidence with the accepted local source and result:

```sh
python3 -B remote_check/check_download.py /path/to/evidence.tar.gz \
  --sha256 DIGEST_FROM_EXPORT_RECEIPT \
  --extract-to /path/to/new-extraction-directory
```

Run this in the working copy, since it writes a transfer receipt. It checks
the fresh environment, exact bootstrap deliveries and completed command logs,
compiler/source/library pins, both axiom logs, and equal external artifact
manifests. The receiving validator does not itself rerun Lean.

## Numerical and packet checks

In the working copy, `python3 -B numerical_checks.py` reruns the derivative
diagnostics and records its script hash. The [diagnostics report](NUMERICAL_DIAGNOSTICS.md)
describes their finite-difference and analytic-tail tolerances.

`PACKET_MANIFEST.json` maps every payload path to its SHA-256 digest. The
external `evidence/FINAL_PACKET_RECEIPT.json` and neighboring ZIP checksum file
record the sealed review archive. The receipt is outside the ZIP to avoid a
self-hash cycle. `finalize.py` verifies accepted evidence and refuses an
existing archive or manifest before writing anything.
