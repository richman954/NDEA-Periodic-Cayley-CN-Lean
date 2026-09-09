# Reproduce Experiment 015

Use a separate working copy for reruns. Preserve sealed sources, receipts and
packets. This directory's scripts define the workflow; a prepared script or
recovery checkpoint is not a successful proof check.

## Pinned inputs and foundation

Lean is 4.31.0, binary SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib is pinned to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`;
`remote_check/bootstrap_inputs/lake-manifest.json` pins all packages.
The compiler and compatible external library artifacts are trusted inputs;
the workflow downloads them independently but does not rebuild them from source.

`predecessor_sources/Exp014Combined.lean` is the exact sealed combined source,
SHA-256 `40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee`.
`make_combined.py` removes only its 143 axiom-print lines to reconstruct
`lean/Exp014Foundation.lean`, SHA-256
`9d8ac0dfcba35dec86ea229657defc88da01f94ddfece9b8f119f52120a4d8c6`.
All predecessor proof bodies, including the retained generic Exp013 foundation,
remain. The final combined source embeds this foundation and the seven new
modules. Its public audit catalog covers only new Exp015 declarations.
Earlier numerical proof chains remain in their independently accepted packets.

## Local development and final combined check

`run_lean.py` checks individual modules against recorded local compiler/package
paths and predecessor development artifacts. It is separate from the final
isolated source check. Each dated module receipt binds its source, log and
compiled artifact; passing receipts count only while those hashes still match.

After all sources and controls pass, generate the combined source and exact
catalog in the working copy:

```sh
python3 -B make_combined.py
```

Run the final checker with a new output directory:

```sh
python3 -B verify_combined.py \
  --root /path/to/exp015-working-copy \
  --lean /path/to/lean-4.31.0-linux/bin/lean \
  --mathlib /path/to/mathlib \
  --other-packages /path/to/mathlib/.lake/packages \
  --output /path/to/new-verification-output
```

The checker verifies exact source reconstruction, every public audit name,
compiler and dependency pins, clean dependency checkouts, and external imports.
It copies only the external artifact closure into a fresh directory and uses
only that directory and pinned compiler core in LEAN_PATH. Inherited
LEAN_SRC_PATH and LEAN_SYSROOT overrides are removed. Source and artifact hashes
are checked again after compilation. Only propext, Classical.choice and
Quot.sound are allowed in the audited dependencies.

## Fresh CPU runtime and source delivery

A distinct session named `exp015-independent-check` must begin with no project
paths under `/content`. Its target is `/content/exp015_check`.
`remote_check/initialize.py` records the empty initial environment;
`VM_ALLOCATION.json` and `ENVIRONMENT_EXPECTED.json` bind the observed VM and
boot identity. The receiver rejects reused predecessor identities, including
the accepted Exp014 VM. No runtime is allocated automatically by these files.

In the finalized working copy, run `prepare_final_sources.py` and
`prepare_bootstrap_inputs.py`. They create and read back exact source-only
archives and pin the bootstrap launcher. Existing delivery receipts/archives
are preserved by refusing repeated preparation. Upload the exact paths named
in their receipts and the current launch scripts. The bootstrap launcher
refuses unprepared hashes. Run it before `remote_check/start_final.py`; the
latter requires successful bootstrap for the same combined source and refuses
existing source/output directories. No compiled project artifact is delivered.

After the independent check passes, `remote_check/export_evidence.py` exports
its inputs, source, environment, bootstrap command logs, compiler log and
artifact manifests. Download the archive and EXPORT_RECEIPT.json, then run:

```sh
python3 -B remote_check/check_download.py /path/to/evidence.tar.gz \
  --sha256 DIGEST_FROM_EXPORT_RECEIPT \
  --extract-to /path/to/new-extraction-directory
```

The receiver verifies the archive before extracting, rejects unsafe/duplicate
members and missing or changed payloads, compares every exact source delivery,
validates fresh initialization and completed bootstrap commands, reparses both
axiom logs and compares the full external artifact maps. It writes an accepted
transfer receipt only after all gates pass; it does not itself rerun Lean.

## Review, packet and recovery

Offline infrastructure tests exercise synthetic reconstruction, corruption,
identity, delivery and inherited-environment controls. They are not Lean proof
evidence. The independent review must bind current source, tools, documents
and complete public catalog before `finalize.py` can seal a packet. The finalizer
rechecks accepted local and received bytes, modular artifacts and preserved
predecessor manifests, then validates exact ZIP readback, CRC and all payload
hashes. Its external packet receipt avoids a self-hash cycle.

The proved scope is coefficient-one continuous L2 forcing/residual stability,
including arbitrary spatial origin, initial error and an Exp014 application.
Joint continuity of the forcing or residual difference is explicit and is not
inferred from the classical predicate for an unrestricted potential. No discrete numerical
convergence follows merely from running this workflow.

Follow `/home/richman954/NDEA_Recovery/START_HERE.md` and RECOVERY_POLICY.md.
Keep verified local Chromebook milestone checkpoints. The final convenience
copy contains the preserved Exp001–012 release base, intervening Exp013/014
packets, the active Exp015 packet and recovery files. Its actual coverage is
recorded by LOCAL_BACKUP_RECEIPT.json under NDEA_Recovery and is accessible in
Files → Linux files → Downloads. Google Drive backup remains canceled.
