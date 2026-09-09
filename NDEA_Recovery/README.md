# Recovery checkpoints

For a normal restart, read [START_HERE.md](START_HERE.md), `TASK_STATE.json`,
then `/home/richman954/NDEA_Evolve_offruntime/RESUME_STATUS.md` and
`WORKING_ROADMAP.md`. Verify the actual result and final packet receipts before
repeating completed work. Preserve sealed experiments and restore only into a
new directory. These instructions also apply when this README is recovered
from a checkpoint ZIP and the separate start page is unavailable.

`checkpoint.py` preserves the selected experiment's sources, evidence, central
`RESUME_STATUS.md` and `WORKING_ROADMAP.md`, this utility, and `TASK_STATE.json`
and `RUN_MANIFEST.json` when present. Its explicit recovery metadata list also
includes `START_HERE.md`, `RECOVERY_POLICY.md`, the recovery test and result,
watcher status, release inventory/receipt and utility, and off-machine backup
receipts/verifier/upload list when available. Build products and dependency
caches are excluded. Snapshots and release archive directories are never
recursively included. It never edits experiment sources or removes older snapshots.

These are **recovery checkpoints, not proof-completion evidence**. Files are
read sequentially; live logs and receipts can describe different instants.
The manifest records capture times, byte counts, source metadata, and SHA-256
hashes of the bytes actually saved. Dependencies must be restored using the
experiment's pinned reproduction instructions before rerunning Lean.

Each ZIP is verified before publication and read back afterward. Receipts and
`LATEST_CHECKPOINT.json` are published using temporary files, `fsync`, and
atomic replacement. A partial write cannot replace the previous latest
pointer. The ZIP includes the recovery utility and instructions, so the
snapshot is self-contained for restoring its included files; it does not
include the compiler, library caches, or sealed predecessor archives.

```sh
python3 -B /home/richman954/NDEA_Recovery/checkpoint.py --once
python3 -B /home/richman954/NDEA_Recovery/checkpoint.py --watch --interval 60 --hours 12
```

Write `TASK_STATE.json` before taking a checkpoint or starting the watcher.
Its `active_experiment` must name a real direct child of
`NDEA_Evolve_offruntime`, such as `exp012`, or its absolute path. Names must
match `expNNN`; outside paths and symlink experiment directories are rejected.
The watcher takes an
immediate snapshot and another after each interval. It stops after at most
12 hours, on SIGINT/SIGTERM after a final snapshot, or once a snapshot includes
the selected experiment's `evidence/FINAL_PACKET_RECEIPT.json`. A filesystem lock prevents duplicate
watchers. `WATCHER_STATUS.json` reports its PID and eventual stop reason. A
snapshot failure stops the watcher and records failure instead of silently
claiming success. The 12-hour bound is checked between snapshots; one snapshot
already in progress is allowed to finish. A Chromebook shutdown stops the
local watcher; restart it after resuming if the selected experiment is unfinished.

Keep the watch command in a live foreground terminal or a tracked execution
session. A detached child launched through the execution tool on 2026-09-08
did not survive its container; an old PID in `RUN_MANIFEST.json` is not proof
that saving is running. Check for `WATCHER_STATUS.json` and advancing checkpoint
timestamps. If the final packet receipt is already present, one checkpoint
and a normal stop are expected. Take `--once` again after final notes or backup
receipts change. For a later experiment, update `TASK_STATE.active_experiment`
before the first `--once` checkpoint and launch a fresh watcher. The stop marker
is derived from that selection; an older experiment's final receipt does not
stop the new task. Changing the active experiment while a watcher is running
causes it to stop with an explicit error; restart it for the newly selected task.

To inspect the latest saved location and hash:

```sh
cat /home/richman954/NDEA_Recovery/LATEST_CHECKPOINT.json
```

Use the archive and SHA-256 from that pointer or its dated receipt:

```sh
python3 -B /home/richman954/NDEA_Recovery/checkpoint.py --verify /path/to/checkpoint.zip --sha256 SAVED_SHA256
python3 -B /home/richman954/NDEA_Recovery/checkpoint.py --restore /path/to/checkpoint.zip --sha256 SAVED_SHA256 --restore-to /path/to/new-recovery-directory
```

Restoration verifies the archive before writing, rejects unsafe paths,
symlinks and duplicate entries, requires a new destination directory, and
checks every restored payload hash. It does not overwrite an existing
workspace. If this utility must itself be recovered, use a trusted copy or
inspect the archive's code before execution.

Restored task/run manifests retain the original absolute paths and process IDs.
Before resuming in a different location, update the restored `TASK_STATE.json`
to name the restored project/experiment, remap its receipt paths, and discard
old process/session IDs as evidence of a live job. Keep the recovery directory
beside `NDEA_Evolve_offruntime`, as in the archive layout. The selected-experiment
check deliberately rejects references to an unrelated original workspace.

All snapshots here are on the same local filesystem. A second copy on a
different machine or durable storage is separate from this utility.

`make_local_copy.py` prepares a convenience folder under the Chromebook's
`Downloads` directory after the active experiment is sealed and a checkpoint
captures its exact final receipts. The folder contains the preserved Exp001–012
release bundle, the selected current recovery checkpoint, the active review
packet, and every intervening sealed packet from Exp013 through the experiment
immediately before the active one. Thus an Exp014 backup also includes Exp013.
Missing or unaccepted intervening experiments stop publication; gaps are not
silently skipped.

Each supplemental packet is checked against its accepted packet receipt,
including archive SHA-256 and size, ZIP CRC, exact manifest coverage and every
payload hash. Its embedded final verification must exactly match the accepted
external qualification. Exact packet/qualification receipt bytes are copied
beside each supplemental ZIP and checked unchanged before publication. The
generated README, manifest and `LOCAL_BACKUP_RECEIPT.json` enumerate actual
supplemental coverage. Original archives remain unchanged. This coverage is of
the preserved completed packets, not every historical intermediate file.

A live checkpoint watcher may advance `LATEST_CHECKPOINT.json` while this
publisher works. The selected archive and exact captured pointer/dated receipt
remain paired; the publisher never substitutes a later pointer into an earlier
selection. Use the original/restored utility beside the project for future
publication, and use the copies in Downloads only to inspect or restore.
