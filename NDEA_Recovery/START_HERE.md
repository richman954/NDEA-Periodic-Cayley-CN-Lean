# Resume the NDEA work

Start with the saved files, even if the previous chat is unavailable.

GitHub backup update, September 9, 2026 UTC: the user now authorizes the
existing public `richman954/NDEA-Periodic-Cayley-CN-Lean` repository as an
additional backup destination. Read `GITHUB_BACKUP_RECEIPT.json` and
`GITHUB_BACKUP_RUNBOOK.md` for verified coverage and recovery commands. The
source branch is `backup/ndeaevolve-20260909`; exact archive payloads are on
`backup/verified-milestones-20260909`. Local Chromebook copies continue.
GitHub updates occur at meaningful source checkpoints and verified milestones; the local minute watcher does
not automatically push them. A Git commit records source bytes, while original
proof receipts establish which source passed which checks. Google Drive remains
canceled. If recovering without this Chromebook, begin at the repository's
archive branch and its `NDEA_BACKUP/README.md` and manifest.

Current accepted milestone: Exp015 is complete and sealed (50 local and independent
audits). Its source, packet and recovery checkpoint are now readback-verified on
GitHub. The clean development branch is `dev/variable-potential`; preserve main.
Exp016 is now the authorized active experiment; read its PLAN.md and task state. Read the latest receipts for exact commit/coverage.

1. Read `TASK_STATE.json` in this directory, then
   `/home/richman954/NDEA_Evolve_offruntime/RESUME_STATUS.md` and
   `/home/richman954/NDEA_Evolve_offruntime/WORKING_ROADMAP.md`.
2. Read the result receipts for `TASK_STATE.active_experiment`. A task-state
   note or recovery ZIP is not a fresh proof check. Inspect that experiment's
   `evidence/local_combined/RESULT.json`, the independent result and transfer
   receipt named in `TASK_STATE.json`, and `evidence/FINAL_PACKET_RECEIPT.json`
   if it exists. Exp016 is the active extension. Exp013–015 are sealed and immutable;
   their receipts cannot establish completion of Exp016.
3. Check for a completed review packet and its checksum before repeating work.
   Preserve sealed experiments and frozen proof sources. Resume the remaining
   work recorded in the central notes; check receipt timestamps when an older
   task-state entry still lists work that has since finished.
4. Inspect `LATEST_CHECKPOINT.json` for the latest recovery archive, SHA-256,
   publication time, and dated receipt. See `README.md` for verification and
   safe restoration into a new directory. Do not restore over the workspace.

The checkpoint ZIP includes the selected experiment's files, central notes,
task/run state, recovery instructions/utilities and available backup receipts.
It excludes compiler/build caches and sealed predecessor packets; the separate
release inventory identifies their preserved bundle. Snapshot/archive directories
are not recursively included. A restored task manifest keeps original absolute
paths: remap those to the restored project before resuming, and do not treat old
PIDs or session IDs as evidence that processes survived.

## Saving while work continues

Follow [RECOVERY_POLICY.md](RECOVERY_POLICY.md). For an unfinished experiment,
update `TASK_STATE.json`, take a `--once` snapshot, then launch:

```sh
python3 -B /home/richman954/NDEA_Recovery/checkpoint.py --watch --interval 60 --hours 12
```

Keep this command in a live foreground terminal or a tracked long-running
execution session. In a tool-driven session, retain the returned session ID
and poll it. The attempted detached child on 2026-09-08 did not survive its
execution container; its `RUN_MANIFEST.json` PID alone did not establish a
running watcher. The user-service bus was inaccessible from that environment.

Confirm that `WATCHER_STATUS.json` appears and the latest checkpoint timestamp
advances. If the task remains active, confirm a second checkpoint after one
interval. On an error, inspect the command output and status; take `--once`
snapshots manually until saving is working. A reboot ends the local process.

The utility selects the experiment from **`TASK_STATE.active_experiment`**.
Only real direct project children named `expNNN` are permitted. It stops normally
after a snapshot contains the selected experiment's final packet receipt.
An already completed Experiment 012 therefore produces one snapshot and exits.
For a later experiment, set its own `active_experiment` in task state before
the first checkpoint and start a new watcher. Its stop marker will refer to
that experiment, so Experiment 012's older receipt cannot end the new run.
If the selected experiment changes during a running watch, the watcher fails
explicitly and must be restarted. No watcher is automatically restarted at boot.

After final reports, task state, or backup receipts change, take an explicit
checkpoint so those later updates are preserved:

```sh
python3 -B /home/richman954/NDEA_Recovery/checkpoint.py --once
```

These saves are local. The user explicitly chose to keep copies on the
Chromebook and canceled the Google Drive backup. Do not mount Google Drive or
resume that transfer unless the user asks again. There is no pending cloud
backup task. Read `LOCAL_BACKUP_RECEIPT.json` for the verified Downloads folder.
The ChromeOS main Downloads folder is not shared with this Linux environment;
find the copies under Files → Linux files → Downloads.

## A short message for a new chat

> Resume the NDEA project from `/home/richman954/NDEA_Recovery/START_HERE.md`.
> Read the task state, central resume notes, roadmap, and actual result receipts.
> Preserve sealed experiments, identify completed work before rerunning it,
> and continue the recorded remaining work. Verify recovery saving at the start
> and take a final checkpoint after updating the notes. Use backup receipts to
> distinguish verified local copies from off-machine storage.
