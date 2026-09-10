# Recovery policy for future sessions

Read this policy with `START_HERE.md` whenever resuming the NDEA work. These
instructions govern recovery handling; they do not authorize new mathematical
scope, publication, network destinations, or edits to sealed proof sources.

1. Before long-running work, read the task state, central resume notes and
   roadmap, and the actual result/packet receipts. Identify completed work and
   preserve frozen sources. Update `TASK_STATE.json` atomically to name the
   authorized active experiment and the remaining steps.
2. Set `active_experiment` to the direct project child `expNNN` or its absolute
   path. Take an explicit `checkpoint.py --once` snapshot before a long check,
   transfer, or packaging operation. Check the command's exit status and the
   newly published `LATEST_CHECKPOINT.json` timestamp and archive hash.
3. During sustained work, optionally run `--watch --interval 60 --hours 12` in
   a tracked foreground execution session. Verify startup status and an advancing
   checkpoint timestamp; while work remains active, observe another checkpoint
   after an interval. A PID record alone does not demonstrate a surviving process.
4. After each meaningful milestone, update task state and central notes and
   run `--once` again. Do this after final packet creation and after backup
   receipts arrive, even if a watcher is present. Never rely on a daemon alone.
5. Preserve dated local snapshots and verified Chromebook copies. The user
   explicitly canceled Google Drive backup; do not mount Drive, resume its
   transfer, or treat a cloud copy as pending unless newly requested. Any
   historical Colab receipts remain historical evidence of those transfers.
6. On restart, inspect the newest receipts and archive before restarting work.
   Restore into a new directory, remap absolute paths in the restored task state,
   and launch a new watcher only if useful. Old session IDs/PIDs may be stale.

The watcher stops on the selected experiment's final packet receipt, an explicit
stop signal, or its duration limit. For a new experiment, change task state and
start a fresh watcher; the old experiment's completion marker is not reused.
There is no automatic reboot service. Failure of a background process must not
prevent explicit milestone snapshots.

Checkpoint qualification is always **recovery copy, not proof-completion
evidence**. Files are captured sequentially and can describe different instants.
Only actual checked proof/result receipts support proof-completion claims.

## User development principles, September 9, 2026 UTC

Choose the next rigorous, verifiable step for maximum useful proof-space
opened. Prefer reusable lemmas, estimates, representations and verification
interfaces that remove shared bottlenecks, reconnect earlier branches and
strengthen the link to actual numerical definitions. Compare plausible moves
by those concrete benefits, feasibility and proof cost. Do not weaken rigor,
silently strengthen assumptions, substitute numerical tests for proofs, or
present proposed generalizations as established. The stated PDE convergence
objective is now explicit; older notes about a pending choice of project
branch are historical.

At major milestones report: (1) barrier removed, (2) doors opened,
(3) best next move and why, (4) next barrier, (5) recovery state. Distinguish
mathematical acceptance, independent qualification, source version history,
verified local copies and actual durable off-device coverage.

The user requested read-only inspection and a clean Git/GitHub architecture
proposal before disruptive repository changes. Preserve existing history and
sealed packet bytes. A commit identifies source; verification receipts identify
which exact source passed which checks. Tie these by hashes without treating
a commit, tag, CI badge or release attestation as a mathematical proof.
Existing public repositories do not imply authorization to publish new work.

## Terminal visibility and efficient execution

Important proof, build, audit, recovery, Git/GitHub and Colab operations must
have visible meaningful status and decisive results, not only collapsed
background-terminal previews. Prefer foreground execution when practical.
For significant long operations preserve complete stdout/stderr in clearly
named logs (or the existing complete evidence logs/receipts). Inspect logs
from foreground commands at meaningful changes; do not poll merely for
reassurance or delay expensive proof work to mirror repetitive output.

Explain what is running, why, its meaningful current status, and its final
result. On completion surface exit status, errors/warnings, theorem/test/audit
counts, source-unchanged checks and applicable hashes/receipts, with a link to
the full log. Distinguish running, failed, warning-only success, incomplete or
stale evidence, and independent verification. Read the decisive actual output;
do not replace it with an unsupported success summary. If displayed output was
truncated, say so and give its retained log path. Use tee or equivalent logging
when useful. Preserve computation throughput while retaining complete evidence
and enough visible observability to understand every important state change.

For short authorized network-client operations, prefer a direct command using
its established approval prefix. Preserve its complete tool-returned output in
a named log immediately afterward. Shell wrappers/redirection can require a
new approval despite an existing direct-command rule and may stall progress.
The expensive remote compiler/bootstrap must still retain complete logs while
running. This is the user's performance-aware observability compromise, not a
reason to evade an approval or omit decisive evidence.

GitHub backup authorization update: the user explicitly authorized using the
existing public `richman954/NDEA-Periodic-Cayley-CN-Lean` repository for backups
alongside local Chromebook copies. Preserve history, use additive changes and
review exact upload contents. Verify remote source/assets by readback before
claiming current off-device protection. This supersedes the earlier inspection-
only limit for this destination; it does not authorize Google Drive backups.

## Git source cadence and development layer

Keep August 30 main unchanged. Use dev/variable-potential for curated source,
tooling, tests, pins, derivations and compact meaningful receipts; retain exact
large archives on the dedicated backup branch. Preserve receipt-bearing logs
intentionally instead of blanket *.log exclusions. Take Git checkpoints after
meaningful source progress, before risky refactors and after milestones. Reduce
push frequency if it interferes with research; local snapshots remain frequent.
Never move a published verified tag. Bind new Git metadata to original accepted
source/receipt SHA-256 values without modifying sealed evidence to add a commit.

## Universal continuation update, September 10, 2026 KST

Recover the newest intact accepted work and drafts together; discovery anchors
and historical experiment numbers do not override newer source-bound evidence.
Retain healthy watchers/jobs. Reconcile bytes before selective restoration and
preserve current material before replacing anything. Do not rerun accepted
checks merely after a reboot. Network failure is not local proof corruption.

The user explicitly requests persistent forward progress. After recovery and
each intermediate milestone, continue the highest-value unfinished dependency
with a concrete consumer while safe authorized work remains. Ordinary proof,
API or infrastructure failures require diagnosis and a changed useful attempt,
not another authorization. Preserve rejected drafts; use a small representative
probe before repeating an expensive check when practical. Never weaken the
target, change pins, edit sealed bytes or bypass qualification to show progress.
Finish and qualify a natural milestone before extending its scope indefinitely.

Keep a compact current job register and blocker/opportunity ledger in task
state. Give commands, IDs, environment, source identity, log/receipt paths and
observed status for significant jobs; distinguish unavailable remote inspection
from no jobs. Account for surviving jobs at handoff. Use KST first and UTC in
parentheses for human timestamps. Bookkeeping protects mathematical progress;
perform it at natural boundaries and reuse established evidence.
