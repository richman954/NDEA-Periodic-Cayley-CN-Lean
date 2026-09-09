# NDEA development backup

This additive branch preserves the original public repository history and a
selected source/evidence snapshot through the Exp015 work in progress captured
at 2026-09-09 02:50:20 UTC. Exp014 is sealed. All seven Exp015 modules passed
separately at this snapshot; its final combined and fresh-runtime qualification
and sealing were still pending. Later receipts must establish any later status.

`NDEA_GITHUB_SOURCE_MANIFEST.json` binds every imported file to its SHA-256,
size and workspace or checkpoint provenance. The Git commit identifies these
bytes; the original accepted proof receipts identify what was verified.
Neither the presence of a file nor this backup commit is a fresh Lean check.

The layout preserves workspace-relative source paths. Start with
`NDEA_Recovery/START_HERE.md`, then task state, roadmap and actual proof receipts.
Machine-specific absolute paths and old session IDs are historical; remap paths
on a new machine. Rebuild excluded dependencies and compiler caches from the
preserved pins and reproduction instructions. This is not a copy of the whole
Chromebook or its credentials.

The separate `backup/verified-milestones-20260909` branch is reserved for exact
sealed experiment archives and checkpoint payloads, with SHA-256 manifests and
readback verification. Its actual manifest determines the currently uploaded
coverage. A source checkout alone does not establish that those archives were
uploaded. Local Chromebook snapshots and milestone copies remain in use.

This initial backup uses authenticated Git object operations. GitHub release
asset upload is not exposed by that connector; immutable release publication
can be added later. Keep sealed packet bytes and original receipts unchanged.
