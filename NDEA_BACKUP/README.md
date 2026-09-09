# Verified NDEA backup payloads

The exact current coverage is listed in `BACKUP_MANIFEST.json`. A work-in-progress
checkpoint is explicitly marked as such; it is not proof of experiment completion.
Original sealed packets and their receipts retain their exact bytes and meaning.

This branch is a durable off-device copy on GitHub, complementing the separate
source branch and local Chromebook snapshots. It is updated at verified milestones,
not by the minute-by-minute local watcher. Unsaved work and later local results are
not protected by an earlier GitHub commit.

Run from a checkout of this branch:

```sh
python3 -B NDEA_BACKUP/verify_backup.py
python3 -B NDEA_BACKUP/verify_backup.py --restore-to /path/to/new-directory
```

The destination must not already exist. The tool verifies every part and complete
archive SHA-256, then reconstructs the original archive bytes and reads them back.
Some archives may be stored in numbered parts to fit the tool's transfer limits.
Concatenation in manifest order reproduces the original archive exactly; no sealed
packet has been repackaged or edited. This check verifies transport integrity,
not the mathematical validity of a theorem. Use the original proof qualification
receipts and reproduction tools inside the restored packets for that purpose.

For active recovery, use the checkpoint's own `checkpoint.py --verify` and safe
restore instructions after reconstructing its ZIP. Read `START_HERE.md`, task
state, roadmap and actual results. Remap old absolute paths and rebuild excluded
toolchains/caches from their pins. Process IDs, runtime IDs and saved session
names are historical information, not proof that a process survived.

The manifest is bound by the published Git commit; retain its SHA-256 and the
independent remote-readback receipt locally. A commit records content. Accepted
Lean receipts bind exact source to completed checks. Ordinary Git branches/tags
can move; this initial archive branch is not an immutable GitHub release.

The authenticated connector exposes Git objects but no release-asset upload.
This initial archive branch therefore stores only selected compact canonical
packets/checkpoints, excluding the multi-gigabyte compiler/build caches. Future
GitHub releases can carry the same bytes and manifests without changing the
existing evidence chain. The original main branch and history remain intact.
