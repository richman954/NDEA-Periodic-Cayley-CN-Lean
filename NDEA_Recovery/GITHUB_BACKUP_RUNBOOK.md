# NDEA GitHub and Chromebook backup runbook

Recorded September 9, 2026 UTC. Read `START_HERE.md`, `TASK_STATE.json`,
`RECOVERY_POLICY.md`, the central resume notes, and actual receipts before
continuing. Receipt timestamps and exact contents take precedence over older
progress summaries. This file documents recovery; it does not extend the
mathematical task.

## Authorized destination and recorded coverage

The user explicitly authorized the existing **public** repository
[`richman954/NDEA-Periodic-Cayley-CN-Lean`](https://github.com/richman954/NDEA-Periodic-Cayley-CN-Lean)
for backups alongside local Chromebook copies. Public upload to this destination
is authorized; it is not an inference from repository visibility. Google Drive
backup remains canceled. Do not mount Drive or substitute another destination.

The original `main` is preserved at
`15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c`. These are additive backup branches;
the original release files and history were not replaced.

| Purpose | Branch | Recorded commit |
| --- | --- | --- |
| Sources, tools, documentation, selected receipts | `backup/ndeaevolve-20260909` | `2a4028add0c09e7e8445e8f6886a965cd2573ac0` |
| Exact packets, Git bundles, and recovery checkpoint | `backup/verified-milestones-20260909` | `ba4cd8d2275e13e812bd566bf5091f219fab1a79` |

The source commit has original `main` as its parent and tree
`252ca564f70e9d4772c920cd85338f605d80f4a4`. Fresh network readback passed at
03:15:45 UTC: all **1,093 uploaded files / 15,290,025 bytes** matched their
SHA-256 and sizes, original files were unchanged, and `git fsck --full` passed.
The decisive record is
`/home/richman954/NDEA_GitHub_Backup/SOURCE_REMOTE_READBACK.json`.

The source backup includes cumulative Exp001–005 source from the Exp005
checkout, selected Exp006–014 code and evidence, and Exp015/recovery files from
the fixed **02:50:20 UTC work-in-progress checkpoint**. The selected workspace
paths are retained under `NDEA_Evolve_offruntime/` and `NDEA_Recovery/`.
The original independent Exp001–005 Git histories are preserved separately in
their original bundles; copying their source files does not merge that ancestry
into the public repository's history.

The archive manifest lists **15 original archives**: the completed Exp001–012
release bundle, sealed Exp013 and Exp014 packets, 11 history bundles, and the
Exp015 work-in-progress checkpoint. It also binds companion receipts and
instructions. The archive branch uses `NDEA_BACKUP/` as its payload directory.
Publication is recorded in `logs/ARCHIVE_COMPLETE_PUBLICATION.json`; that
publication receipt alone explicitly does **not** establish remote readback.
The subsequent `ARCHIVE_REMOTE_READBACK.json` passed at **03:19:53 UTC**:
39 remote files matched, all 15 original archives totaling 63,732,217 bytes
were reconstructed, all 95 working-checkpoint payloads were restored and
rehashed, and the original 66 main files and Git integrity checks passed.
It independently checked the original receipt bindings and ZIP CRC/manifests;
the published restore checker was also run as an additional check. The archive
commit tree is `c549d2424caf15d9ddbc07f830526ca1513738ad`.

The initial GitHub snapshots do not include later Exp015 freeze, combined
verification, or final sealing. A **sealed Exp015 refresh remains pending**.
Current local proof status may be newer: the local combined check passed 50
audits, but only the actual independent-transfer and final-packet receipts can
establish later qualification and sealing. A source commit, branch, tag, backup
check, or CI badge does not establish a Lean theorem's qualification.

## Where the exact inputs and records live

All paths below are under `/home/richman954/NDEA_GitHub_Backup/` unless stated.

| Record or directory | Meaning |
| --- | --- |
| `integration/` | Initial source staging clone; preserves public history |
| `stage_sources.py` | Initial, fixed-checkpoint staging program; refuses overwrites; not a generic future-sync command |
| `SOURCE_CANDIDATES.json` | 1,091 original selected paths with origin, bytes and SHA-256 |
| `SOURCE_CANDIDATE_REVIEW.json` | Exact candidate byte and credential-pattern review |
| `SOURCE_UPLOAD.json` | 1,093 uploaded paths, including the source manifest and backup status document |
| `source_batches/`, `logs/SOURCE_TREE_UPLOAD.json` | Source Git-object transport batches and returned identifiers |
| `logs/SOURCE_PUBLICATION.json` | Source branch/commit publication response; later readback supersedes its initial unchecked status |
| `source_readback_root/` | Successful fresh network source clone |
| `SOURCE_REMOTE_READBACK.json` | Successful source commit, parent, file-hash and Git-integrity readback |
| `logs/SOURCE_ROOT_CLONE.log`, `logs/SOURCE_ROOT_*.log` | Complete successful source clone and local verification command output |
| `archive_stage/` | Exact archive parts, manifest, companion receipts, restore checker and instructions |
| `ARCHIVE_UPLOAD.json` | 39 uploaded archive/companion paths with SHA-256, size and Git blob identifier |
| `archive_tree_elements.json` | Prepared archive Git-tree entries |
| `logs/ARCHIVE_BLOB_UPLOAD.json` | Archive blob upload responses |
| `logs/ARCHIVE_INITIAL_PUBLICATION.json`, `logs/ARCHIVE_COMPLETE_PUBLICATION.json` | Initial and completed archive branch publication records |
| `archive_readback_root/`, `logs/ARCHIVE_ROOT_CLONE.log` | Successful fresh archive readback clone and its full clone output |
| `ARCHIVE_REMOTE_READBACK.json`, `archive_readback_logs/` | Successful independent archive/receipt/restore checks and complete command output |
| `archive_restored/Exp015_CHECKPOINT_FILES/` | Actual 95-payload restoration from the downloaded WIP checkpoint |
| `RELEASE_ASSET_REVIEW.json`, `RELEASE_ASSET_CONTENT_INVENTORY.json` | Reviewed original archive contents and Git-bundle history inventory |
| `logs/BACKUP_RESTORE_TEST.json`, `logs/BACKUP_RESTORE_TEST.log` | Local restore/corruption-control results and full output |

Keep failed attempts as historical evidence. The initial restricted-network
source clone failed DNS resolution; its saved records are
`source_readback_clone.log.network_failure_1` and
`SOURCE_REMOTE_READBACK.json.network_failure_1`. The successful source receipt
uses `source_readback_root/`, not the abandoned `source_readback/` destination.
Do not rerun the initial fixed-destination `verify_source_remote.py` blindly.

The source manifest SHA-256 is
`0027795707573837cb735c6a235710286099b36a27a244b9b7c3e5f6f0b3239f`;
the source upload manifest SHA-256 is
`7facfd9f69a597cb6de11cd69bc20cef81dd6a7ee238ea7c86c2a9a25450f3f0`.
The initial `archive_stage/BACKUP_MANIFEST.json` SHA-256 is
`54434c6778b0d4a906725b6fc96739236da1969790d4aedd221d467b78747be4`.

## Recover into new directories

Use new, nonexistent destinations. For the recorded source snapshot:

```sh
git clone --branch backup/ndeaevolve-20260909 --single-branch https://github.com/richman954/NDEA-Periodic-Cayley-CN-Lean.git /home/richman954/NDEA_Restore_Source_20260909
git -C /home/richman954/NDEA_Restore_Source_20260909 checkout --detach 2a4028add0c09e7e8445e8f6886a965cd2573ac0
git -C /home/richman954/NDEA_Restore_Source_20260909 fsck --full
```

Check its commit/tree against the external readback receipt and verify every
manifest file's SHA-256 and length. `git fsck` complements these checks; it does
not replace the independently recorded SHA-256 manifest.

For the recorded archive snapshot:

```sh
git clone --branch backup/verified-milestones-20260909 --single-branch https://github.com/richman954/NDEA-Periodic-Cayley-CN-Lean.git /home/richman954/NDEA_Restore_Archives_20260909
git -C /home/richman954/NDEA_Restore_Archives_20260909 checkout --detach ba4cd8d2275e13e812bd566bf5091f219fab1a79
git -C /home/richman954/NDEA_Restore_Archives_20260909 fsck --full
python3 -B /home/richman954/NDEA_Restore_Archives_20260909/NDEA_BACKUP/verify_backup.py
python3 -B /home/richman954/NDEA_Restore_Archives_20260909/NDEA_BACKUP/verify_backup.py --restore-to /home/richman954/NDEA_Restored_Packets_20260909
```

The restore checker verifies part hashes, concatenates parts in **manifest
order**, verifies each complete archive hash, and reads restored bytes back.
Numbered parts are a transport representation of the original ZIP/bundle;
concatenation restores unchanged original bytes. Do not unzip individual parts
or rebuild a replacement ZIP from extracted files. Restore targets must not
already exist, and their parent directory must exist.

For the initial Exp015 recovery ZIP, the trusted SHA-256 is
`81a5b7d1d808c5d52eaa9b49436b6e2b655540fe1bf489f95e56793aa3faeaf6`.
Use the recovery utility's documented `--verify ARCHIVE --sha256 HASH`, then
`--restore ARCHIVE --sha256 HASH --restore-to NEW_DIRECTORY`. Verify original
packet manifests/receipts separately and read their reproduction instructions.
Retain all restored Git bundles: later bundles can retain ancestry while earlier
bundles preserve additional historical refs and milestone tags.

Restored metadata and scripts retain historical absolute paths. Remap paths to
the new workspace before running tools; restore pinned toolchains/dependencies
separately. Saved PID, Colab VM, boot and session identifiers are historical
provenance, not credentials and not evidence that a runtime survived. Colab is
temporary computation, not the durable backup destination.

If a necessary public clone fails with sandbox DNS/network errors, inspect and
save its actual stderr, then retry the **direct `git clone` command** using the
approved network permission path. Report a pending approval or rejection
promptly. Do not silently wait on an unstarted wrapper or create duplicate
clones while another download is running.

## Local saving and future GitHub milestones

Local saving continues under `RECOVERY_POLICY.md`: explicit verified
`checkpoint.py --once` saves before long operations and after meaningful
milestones, with an optional tracked 60-second watcher during sustained work.
Verify startup and an advancing interval snapshot. The watcher is bounded,
stops when it captures the selected experiment's final-packet receipt, and is
not restarted automatically after reboot. GitHub uploads are **milestone
operations**, not a minute-by-minute daemon. Later unsent changes remain local.

For a future update to both backup branches:

1. Finish the authorized milestone, inspect actual qualification/packet receipts,
   update status and the central notes, then publish and verify a fixed local
   checkpoint. Choose that exact archive/hash as the active-workspace source.
   Do not build a milestone from files changing while copied.
2. Prepare new dated staging/manifests from the fixed checkpoint and immutable
   sealed predecessors. Preserve exact source/packet bytes and original history.
   Label an unfinished checkpoint as WIP. Include the new sealed packet only
   after its actual final receipt exists. Review exact selected files and all
   newly included archive/history content before public transfer.
3. Publish additive Git objects/commits to the appropriate backup branches,
   retaining the previous commits and original `main`. Record returned blob,
   tree, commit and ref identifiers; do not force-rewrite old milestones.
4. Independently fetch/clone the recorded remote commits into new directories.
   Verify all source hashes, archive parts and reconstructed archives, original
   main-file preservation, and normal Git integrity. Preserve full stdout/stderr
   and write explicit successful readback receipts before claiming coverage.
5. Record the exact covered checkpoint/packet/commit hashes in task state and
   the backup receipt, take a final verified local checkpoint, and refresh the
   Chromebook convenience copy with `make_local_copy.py` when its sealed-packet
   prerequisites hold. Keep both destinations and dated earlier copies.

Filesystems and Git have different roles: local snapshots protect ongoing work;
Git records selected source history; archive backups retain exact release and
recovery payloads; Lean/compiler and independent-transfer receipts establish
which exact proofs were checked. Qualify each claim at its own level.

## Authenticated transport and hash binding

The connected GitHub app is already authenticated and exposes blob, tree,
commit and ref operations. The current route does not require the user to
provide a token. The installed connector has no release-asset upload tool, so
the initial archive backup uses its separate branch. This is not a GitHub
Release. The same verified bytes can later be attached to Releases through an
authorized available API without rewriting the old evidence.

At inspection, `gh` and local shell Git write credentials were absent; public
clone success establishes read access only. Do not assume a shell push or
release API is authenticated, and do not extract or print account secrets.

The tool-output transport was observed to cap a returned output at **512 KiB**.
When moving file bytes from a shell tool into the orchestration layer, use
**196,608-byte raw chunks**: each becomes 262,144 base64 bytes before its small
wrapper. Assemble in explicit offset order and verify total length and SHA-256
before creating a blob. These transport chunks are distinct from the stored
archive parts, which are up to 4 MiB. Never accept a silently truncated tool
result. Preserve structured API responses and full command logs.

Payload manifests contain SHA-256 and sizes; Git records their exact bytes in
a tree/commit. An **external publication/readback receipt** records the
manifest SHA-256, remote commit/tree and verification outcome. It does not try
to contain its own checksum or the identifier of a commit that contains that
same final receipt. Later receipts can bind earlier immutable commits. This
avoids a self-hash cycle and preserves sealed packet bytes. Branch names can
move; retain exact commits and external hashes.

Exclude account credentials, OAuth tokens, private keys and unrelated home
files; compiler caches, `.lake/`, dependency closures, generated `.olean*`,
`.ilean` and `.ir` artifacts; repeated runtime bulk and multi-gigabyte duplicate
archives. Preserve useful original source, tools, pins, tests, documentation,
accepted receipts and reviewed historical evidence. Session/boot identifiers
in qualification receipts may remain as provenance; they provide no login.

## Checkpoint metadata coverage fixed and tested

The metadata fix was applied after the Exp015 watcher stopped normally at
03:30:31 UTC. `checkpoint.py` now requires and captures the workspace
`AGENTS.md`, includes `GITHUB_BACKUP_RECEIPT.json` and this runbook, and captures
the explicitly staged `NDEA_Recovery/github_evidence/` subtree. That subtree
accepts only regular UTF-8 `.json`, `.log`, `.md`, `.py`, `.txt` and `.sha256`
files, each at most 2 MiB; symlinks and unrelated staging/clone directories are
excluded or rejected. The whole `NDEA_GitHub_Backup/` directory is not copied.

The actual workspace recovery test passed at **03:32:32 UTC**: all **282
payloads** were verified and restored, including exact bytes and hashes for
**44 startup/GitHub metadata files**. Existing corruption, unsafe-path and
task-selection controls passed, as did rejection of evidence-file symlinks,
directory symlinks, archive files, oversized files and invalid UTF-8.

Read `RECOVERY_TEST_RESULT.json` and
`github_evidence/RECOVERY_METADATA_FIX_RESULT.json`; complete actual test output
is preserved in `github_evidence/logs/RECOVERY_METADATA_FIX_TEST.log`. The
updated utility SHA-256 is
`70aeeb67bdae5880944c3256f8758bac6425d187fa4562c02adc10028d94b0b0`,
and the updated test SHA-256 is
`446e12400cece679f18a152d5f4d1a39e7cf19555b413ef96a750d841c17d266`.
A subsequent explicit checkpoint captures the completed test record, this
updated runbook, the full test log and metadata summary. Its dated receipt and
`LATEST_CHECKPOINT.json` identify that later archive.

Earlier ZIPs retain their original coverage. `make_local_copy.py` also copies
`AGENTS.md` separately as `NDEA_STARTUP_INSTRUCTIONS.md`, and the initial archive
branch carries that file, but neither fact retroactively changes an old ZIP.
Final sealed Exp015 source/archive refresh and the final local Chromebook copy
must record their actual later coverage.
