
# Local Chromebook intake reconciliation

This intake was additive and never changed Experiment 001's mathematical inputs.
The research assets were not executed, imported, parsed as proof data, or used to
launch another mission.

Initial intake state:

- local inbox: `/home/richman954/NDEA_Inbox`
- initial inventory: `metadata/local_asset_intake_inventory.json`
- initial SHA manifest and verification: `metadata/local_asset_SHA256SUMS` and
  `metadata/local_asset_SHA256SUMS_verify.txt` — 17/17 PASS
- original note: `metadata/local_asset_intake_note.md`

Append 001 resolved the five requested originals:

- outer archive size: `6995572` bytes
- outer SHA-256: `6a24f7ff1cefc961876d70ee406c5fb67c1026765750b97c0a855cdfddff5ebf`
- append manifest: `metadata/local_asset_SHA256SUMS_APPEND_001`
- append verification: `metadata/local_asset_SHA256SUMS_APPEND_001_verify.txt` — 12/12 PASS
- six-entry inner manifest: 6/6 PASS
- receipt: `metadata/local_asset_missing_inputs_receipt.json`
- append-only note: `metadata/local_asset_intake_note_append_001.md`

The nested QGI archive remains unopened, at SHA-256
`1ff66d3d9258f8d9c24034ba7327f631a56f4c66ed5e6c99f9299877f9bb91f6`. The three geometry transcripts are
byte-identical copies at SHA-256
`636269e40717f3e60b1969340ad71c230956eb753c8fccebb1abf49a7ed9c525` and count as one content object,
not three independent evidence sources. No legacy restore or historical transcript
instruction was executed.

Canonical-name mapping for the intake addendum:

- inventory report → `metadata/local_asset_intake_inventory.json`
- original path/hash table → `metadata/local_asset_original_paths_sha256.tsv`
- unresolved table → `metadata/local_asset_missing_inputs.tsv`
- resolved append table → `metadata/local_asset_missing_inputs_resolved.tsv`
- extraction/path-safety report → `metadata/local_asset_zip_validation.json`
- missing-input receipt → `metadata/local_asset_missing_inputs_receipt.json`
- remote transfer cross-check → `metadata/local_intake_remote_receipt.json`
