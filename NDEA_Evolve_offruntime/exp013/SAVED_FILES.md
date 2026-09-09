# Experiment 013 sources, checkpoints and accepted evidence

Read the completion report and actual accepted result receipts before making
a proof claim. During implementation, PLAN.md and the central recovery task
state record pending work. Failed development checks remain preserved.

- `lean/GenericClassical.lean`: generic classical predicate, local density/flux/
  forcing identities, continuity, and subtraction/zero closure.
- `lean/GenericEnergy.lean`: compact domination, differentiation of interval
  mass, exact forcing work balance, homogeneous conservation.
- `lean/GenericUniqueness.lean`: norm-square separation, conserved distance and
  uniqueness from any common time slice.
- `lean/LegacyBridge.lean`: exact equivalence with the previous concrete class,
  regular-data uniqueness and inherited numerical convergence/error.
- `lean/Controls.lean`: exact variable-potential, forcing and period controls.
- `lean/Exp012Foundation.lean`: unchanged retained predecessor proof bodies.
- `lean/Exp013Combined.lean` and `evidence/FINAL_INPUTS.json`: deterministic
  combined source and full new public axiom catalog, generated after freeze.
- `evidence/*_<Module>.json` and neighboring logs: dated development receipts;
  only exact-source passing receipts qualify the modules.
- `attempts/r1/`: preserved first combined attempt, original source deliveries,
  local and remote failure logs, verified downloaded evidence, and earlier
  control/review records. Its unqualified `smul_apply` was ambiguous in the
  combined namespace; accepted final results use the explicitly qualified lemma.
- `evidence/local_combined/RESULT.json`: final local source-only project check.
- `remote_check/downloaded_evidence/`: accepted fresh VM source, bootstrap,
  compiler evidence and dependency manifests after receiving validation.
- `remote_check/FINAL_TRANSFER_CHECK.json`: exact received evidence agreement.
- `REVIEW.md`, `evidence/REVIEW_CHECK.json`, and `INFRASTRUCTURE_REVIEW.md`:
  independent mathematical/source/tool review and its checked inputs.
- `evidence/FINAL_VERIFICATION.json`: final qualification, written only after
  the local/independent/transfer/review gates pass.
- `PACKET_MANIFEST.json` and `evidence/FINAL_PACKET_RECEIPT.json`: sealed
  payload hashes and external checksum/readback receipt.

The final review ZIP is saved under `/home/richman954/` with a neighboring
checksum. Active recovery state, minute snapshots and latest pointers live
outside sealed experiments in `/home/richman954/NDEA_Recovery/`. The user
selected local Chromebook copies; no Google Drive backup is requested.
Completed convenience copies are found in Files → Linux files → Downloads,
with their authoritative current location in `LOCAL_BACKUP_RECEIPT.json`.

The recovery snapshots are not new proof checks and may capture mutable files
at different instants. Explicit milestone snapshots supplement the tracked
watcher. Compile caches are excluded from review and recovery archives.
