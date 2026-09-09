# Experiment 008 saved-file guide

This guide identifies the accepted result and the retained development history.
The complete file-by-file checksum inventory is [PACKET_MANIFEST.json](PACKET_MANIFEST.json).
The external [packet receipt](evidence/FINAL_PACKET_RECEIPT.json) records the
review ZIP, its checksum, and its read-back verification. That receipt is
written after sealing and is intentionally outside the ZIP.

## Accepted result

- [Completion report](COMPLETION_REPORT.md): proved endpoint, assumptions,
  controls, final checks, and scope.
- [Final qualification](evidence/FINAL_VERIFICATION.json): accepted source,
  theorem counts, both combined results, and matching modular receipts.
- [Mathematical derivation](MATHEMATICAL_DERIVATION.md) and
  [reproduction instructions](REPRODUCE.md).
- [Implementation and verification review](REVIEW.md).
- [Convergence figure](evidence/exp008_convergence.png) and
  [numerical diagnostic data](evidence/numerical_checks.json).

## Proof sources

| Source | Role |
|---|---|
| [Exp007Foundation.lean](lean/Exp007Foundation.lean) | Exact frozen predecessor combined proof; its pin is in [FOUNDATION_PIN.json](evidence/FOUNDATION_PIN.json). |
| [FrequencyBounds.lean](lean/FrequencyBounds.lean) | Signed-frequency symbol estimates and cutoff-dependent consistency bounds. |
| [ContinuumModes.lean](lean/ContinuumModes.lean) | Actual finite-superposition PDE and orbit properties. |
| [FourierGrid.lean](lean/FourierGrid.lean) | Integer-frequency lifts and wrapped-grid Cayley intertwining. |
| [Orthogonality.lean](lean/Orthogonality.lean) | Aliasing criterion, discrete orthogonality, and weighted Parseval. |
| [SuperpositionClosure.lean](lean/SuperpositionClosure.lean) | Full-grid error with arbitrary initialization and fixed-band mesh convergence. |
| [StageBridge.lean](lean/StageBridge.lean) | Actual factor residual decomposition and full-grid stage budget. |
| [Controls.lean](lean/Controls.lean) | Seven exact controls. |
| [Exp008Combined.lean](lean/Exp008Combined.lean) | Complete re-elaboration source with all 90 new public audits. |

The combined source and every constituent are pinned in
[FINAL_INPUTS.json](evidence/FINAL_INPUTS.json). [make_combined.py](make_combined.py)
reconstructs the complete source and audit catalog. The exploratory
[OrthogonalityProbe.lean](lean/OrthogonalityProbe.lean) is retained as history
and is excluded from the production source and accepted theorem count.

## Verification and transfer evidence

- [Local combined result](evidence/local_combined/RESULT.json),
  [compiler log](evidence/local_combined/combined.log), and
  [external artifact hashes](evidence/local_combined/DEPENDENCY_ARTIFACTS.json).
- [Independent combined result](remote_check/downloaded_evidence/exp008_independent_evidence/final_verification/RESULT.json),
  [compiler log](remote_check/downloaded_evidence/exp008_independent_evidence/final_verification/combined.log), and
  [external artifact hashes](remote_check/downloaded_evidence/exp008_independent_evidence/final_verification/DEPENDENCY_ARTIFACTS.json).
- [Cross-environment comparison](evidence/CROSS_ENVIRONMENT_DEPENDENCIES.json).
- [Upload receipt](remote_check/FINAL_UPLOAD.json),
  [independent export receipt](remote_check/EXPORT_RECEIPT.json), and
  [validated transfer receipt](remote_check/FINAL_TRANSFER_CHECK.json).
- [Final predecessor preservation](evidence/PREDECESSOR_PRESERVATION.json)
  and [initial predecessor baseline](evidence/PREDECESSOR_BASELINE.json).

The accepted local and independent modular receipt paths are listed in
`FINAL_VERIFICATION.json`. Dated local logs and receipts remain in `evidence/`.
Independent bootstrap commands, module attempts, frozen source snapshots, and
figures are retained under
`remote_check/downloaded_evidence/exp008_independent_evidence/`.
The independent archive's exact filename and SHA-256 are in its export receipt.

## Retained checkpoints and tools

- [Original acceptance plan](PLAN.md), [progress checkpoints](STATUS_PROGRESS.md),
  and [pre-final report draft](COMPLETION_REPORT_DRAFT.md).
- [Failure and repair log](FAILURE_AND_REPAIR_LOG.md), including dated failed
  attempts and the accepted replacements.
- [Expired-runtime recovery record](evidence/REMOTE_RECOVERY.json).
- `remote_check/`: bootstrap inputs, launch/status/export/check scripts,
  source-upload archives, and corresponding request hashes.
- [run_lean.py](run_lean.py), [verify_combined.py](verify_combined.py),
  [finalize_verification.py](finalize_verification.py), and
  [seal_packet.py](seal_packet.py): modular compilation, combined checking,
  final evidence qualification, and checksum-verified packaging.

Historical failed logs can contain compiler errors or failed axiom output;
they are retained for provenance and do not determine acceptance. The final
qualification selects successful receipts whose hashes match the final source.
Build caches are excluded from the review packet.

The earlier Experiments 001–007 recap and searchable file inventory remain in
`../recap_001_007_20260908/`; predecessor review archives remain beside the
project workspace in `/home/richman954/`.
