# Fresh VM recheck: saved files and checkpoints

This is additional evidence for the completed Experiments 001–008. The
original sealed Experiment 008 files and earlier packets remain separate.

## Accepted outcome and complete packet

- [Report](REPORT.md): scope, per-experiment audit counts, compiler results,
  expected rejection controls, numerical rerun, and trust qualifications.
- [Final qualification](FINAL_VERIFICATION.json).
- [Transfer validation](FINAL_TRANSFER_CHECK.json) and
  [three-environment comparison](CROSS_ENVIRONMENT_COMPARISON.json).
- [Complete packet manifest](PACKET_MANIFEST.json). The external
  [packet receipt](FINAL_PACKET_RECEIPT.json) is written after sealing and is
  intentionally outside the ZIP to avoid a self-hash cycle.

## Machine and original-file preservation

- [Fresh VM allocation](VM_ALLOCATION.json) and [initial state](FRESH_VM.json).
- [Original Experiment 008 packet baseline](SEALED_BASELINE.json).
- [Earlier predecessor preservation](PREDECESSOR_PRESERVATION.json).
- [Reused sealed input hashes](REUSED_INPUTS.json).

## Proof and control inputs

- [Retained source scope](AUDIT_SCOPE.md) and
  [all 332 retained public names](ALL_PUBLIC_THEOREMS.json).
- [Historical supplement plan](HISTORICAL_CHECK_PLAN.md),
  [historical input catalog](historical_inputs/HISTORICAL_INPUTS.json), and
  [exact original provenance](historical_inputs/ORIGINAL_SOURCE_INVENTORY.json).
- [Full 473-audit and 13-rejection suite catalog](SUITE_INPUTS.json),
  [upload hashes](SUITE_UPLOAD.json), and
  [uploaded source archive](historical_suite_sources.tar.gz).
- `suite_payload/`: exact upload contents, including the sealed source plus
  the additional audit prints and reconstructed historical check files.
- `historical_inputs/originals/` and `historical_inputs/provenance/`: exact
  accepted historical sources, positive/negative controls, and prior manifests.
- `reused_inputs/`: unchanged original bootstrap, source archive, and verifier
  launch tools, with their source hashes recorded separately.

## Downloaded evidence

- [Fresh exact-source result](downloaded_evidence/recheck_evidence/final_verification/RESULT.json)
  and [compiler log](downloaded_evidence/recheck_evidence/final_verification/combined.log).
- [Supplemental suite result](downloaded_evidence/recheck_evidence/historical_verification/RESULT.json).
  This receipt lists all nine source checks, their logs and source hashes,
  elapsed times, positive audits, and exact negative-control diagnostics.
- [Fresh numerical receipt](downloaded_evidence/recheck_evidence/final_verification/NUMERICAL_RESULT.json)
  and [numerical data](downloaded_evidence/recheck_evidence/final_verification/evidence/numerical_checks.json).
- [Fresh bootstrap result](downloaded_evidence/recheck_evidence/bootstrap/RESULT.json).
  Its 57 command logs, input files, dependency pins, compiler hash, and cache
  fetch evidence are preserved alongside it.
- [Independent archive export receipt](EXPORT_RECEIPT.json): exact archive
  filename, byte size, SHA-256, and complete evidence-manifest hash.

All downloaded evidence lives under `downloaded_evidence/recheck_evidence/`.
The remote evidence archive itself is also retained in this folder.
The larger library caches are excluded from the evidence packet; their full
artifact manifests and recorded before/after checks are retained.

## Reproduction and intermediate checkpoints

- [Reproduction instructions](REPRODUCE.md) and [initial plan](PLAN.md).
- [Intermediate suite checkpoint](checkpoints/SUITE_IN_PROGRESS_20260908T0842Z.json),
  retained before all rejection checks and final artifact checks completed.
- [Source reconstruction](prepare_suite.py),
  [remote source verifier](verify_suite.py),
  [receiving checker](check_download.py), and [packet sealer](seal_recheck.py).
- `TOOLS_UPLOAD.json` identifies the installed version 2 execution tools.
  Version 1's archive and request remain as packaging history; it was not
  installed or used to execute checks. The change corrected export coverage
  for extensionless historical input files.

Prepared-input documents retain their original checkpoint wording. The final
report and qualification determine the completed verification status. Expected
rejection logs intentionally contain compiler errors and are distinguished
from the successful production/control proof logs in the final receipts.
