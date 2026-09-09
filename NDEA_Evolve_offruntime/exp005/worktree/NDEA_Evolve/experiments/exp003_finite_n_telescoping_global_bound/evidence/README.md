# Experiment 003 Step 4 evidence

This directory is separate from all predecessor evidence and records only the
finite-`N` telescoping identity, global operator-norm bound, and focused
controls.

Qualifying evidence:

- `logs/combined_controls_attempt_005.log` and
  `receipts/combined_controls_attempt_005_20260907.json`: independent combined
  production/control verification, exit code 0;
- `logs/modular_verification.log` and
  `receipts/modular_verification_20260907.json`: traced, serial,
  module-by-module verification, exit code 0;
- `ENVIRONMENT.md`, `PREDECESSOR_IMMUTABILITY.md`,
  `SHADOW_IMPORT_PROVENANCE.md`, `THEOREM_AND_CONTROLS.md`,
  `SPECIFICATION_CORRECTIONS.md`, and `PROOF_POLICY_AUDIT.md`: interpretation
  and provenance;
- `receipts/assurance_checks_20260907.json`: final read-only assurance results;
- `SOURCE_SHA256SUMS` and `FINAL_SHA256SUMS`: source-focused and complete
  release checksum manifests.

Nonqualifying historical logs are deliberately retained:

- `combined_production_attempt_001.log`: rejected obsolete Omega import;
- `combined_production_attempt_002.log`: rejected summation-notation parse;
- `combined_controls_attempt_003.log`: production green, control keyword and
  scalar-normalization failures;
- `combined_controls_attempt_004.log`: production green, final scalar
  commutativity/normalization failure.

Only attempt 5 and the modular run qualify the release.
