# Experiment 003 Step 3 evidence

This directory is separate from the Step 2 evidence and records only the exact
split-versus-unsplit Cayley defect, its operator-norm bound, discovery pipeline,
and focused controls.

Qualifying evidence:

- `logs/julia_discovery.log` and `receipts/julia_discovery_20260907.json`:
  exact Julia discovery and certificate generation, exit code 0;
- `logs/python_certificate_validation.log` and
  `receipts/python_validation_20260907.json`: independent exact reconstruction,
  407 checks, exit code 0;
- `logs/modular_verification.log` and
  `receipts/modular_verification_20260907.json`: traced, serial,
  module-by-module Lean compile, exit code 0;
- `logs/combined_attempt_003.log` and
  `receipts/combined_lean_attempt_003_20260907.json`: independent combined-unit
  Lean compile, exit code 0;
- `ENVIRONMENT.md`, `PIPELINE_CERTIFICATE.md`,
  `PREDECESSOR_IMMUTABILITY.md`, `SHADOW_IMPORT_PROVENANCE.md`,
  `THEOREM_AND_CONTROLS.md`, `SPECIFICATION_CORRECTION.md`, and
  `PROOF_POLICY_AUDIT.md`: interpretation and provenance.

`logs/combined_attempt_001.log` and `combined_attempt_002.log` are deliberately
retained as rejected historical evidence. They record control-only arithmetic
normalization failures fixed before the qualifying attempt and must not be
interpreted as passing runs.
