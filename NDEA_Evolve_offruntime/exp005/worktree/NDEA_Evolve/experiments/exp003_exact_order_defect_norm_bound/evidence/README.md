# Experiment 003 Step 2 evidence

This directory is independent of the Step 1 evidence and records only the
exact order-defect operator-norm bound and its two requested negative controls.

Qualifying evidence:

- `logs/modular_controls_pass_20260907.log`: traced, serial, module-by-module
  compile ending with exit code 0;
- `receipts/modular_controls_20260907.json`: command, bounds, timing, commit,
  result, and log digest;
- `logs/combined_controls_pass_20260907.log`: independent combined-unit control
  compile ending with exit code 0;
- `receipts/combined_controls_20260907.json`: corresponding receipt;
- `ENVIRONMENT.md`, `PREDECESSOR_IMMUTABILITY.md`,
  `SHADOW_IMPORT_PROVENANCE.md`, `THEOREM_AND_CONTROLS.md`, and
  `PROOF_POLICY_AUDIT.md`: interpretation and provenance.

`logs/combined_controls_failed_cleanup_20260907.log` is deliberately retained
as rejected historical evidence. It records a temporary tactic-cleanup
regression, was followed by restoring the checkpointed passing tactic sequence,
and must never be interpreted as a qualifying run.
