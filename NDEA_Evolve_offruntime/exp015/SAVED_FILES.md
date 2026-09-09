# Experiment 015 sources and evidence map

Read actual passing receipts before claiming completion. The implementation
is active until the final combined, independent, receiving, review and packet
gates have passed. Failed development attempts and receipts are preserved.

| Source | Purpose |
|---|---|
| `lean/ScalarSqrtEstimate.lean` | Square-root comparison with positive regularization, including zero error |
| `lean/SpatialL2.lean` | Spatial L2 norm, integral estimates and continuity prerequisites |
| `lean/ResidualField.lean` | Classical approximate-field regularity and the actual PDE residual |
| `lean/ForcedStability.lean` | Coefficient-one stability from the actual forced energy derivative |
| `lean/ResidualEstimate.lean` | Residual-to-error estimate retaining initial error |
| `lean/VariablePotentialBridge.lean` | Application to Exp014's unique regular variable-potential solution |
| `lean/Controls.lean` | Exact endpoint, initialization, zero-defect and active-forcing controls |
| `predecessor_sources/Exp014Combined.lean` | Exact sealed predecessor combined source and old audit catalog |
| `lean/Exp014Foundation.lean` | Same predecessor source with only the 143 old axiom-print lines removed |

`make_combined.py` reconstructs `lean/Exp015Combined.lean` and
`evidence/FINAL_INPUTS.json` from the exact foundation and new modules. The
receipt pins every delivered source, the generator and the complete new public
theorem/control catalog. Counts are derived after the source is complete.
`evidence/*_<Module>.json` and neighboring logs record each development check.

`evidence/local_combined/RESULT.json` is the isolated local final result.
The corresponding independent result is under
`remote_check/downloaded_evidence/final_verification/RESULT.json`.
`remote_check/VM_ALLOCATION.json` and `ENVIRONMENT_EXPECTED.json` identify the
new runtime; PREDECESSOR_ENVIRONMENT.json preserves the accepted Exp014 identity.
BOOTSTRAP_INPUTS.json and FINAL_UPLOAD.json identify exact source-only deliveries.
FINAL_TRANSFER_CHECK.json binds all accepted downloaded and local evidence.
These success/delivery receipts exist only after their workflow stage succeeds.

The offline tool tests are `test_combined_infrastructure.py`,
`test_infrastructure.py`, `test_environment_isolation.py` and
`test_finalizer_gates.py`. Their corresponding receipts are
COMBINED_INFRASTRUCTURE_TESTS.json, INFRASTRUCTURE_TESTS.json,
ENVIRONMENT_ISOLATION_TEST.json and FINALIZER_GATE_TESTS.json under evidence/.
These explicitly synthetic controls are separate from mathematical proof checks.

`REVIEW.md`, `evidence/REVIEW_CHECK.json` and `INFRASTRUCTURE_REVIEW.md` record
source and tool review. `MATHEMATICAL_DERIVATION.md` explains the estimate and
its assumptions. `evidence/FINAL_VERIFICATION.json` records accepted final
qualification; `COMPLETION_REPORT.md` states the exact scope and limitations.
`PACKET_MANIFEST.json` and `evidence/FINAL_PACKET_RECEIPT.json` bind the sealed
packet, saved under `/home/richman954/` with a neighboring checksum file.
The final packet receipt is outside the archive to avoid self-reference.

The continuous residual estimate does not by itself prove convergence of
actual numerical iterates or reconstructions. Prior experiments and their
sealed packets remain unchanged. `check_predecessors.py` checks inherited
manifests and the sealed Exp014 packet without writing into old experiments.

Active recovery state, verified snapshots and the backup receipt live outside
sealed experiments under `/home/richman954/NDEA_Recovery/`. Compiler/build
caches are excluded from snapshots. Final verified Chromebook copies include
the Exp001–012 release base, supplemental Exp013/014 packets, active Exp015
packet and recovery metadata. Read LOCAL_BACKUP_RECEIPT.json for the actual
latest coverage. The user canceled Google Drive backup.
