# Experiment 010 saved files and checkpoints

Start with [completion report](COMPLETION_REPORT.md),
[mathematical derivation](MATHEMATICAL_DERIVATION.md), and
[review](REVIEW.md). [Reproduction instructions](REPRODUCE.md) distinguish
development checks, independent proof verification, and transfer validation.

| File or directory | Purpose |
|---|---|
| `PLAN.md` | Scope and acceptance criteria |
| `evidence/BASELINE.json` | Frozen Experiment 009 foundation, manifest and archive pins |
| `lean/Exp009Foundation.lean` | Exact preserved Experiment 009 combined source |
| `lean/Regularity.lean` | Summable moment and derivative majorants |
| `lean/ClassicalSolution.lean` | Actual differentiation of the infinite series and PDE |
| `lean/Continuity.lean` | Joint continuity and explicit classical-solution predicate |
| `lean/ClassicalClosure.lean` | Pointwise grid samples, weighted error and convergence |
| `lean/Controls.lean` | Infinite-support regular datum and exact derivative controls |
| `lean/Exp010Combined.lean` | Entire retained proof chain and all new public audits |
| `lean/probes/` | Retained development probes; final claims use production sources |
| `evidence/*_<Module>.json` and `.log` | Dated modular compiler receipts, including failed development attempts |
| `evidence/FINAL_INPUTS.json` | Final component hashes, import list and public audit names |
| `evidence/local_combined/` | Accepted local combined result, compiler log and library manifest |
| `remote_check/VM_ALLOCATION.json` | Distinct fresh CPU VM identity |
| `remote_check/ENVIRONMENT_EXPECTED.json` | Initial empty project workspace and boot identity |
| `remote_check/BOOTSTRAP_INPUTS.json` | Bootstrap archive, script and input pins |
| `remote_check/bootstrap_inputs.tar.gz` | Six source/helper inputs for fresh dependency preparation |
| `remote_check/FINAL_UPLOAD.json` | Exact final source delivery receipt and archive path |
| `remote_check/EXPORT_RECEIPT.json` | Independent evidence archive checksum and byte count |
| `remote_check/downloaded_evidence/` | Verified independent source, inputs, bootstrap logs and proof result |
| `remote_check/FINAL_TRANSFER_CHECK.json` | Accepted received file hashes and cross-environment comparisons |
| `evidence/numerical_checks.json` | Derivative/PDE diagnostic data and numerical script hash |
| `NUMERICAL_DIAGNOSTICS.md` | Diagnostic method, counts and limitations |
| `evidence/REVIEW_CHECK.json` | Reviewed final source/catalog and tool hashes |
| `evidence/PREDECESSOR_PRESERVATION.json` | Read-only checks of earlier sealed manifests and archives |
| `evidence/FINAL_VERIFICATION.json` | Final qualification binding all accepted evidence |
| `PACKET_MANIFEST.json` | SHA-256 for every review-packet payload |
| `evidence/FINAL_PACKET_RECEIPT.json` | External sealed ZIP receipt, excluded from ZIP |

`run_lean.py`, `make_combined.py`, `verify_combined.py`,
`prepare_final_sources.py`, `prepare_bootstrap_inputs.py`, `check_predecessors.py`,
`finalize.py`, `verification_tools/`, and `remote_check/*.py` retain the
verification workflow. Build caches are omitted from the review packet.

The review ZIP is saved at
`/home/richman954/Exp010_Verified_Review_Packet_20260908.zip`, with a
neighboring `.zip.sha256` file. Earlier packets remain at their original paths;
the central project `RESUME_STATUS.md` records the progression between experiments.
