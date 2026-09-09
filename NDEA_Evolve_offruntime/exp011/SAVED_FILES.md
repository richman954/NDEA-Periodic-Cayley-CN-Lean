# Experiment 011 saved files and checkpoints

Start with [completion report](COMPLETION_REPORT.md),
[derivation](MATHEMATICAL_DERIVATION.md), and [review](REVIEW.md).
[Reproduction instructions](REPRODUCE.md) explain the distinct development,
combined proof, and receiving checks.

| File or directory | Purpose |
|---|---|
| `PLAN.md` | Scope and acceptance criteria |
| `evidence/BASELINE.json` | Frozen Experiment 010 source, manifest and archive pins |
| `lean/Exp010Foundation.lean` | Exact retained Experiment 010 combined source |
| `lean/SolutionLipschitz.lean` | Actual space/time derivative and norm difference bounds |
| `lean/Reconstruction.lean` | Explicit indices, actual iterates, node extraction and reconstruction error |
| `lean/ScheduleBounds.lean` | Error bounds for every scheduled step and the inverse-mesh limit |
| `lean/UniformConvergence.lean` | Full-rectangle uniform convergence to the classical PDE solution |
| `lean/Controls.lean` | Exact index, norm and infinite-support controls |
| `lean/Exp011Combined.lean` | Retained proof chain and complete new public audit catalog |
| `lean/probes/` | Preserved feasibility probes; not production evidence |
| `FUTURE_UNIQUENESS_NOTE.md` | Unverified future energy-uniqueness route and interrupted probe scope |
| `evidence/*_<Module>.json` and `.log` | Dated modular checks, including failed development attempts |
| `evidence/FINAL_INPUTS.json` | Frozen component hashes, external imports and audit names |
| `evidence/local_combined/` | Accepted local proof result, log and external artifact manifest |
| `remote_check/VM_ALLOCATION.json` | Distinct fresh CPU VM identity |
| `remote_check/ENVIRONMENT_EXPECTED.json` | Initial empty project workspace and boot identity |
| `remote_check/BOOTSTRAP_INPUTS.json` | Bootstrap delivery and script pins |
| `remote_check/FINAL_UPLOAD.json` | Frozen final source delivery and archive name |
| `remote_check/EXPORT_RECEIPT.json` | Independent evidence archive hash and size |
| `remote_check/downloaded_evidence/` | Validated independent source, bootstrap and proof evidence |
| `remote_check/FINAL_TRANSFER_CHECK.json` | Accepted evidence hashes and cross-environment comparison |
| `evidence/numerical_checks.json` | Off-grid numerical diagnostics and exact script hash |
| `NUMERICAL_DIAGNOSTICS.md` | Diagnostic methods, counts, aliases and truncation qualifications |
| `evidence/INFRASTRUCTURE_TESTS.json` | Focused offline protocol exercises, not proof certificates |
| `evidence/REVIEW_CHECK.json` | Reviewed final source/catalog and tool hashes |
| `evidence/PREDECESSOR_PRESERVATION.json` | Earlier sealed manifest and archive checks |
| `evidence/FINAL_VERIFICATION.json` | Final qualification binding all accepted evidence |
| `PACKET_MANIFEST.json` | Every review-packet payload hash |
| `evidence/FINAL_PACKET_RECEIPT.json` | External sealed ZIP receipt, excluded from ZIP |

The preserved workflow consists of `run_lean.py`, `make_combined.py`,
`verify_combined.py`, `prepare_final_sources.py`, `prepare_bootstrap_inputs.py`,
`check_predecessors.py`, `finalize.py`, `verification_tools/`, and
`remote_check/*.py`. Build caches are excluded from the review packet.

The packet is saved at
`/home/richman954/Exp011_Verified_Review_Packet_20260908.zip`, with a
neighboring `.zip.sha256` file. Earlier sealed packets remain unchanged.
The central `RESUME_STATUS.md` and `WORKING_ROADMAP.md` are outside these
packets and record the current project direction.
