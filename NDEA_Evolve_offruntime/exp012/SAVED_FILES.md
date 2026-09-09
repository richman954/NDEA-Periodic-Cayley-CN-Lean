# Experiment 012 saved files and checkpoints

Start with the [completion report](COMPLETION_REPORT.md),
[derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md), and
[reproduction instructions](REPRODUCE.md).

| File or directory | Purpose |
|---|---|
| `PLAN.md` | Scope and acceptance criteria |
| `evidence/BASELINE.json` | Frozen Experiment 011 source, manifest and archive pins |
| `lean/Exp011Foundation.lean` | Exact retained Experiment 011 combined source |
| `lean/EnergyLocal.lean` | Actual density/flux identity, periodicity and subtraction closure |
| `lean/EnergyConservation.lean` | Local compact domination and conserved period energy |
| `lean/EnergySeparation.lean` | Positivity and separation of continuous spinor fields by energy |
| `lean/ClassicalUniqueness.lean` | All-real-time uniqueness, regular-data existence and unique numerical limit |
| `lean/Controls.lean` | Exact nonzero-mode, data-matching, energy, uniqueness and flux controls |
| `lean/Exp012Combined.lean` | Retained proof bodies and complete new public axiom catalog |
| `lean/probes/` | Preserved focused development probes |
| `evidence/*_<Module>.json` and `.log` | Dated module receipts, including failed or interrupted attempts |
| `evidence/FINAL_INPUTS.json` | Frozen component hashes, external imports and audit names |
| `evidence/local_combined/` | Accepted local proof, log and external artifact manifest |
| `remote_check/VM_REPLACEMENT.json` | Completed Exp011 VM release and replacement after allocation limit |
| `remote_check/release_exp011_preflight.py` | Read-only completed-proof/evidence/process preflight |
| `remote_check/VM_ALLOCATION.json` | Distinct fresh Exp012 CPU VM identity |
| `remote_check/ENVIRONMENT_EXPECTED.json` | Initial empty project workspace and boot identity |
| `remote_check/BOOTSTRAP_INPUTS.json` | Exact bootstrap delivery and driver pins |
| `remote_check/FINAL_UPLOAD.json` | Frozen final source archive and delivery manifest |
| `remote_check/EXPORT_RECEIPT.json` | Independent evidence archive checksum and size |
| `remote_check/downloaded_evidence/` | Validated independent source, bootstrap and proof evidence |
| `remote_check/FINAL_TRANSFER_CHECK.json` | Accepted transferred hashes and agreement between environments |
| `evidence/INFRASTRUCTURE_TESTS.json` | Focused offline protocol checks |
| `evidence/PREDECESSOR_PRESERVATION.json` | Earlier sealed manifest and archive checks |
| `evidence/REVIEW_CHECK.json` | Final reviewed proof/catalog and tool hashes |
| `evidence/FINAL_VERIFICATION.json` | Final qualification binding all accepted evidence |
| `PACKET_MANIFEST.json` | Every review-packet payload hash |
| `evidence/FINAL_PACKET_RECEIPT.json` | External sealed ZIP receipt, excluded from the ZIP |

The preserved workflow includes `run_lean.py`, `make_combined.py`,
`verify_combined.py`, `prepare_final_sources.py`, `prepare_bootstrap_inputs.py`,
`check_predecessors.py`, `finalize.py`, `verification_tools/` and
`remote_check/*.py`. Build caches are excluded from the packet. This milestone
uses exact formal controls and does not add a numerical simulation as evidence
of uniqueness.

The review packet is
`/home/richman954/Exp012_Verified_Review_Packet_20260908.zip`, with a neighboring
`.zip.sha256` file. Earlier sealed experiment files remain unchanged.
The central `RESUME_STATUS.md` and `WORKING_ROADMAP.md` are outside the packets.
