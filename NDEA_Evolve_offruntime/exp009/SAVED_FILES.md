# Experiment 009 saved files and checkpoints

Read [COMPLETION_REPORT.md](COMPLETION_REPORT.md) for the accepted outcome,
[MATHEMATICAL_DERIVATION.md](MATHEMATICAL_DERIVATION.md) for the argument, and
[REVIEW.md](REVIEW.md) for the independent mathematical and verification review.

| File or directory | Purpose |
|---|---|
| `lean/Exp008Foundation.lean` | Exact frozen Experiment 008 combined proof |
| `lean/InfiniteReference.lean` | Actual infinite series, summability, sampling identity, and tail |
| `lean/WeightedTail.lean` | Weighted coefficient moments and quantitative tail bound |
| `lean/CutoffSchedule.lean` | Explicit growing cutoff, compatible mesh/step, common terminal time |
| `lean/InfiniteClosure.lean` | Full-reference grid error and generic growing-cutoff convergence |
| `lean/WeightedClosure.lean` | Weighted-tail bound inserted into the actual error theorem |
| `lean/ScheduleClosure.lean` | Concrete convergence at terminal time one |
| `lean/Controls.lean` | Infinite-support positive example and aliasing controls |
| `lean/Exp009Combined.lean` | Complete combined proof used in both final checks |
| `evidence/FINAL_INPUTS.json` | Exact constituent hashes, combined hash, and public audit catalog |
| `evidence/FINAL_VERIFICATION.json` | Final qualification and accepted modular receipt paths |
| `evidence/local_combined/` | Local compiler log, result, and external artifact manifest |
| `remote_check/downloaded_evidence/` | Accepted independent source, inputs, compiler log, and receipts |
| `remote_check/FINAL_TRANSFER_CHECK.json` | Download integrity, source/audit agreement, library comparison |
| `remote_check/EXPORT_RECEIPT.json` | Independent evidence archive name and checksum |
| `evidence/numerical_checks.json` | Supporting infinite-data numerical diagnostics |
| `NUMERICAL_DIAGNOSTICS.md` | Datum, tests, truncation estimate, and roundoff limits |
| `evidence/exp009_convergence.png`, `evidence/exp009_convergence.pdf` | Refinement figure from the accepted numerical data |
| `evidence/exp009_convergence_receipt.json` | Figure input, script, and output hashes |
| `FAILURE_AND_REPAIR_LOG.md` | Development repairs and the replaced Colab runtime |
| `evidence/BASELINE.json` | Previous source and packet pins before new work |
| `evidence/PREDECESSOR_PRESERVATION.json` | Read-only check of all older sealed manifests |
| `evidence/2026*.json`, `evidence/2026*.log` | Dated modular development attempts; final receipt selects accepted ones |
| `lean/probes/`, `lean/ProbeControls.lean` | Exploratory API checks; excluded from the final public catalog |
| `PACKET_MANIFEST.json` | Every packaged payload file and SHA-256 |
| `evidence/FINAL_PACKET_RECEIPT.json` | ZIP checksum and complete post-write verification |

The home review archive is
`/home/richman954/Exp009_Verified_Review_Packet_20260908.zip`, with a neighboring
`.zip.sha256` file. Its receipt remains outside the ZIP to avoid a self-hash
cycle. Build caches are excluded from the packet. Earlier archives remain
separate and unchanged.

The central restart guide is `../RESUME_STATUS.md`. Reproduction commands are
in [REPRODUCE.md](REPRODUCE.md).
