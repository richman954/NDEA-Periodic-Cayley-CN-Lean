# Experiment 014 sources, checkpoints and verification files

Read actual accepted result receipts before making a proof claim. During
implementation, PLAN.md and the central recovery state record unfinished work.
Paths below describe the verification workflow; final receipts exist only after
all required checks pass. Failed development receipts are retained.

| Source | Purpose |
|---|---|
| `lean/GlobalLinearEvolution.lean` | All-real-time Dyson evolution for a uniformly bounded strongly continuous linear vector field on a real Banach space |
| `lean/StrongOperatorDerivative.lean` | Product rule for a strongly varying bounded operator applied to a differentiable state |
| `lean/WeightedFourier.lean` | Complete weighted Fourier state, raw initialization, free isometric group and joint continuity |
| `lean/ScalarSeries.lean` | Bounded scalar-multiplier summation, joint continuity and actual differentiation |
| `lean/FourierPotential.lean` | Weighted convolution, continuous periodic operator potential and selfadjointness |
| `lean/FourierSynthesis.lean` | Synthesized field, first/second spatial derivatives and free time derivative |
| `lean/FourierProduct.lean` | Convolution synthesis equals pointwise multiplication by the potential |
| `lean/ClassicalExistence.lean` | Interaction evolution, actual classical PDE construction and unique global existence |
| `lean/Controls.lean` | Exact assumption and endpoint applications, including variable potential and infinite-support data |
| `predecessor_sources/` | Three unchanged, pinned generic Exp013 original files |
| `lean/Exp013GenericFoundation.lean` | Reconstructed generic predecessor bodies; no earlier numerical chain |

`lean/Exp014Combined.lean` and `evidence/FINAL_INPUTS.json` are generated from the
frozen source. The latter binds component hashes, exact reconstruction and all
new public theorem/control audit names. Dated `evidence/*_<Module>.json` and
neighboring logs record development compiles; only passing receipts for the
current unchanged source and artifact qualify a module.

`evidence/local_combined/RESULT.json` records the final local combined check.
`remote_check/VM_ALLOCATION.json` and `ENVIRONMENT_EXPECTED.json` identify the
separate fresh runtime. `BOOTSTRAP_INPUTS.json` and `FINAL_UPLOAD.json` pin
source-only deliveries. `remote_check/downloaded_evidence/` holds the received
independent source, bootstrap logs, compiler log and dependency manifests;
`FINAL_TRANSFER_CHECK.json` verifies their agreement with the local proof.

`REVIEW.md`, `evidence/REVIEW_CHECK.json`, and `INFRASTRUCTURE_REVIEW.md` record
independent source/tool review. `evidence/FINAL_VERIFICATION.json` is written
only after the local, independent, transfer and review gates pass.
`PACKET_MANIFEST.json` and `evidence/FINAL_PACKET_RECEIPT.json` bind the sealed
payload and verified ZIP. The review ZIP and neighboring checksum are saved
under `/home/richman954/`. Receipts outside the ZIP avoid a self-hash cycle.

The working derivation and API/design notes explain the proof. They are not
compiler receipts. No numerical diagnostic is used to prove existence.

Active recovery state and minute snapshots live outside sealed experiments in
`/home/richman954/NDEA_Recovery/`. Snapshots are restart aids and may capture
mutable files at different instants; explicit verified milestone snapshots
supplement the tracked watcher. Build caches are excluded. The user selected
local Chromebook backup copies and canceled Google Drive. The newest verified
convenience folder is identified by `NDEA_Recovery/LOCAL_BACKUP_RECEIPT.json`
and is found under Files → Linux files → Downloads. Its manifest states exactly
which completed packets and current recovery files are copied.
