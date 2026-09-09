# Variable-potential development

This is the curated `dev/variable-potential` branch of NDEA. It starts from the August 30 main commit `15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c`. Main and its history remain unchanged. The original release sources, paper, configuration and audit files remain here; the [original README](https://github.com/richman954/NDEA-Periodic-Cayley-CN-Lean/blob/15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c/README.md) describes that release. This branch changes only this README and `.gitignore` among those original files.

Exp016 is authorized and in progress. This checkpoint contains **30 accepted development modules**: 28 property modules with 187 public theorem declarations, a separate norm axiom-audit module, and independently authored target definitions. Pending sources: none at this capture. The [current defects catalog](NDEA_Evolve_offruntime/exp016/DEFECTS_CHECKPOINT.json) binds every captured mathematical source to its completed receipt and full compiler log. **Exp016 remains incomplete and unsealed:** no combined or independent Exp016 qualification is included.

The accepted ordered-stage identities and norm bounds feed the actual Cayley trajectory certificate. The quantitative certificate substitutes these proved bounds into the grid-time and partial-slab estimates while retaining the derived stencil and potential terms and arbitrary initial error. Its operator norms are those of the actual grid matrices; no bound uniform across mesh refinements is asserted. Weighted coefficient extraction identifies the continuum Fourier coefficients of Exp014's all-mode synthesis and its actual potential product with the corresponding integer convolution. This continuum identity does not identify sampled coefficients without aliasing. The spatial residual is separated into the actual centered-stencil discrepancy and the sampled-potential interpolation discrepancy, with their derived norm contributions retained explicitly. Grid-time and partial-slab analytical certificates accumulate computed budgets over the actual trajectory. These results do not establish spatial-defect vanishing, a refinement limit, or a general variable-potential convergence rate.

The actual sampled-matrix potential is bound to Exp014's operator-valued potential, and the independently specified target is connected to the reconstructed trajectory by accepted theorems. An independently written target definition alone is not a PDE property theorem. The one-node cosine-potential control and earlier finite-reconstruction Parseval/coefficient identities retain their previous accepted scope.

The full-grid stencil is diagonalized on the actual Fourier reconstruction. Its spatial defect has an explicit bound with factor `sqrt(2*pi) * h^2` times the actual fourth-frequency moment of the current grid coefficients. This is a computed-data bound; no fourth-moment bound uniform along the numerical trajectory or across mesh refinements is supplied.

The [pinned external reuse map](NDEA_Evolve_offruntime/exp016/design/external_reference/REUSE_MAP.md) records the inspected source and manuscript, dependency differences and bounded transfer. Its compact manifests and upstream license are retained; external source trees, PDF, extracted text, build caches and compiled artifacts are excluded. No upstream build, Comparator or additional independent kernel run is claimed. Runtime recovery records are operational evidence, separate from theorem acceptance.

Start with [Exp016 PLAN.md](NDEA_Evolve_offruntime/exp016/PLAN.md) and the [current exact source/receipt catalog](NDEA_Evolve_offruntime/exp016/DEFECTS_CHECKPOINT.json). The previous [transfer catalog](NDEA_Evolve_offruntime/exp016/TRANSFER_CHECKPOINT.json), [certificate catalog](NDEA_Evolve_offruntime/exp016/CERTIFICATE_CHECKPOINT.json), startup catalogs and root [development plan](DEVELOPMENT_PLAN.md) remain unchanged historical checkpoints.

Exp015 remains the unchanged accepted predecessor: its [completion report](NDEA_Evolve_offruntime/exp015/COMPLETION_REPORT.md) records local and independent qualification and sealing. Exp013 establishes generic classical energy and uniqueness; Exp014 constructs classical solutions for a weighted Fourier variable-potential class; Exp015 proves continuous L2 forcing/residual estimates with coefficient 1 and arbitrary initial error. Main and its history remain unchanged; this source checkpoint targets only dev/variable-potential and preserves all sealed predecessor bytes.

## Layout and evidence

`NDEA_Evolve_offruntime/exp013` through `exp015` retain exact accepted Lean sources, combined sources, verification/audit Python, controls, tests, dependency pins, derivations and compact receipts. Exp016 adds the selected current certificate sources, completed matching development evidence, small runners, design notes and an exact Exp015 combined-source copy. Its required Exp008 `StageBridge.lean` import is retained with its original sealed manifest binding. Its `BASELINE.json` and `NUMERICAL_PINS.json` retain predecessor source/packet bindings. The selected Exp008–012 Lean files complete the actual modular import chain. Their packet manifests and receipts bind those bytes to earlier sealed packets. The older experiment folders here are deliberately partial.

The [source manifest](DEVELOPMENT_SOURCE_MANIFEST.json) maps paths and SHA-256 values to sealed packet entries, accepted module receipts, combined-source hashes and local/independent result receipts. Small accepted compiler `.log` files are deliberately included. Large dependency artifact inventories, downloaded libraries, project build caches, full bootstrap logs, scratch files, launch/session state and packet archives belong in recovery storage. Historical receipt paths remain unchanged; not every referenced payload is in this curated tree.

The separate `backup/ndeaevolve-20260909` branch is a recovery source snapshot. `backup/verified-milestones-20260909` contains exact archive payloads and its `NDEA_BACKUP/README.md` explains restoration and coverage. Use its actual manifest and verified readback receipts to establish the latest uploaded milestone; a local sealed packet does not by itself establish remote coverage. Restore full archives into a separate directory when historical packet validation is needed. Local Chromebook recovery copies continue; Google Drive is canceled.

## Rechecking accepted combined sources

The Exp016 `run_lean.py` and additive `run_lean_timed.py` are machine-pinned development runners. The small `remote_dev` scripts preserve the Colab development workflow; their bootstrap, compiler caches and project artifacts are intentionally omitted, so this thin checkout does not provision that workflow by itself. It imports cached project artifacts through absolute Chromebook paths. This snapshot is not yet an independent isolated Exp016 qualification workflow, and a fresh checkout on another machine cannot run that runner unchanged. The instructions below apply to the completed Exp013–015 combined checks.


Use the exact Lean 4.31.0 compiler and clean pinned dependency checkouts with compatible prebuilt external artifacts. The complete package lock is `expNNN/remote_check/bootstrap_inputs/lake-manifest.json`; Mathlib is pinned to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The recorded Lean binary SHA-256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. These dependencies are not vendored here. The old root Lake project still describes the August 30 release; `lake build` at this root is not the Exp013–015 qualification command.

From this checkout, after provisioning the pinned compiler and external package artifacts, run one experiment at a time, with absolute paths substituted:

```sh
python3 -B NDEA_Evolve_offruntime/exp015/verify_combined.py \
  --root /absolute/path/to/checkout/NDEA_Evolve_offruntime/exp015 \
  --lean /absolute/path/to/lean-4.31.0/bin/lean \
  --mathlib /absolute/path/to/packages/mathlib \
  --other-packages /absolute/path/to/packages \
  --output /absolute/path/to/new-exp015-check-output
```

The output directory must not exist. Substitute `exp013` or `exp014` for the other accepted checks. The checker reconstructs and compares the combined source and source pins, uses an isolated external import closure, sanitizes Lean environment paths, elaborates the combined file and records the expected axiom audits. It trusts the pinned compiler and compatible library artifacts; it does not rebuild their sources or prove source-to-artifact correspondence. Keep new results outside the historical evidence paths. A direct Lean elaboration alone establishes less than this receipt-producing check.

The original `run_lean.py` scripts contain Chromebook-specific compiler, package, build and lock paths; their presence is historical tooling preservation, not a portable modular build promise. `make_combined.py` writes accepted source/receipt files when run as a script; do not run it over this baseline. Preparation scripts are already prepared and single-use. Real finalizers/predecessor checks require full prior packets, all manifest payloads, archived evidence, review bindings and historical absolute paths/.olean artifacts, so they cannot be run unchanged using only this thin tree.

Environment-isolation tests are self-contained. Combined-infrastructure tests for Exp014/015 have the required canonical predecessor source copies here. General `test_infrastructure.py` suites require omitted full downloaded bootstrap/evidence fixtures. Exp015 finalizer-gate tests also assume historical absolute archive anchors. Copied historical `REPRODUCE.md` files describe the full original workspace; this guide states the limits of this curated checkout. No proof checks were rerun while staging it.

## What each record establishes

A Git commit identifies repository bytes. Lean acceptance establishes elaboration of specified source under its inputs. An NDEA receipt records the specified checks and their input/output hashes. Independent qualification repeats the check in the documented isolated environment. These are different claims.

The manifest records accepted source and receipt hashes without changing sealed evidence. After publication, an external readback receipt must bind the actual Git commit/tree to this manifest's SHA-256 and every staged file hash. This yields commit → source → acceptance receipt and receipt → source hash → committed path without a self-hash cycle. No commit ID is invented inside its own content. Tags or releases can later mark a fully qualified milestone after review; never move a published verified tag.

Commit after meaningful source progress, before risky refactors, and at accepted milestones. Push at useful milestones; local recovery snapshots remain frequent. Changes to mathematics or tooling require new checks and new receipts in a working experiment, preserving this accepted baseline.

## Continue from this defects checkpoint

Read the [startup milestone report](NDEA_Evolve_offruntime/exp016/STARTUP_MILESTONE.md), [NEXT_STEPS](NDEA_Evolve_offruntime/exp016/NEXT_STEPS.md) and the [regular synthesis interface](NDEA_Evolve_offruntime/exp016/design/REGULAR_SYNTHESIS_INTERFACE.md) for the immediate bridge to the actual PDE residual. The [density/perturbation option](NDEA_Evolve_offruntime/exp016/design/DENSITY_PERTURBATION_OPTION.md) is a later mathematical design possibility, not a new accepted theorem or an Exp017 selection. The current source snapshot preserves the exact acceptance boundary in DEFECTS_CHECKPOINT.json even when later workspace checks finish. Earlier startup, certificate and transfer catalogs retain their historical meaning.
