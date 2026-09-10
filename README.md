# Current development checkpoint — actual spatial residual refinement

62 development modules are accepted. The actual complete quadratic spatial slab budget now consumes the propagated weighted DFT estimate, and its explicit coefficient vanishes. The actual accumulated spatial residual and fixed-cutoff solver error at time 1 converge to zero. Additional approximation and finite-horizon source drafts are preserved separately. See [source/receipt catalog](NDEA_Evolve_offruntime/exp016/SPATIAL_REFINEMENT_CHECKPOINT.json) and [the mathematical scope](NDEA_Evolve_offruntime/exp016/design/SPATIAL_REFINEMENT_MILESTONE.md). Exp016 remains unsealed; original-data approximation, uniform finite-horizon convergence and full combined/independent qualification remain pending. The sections below retain earlier checkpoint history.

# Current development checkpoint — actual initial weights and spatial moments

59 development modules are accepted. Actual samples of fixed finite initial-data cutoffs have a grid-independent weighted DFT bound, which feeds the accepted ordered Cayley propagation theorem. Fourth moments and low/high coefficient sums now control the existing complete spatial defect budget, with an actual endpoint-trajectory consumer. See [source/receipt catalog](NDEA_Evolve_offruntime/exp016/INITIAL_WEIGHTED_CHECKPOINT.json) and [the mathematical scope](NDEA_Evolve_offruntime/exp016/design/INITIAL_WEIGHTED_MILESTONE.md). Exp016 remains unsealed; quadratic slab estimates, spatial refinement, approximation quantifiers and full combined/independent qualification remain pending. The sections below retain earlier checkpoint history.

# Current development checkpoint — actual weighted Cayley propagation

57 development modules are accepted. The actual kinetic/Z Cayley factors preserve the weighted DFT sum, and finite-cutoff sampled B stages have an explicit mesh-independent growth bound. The actual ordered trajectory satisfies W(y_j) <= exp(2*K_B*sum(abs(k_i)))*W(y_0) under the stated step restriction, which eventually holds on the saved refinement schedule. See [source/receipt catalog](NDEA_Evolve_offruntime/exp016/WEIGHTED_CAYLEY_CHECKPOINT.json) and [the mathematical scope](NDEA_Evolve_offruntime/exp016/design/WEIGHTED_CAYLEY_MILESTONE.md). Exp016 remains unsealed; uniform initial moments, spatial refinement and full combined/independent qualification remain pending. The sections below retain earlier checkpoint history.

# Current development checkpoint — weighted sampled-potential control

55 development modules are accepted. Centered grid aliases cannot increase the frequency weight. Actual sampled multiplication by a fixed finite Fourier cutoff is bounded in the fourth weighted absolute DFT sum, with a constant independent of the numerical grid. See [source/receipt catalog](NDEA_Evolve_offruntime/exp016/WEIGHTED_SPATIAL_CHECKPOINT.json) and [the mathematical scope](NDEA_Evolve_offruntime/exp016/design/WEIGHTED_SPATIAL_MILESTONE.md). Exp016 remains unsealed; actual weighted Cayley propagation, spatial refinement, and full combined/independent qualification remain pending. The sections below retain earlier checkpoint history.

# Current development checkpoint — actual temporal refinement

53 development modules are accepted. The actual accumulated temporal contribution tends to zero for N=2(q+1)+1, h=2*pi/N, J=N^4 and k=1/J. The actual time-1 PDE certificate retains its spatial sum. See [source/receipt catalog](NDEA_Evolve_offruntime/exp016/TEMPORAL_CHECKPOINT.json) and [pinned reference reuse delivery](NDEA_Evolve_offruntime/exp016/design/external_reference/RESUMED_REFERENCE_DELIVERY.md). Exp016 remains unsealed; full combined/independent qualification and spatial refinement are pending. The sections below retain earlier checkpoint history.

# Current development checkpoint — recovered Exp016

51 development modules are accepted, including the actual fixed-Z bound `||op(sampledSplitA)|| <= 4/h^2 + 1` on the positive physical odd grid. See [source/receipt catalog](NDEA_Evolve_offruntime/exp016/REBOOT_CHECKPOINT.json) and [pinned reference reuse delivery](NDEA_Evolve_offruntime/exp016/design/external_reference/RESUMED_REFERENCE_DELIVERY.md). Exp016 remains unsealed; full combined/independent qualification and spatial refinement are pending. The sections below retain earlier checkpoint history.

# Variable-potential development

This is the curated `dev/variable-potential` branch of NDEA. It starts from the August 30 main commit `15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c`. Main and its history remain unchanged. The original release sources, paper, configuration and audit files remain here; the [original README](https://github.com/richman954/NDEA-Periodic-Cayley-CN-Lean/blob/15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c/README.md) describes that release. This branch changes only this README and `.gitignore` among those original files.

Exp016 is authorized and in progress. This checkpoint contains **49 accepted development modules**: 47 property modules with 282 public theorem declarations, a separate norm axiom-audit module, and independently authored target definitions. Pending sources: none at this capture. The [current continuum-stability catalog](NDEA_Evolve_offruntime/exp016/CONTINUUM_CHECKPOINT.json) binds every captured mathematical source to its completed receipt and full compiler log. **Exp016 remains incomplete and unsealed:** no combined or independent Exp016 qualification is included.

The new spatial L2 operator bound turns pointwise operator-norm domination into physical L2 domination with the same constant. For two actual Exp014 solutions with regular Hermitian potentials, the residual of the second solution in the first equation is derived with sign `(W-V) * u_W`. Its physical L2 norm is bounded using conservation of the second solution's physical mass. The resulting continuum potential-perturbation estimate is the initial L2 mismatch plus `t * delta` times the second initial datum's physical L2 norm, for `t >= 0`. It does not assume a bound on evolving weighted Fourier norms or introduce a Gronwall factor.

The potential error-transfer theorem compares actual solver errors for the full potential and its symmetric Fourier cutoff. Both numerical runs start from the original initial field's actual point samples, the grid has `2*M+1` nodes with `(2*M+1)*h = 2*pi`, and nonnegative steps total time `T`. It proves `E_v <= E_cutoff + 2*T*sqrt(2*pi)*||a||*tail_v(R)`, with `tail_v(R) <= W_v/(1+R)^2` for the original weighted potential moment `W_v`. Here `E_cutoff` is the actual unresolved solver error for the cutoff potential, not a supplied or established approximation estimate. The theorem does not establish that error's vanishing or full variable-potential solver convergence.

Earlier accepted results retain their exact scope: grid-time sampled-potential perturbation is uniform in the mesh, symmetric potential cutoff is controlled by its omitted coefficient tail and original weighted moment, and actual initial interpolation converges on expanding odd grids. Arbitrary initial mismatch remains explicit where stated. The existing alias, stencil, target-binding and grid-time/partial-slab residual certificates are preserved. Uniform control of evolving numerical Fourier tails and fourth-frequency moments and the remaining spatial/time refinement argument are not supplied here. The grid-time numerical perturbation constant is not asserted unchanged for quadratic paths between grid times.

The [pinned external reuse map](NDEA_Evolve_offruntime/exp016/design/external_reference/REUSE_MAP.md) records the inspected source and manuscript, dependency differences and bounded transfer. Its compact manifests and upstream license are retained; external source trees, PDF, extracted text, build caches and compiled artifacts are excluded. No upstream build, Comparator or additional independent kernel run is claimed. Runtime readbacks and the small unchanged module-workflow helper preserve operational source/import bindings; restored-artifact development checks remain separate from independent qualification.

Start with [Exp016 PLAN.md](NDEA_Evolve_offruntime/exp016/PLAN.md), the [continuum milestone report](NDEA_Evolve_offruntime/exp016/design/CONTINUUM_MILESTONE.md) and the [current exact source/receipt catalog](NDEA_Evolve_offruntime/exp016/CONTINUUM_CHECKPOINT.json). The previous [potential catalog](NDEA_Evolve_offruntime/exp016/POTENTIAL_CHECKPOINT.json), [initialization catalog](NDEA_Evolve_offruntime/exp016/INIT_CHECKPOINT.json), [alias catalog](NDEA_Evolve_offruntime/exp016/ALIAS_CHECKPOINT.json), [defects catalog](NDEA_Evolve_offruntime/exp016/DEFECTS_CHECKPOINT.json), [transfer catalog](NDEA_Evolve_offruntime/exp016/TRANSFER_CHECKPOINT.json), [certificate catalog](NDEA_Evolve_offruntime/exp016/CERTIFICATE_CHECKPOINT.json), startup catalogs and root [development plan](DEVELOPMENT_PLAN.md) remain unchanged historical checkpoints.

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

## Continue from this continuum-stability checkpoint

Read the [startup milestone report](NDEA_Evolve_offruntime/exp016/STARTUP_MILESTONE.md), [NEXT_STEPS](NDEA_Evolve_offruntime/exp016/NEXT_STEPS.md) and the [regular synthesis interface](NDEA_Evolve_offruntime/exp016/design/REGULAR_SYNTHESIS_INTERFACE.md) for the immediate bridge to the actual PDE residual. The [density/perturbation option](NDEA_Evolve_offruntime/exp016/design/DENSITY_PERTURBATION_OPTION.md) is a later mathematical design possibility, not a new accepted theorem or an Exp017 selection. The current source snapshot preserves the exact acceptance boundary in CONTINUUM_CHECKPOINT.json even when later workspace checks finish. Earlier startup, certificate, transfer, defects, alias, initialization and potential catalogs retain their historical meaning.
