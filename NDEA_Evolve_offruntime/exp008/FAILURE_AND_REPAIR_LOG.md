# Experiment 008 failure and repair history

Prepared September 8, 2026 during final verification. **All seven production/control modules have successful local receipts matching the final source. Combined verification and final evidence-transfer acceptance are separate gates; this history does not certify them.** At commissioning, those combined checks were pending. Consult the final receipts for their later outcome.

This document summarizes retained evidence, not a new proof run. All 17 dated local receipts were inspected: nine failed attempts and eight successful checks, including the frozen foundation. Every corresponding log hash was checked against its receipt. Each successful receipt records unchanged source bytes and matches the current source hash. Timestamps below are UTC receipt invocation times; the serial compiler queue can delay actual execution.

## Local failed attempts

Every attempt in this table exited with code **1**. The receipt links preserve the exact source hash, command, elapsed time, and log hash. Failed elaborations can print `sorryAx` for failed declarations and their dependents; such output is failure evidence and is never accepted as a proof.

| Receipt time / component | Failure | Repair | Retained evidence |
|---|---|---|---|
| 07:15:07 — ContinuumModes | The initial-value proof tried `rfl` on an operator exponential at zero; a derivative proof also left the constant scalar/function form insufficiently explicit. | Normalize the zero operator/exponential and make the scalar-multiplication derivative application explicit. | [Receipt](evidence/20260908T071507.452546Z_ContinuumModes.json), [log](evidence/20260908T071507.452546Z_ContinuumModes.log) |
| 07:15:13 — FrequencyBounds | The adjacent characters `|*` were parsed as malformed absolute-value notation, producing downstream elaboration errors. | Separate the closing absolute-value bar from multiplication. | [Receipt](evidence/20260908T071513.860947Z_FrequencyBounds.json), [log](evidence/20260908T071513.860947Z_FrequencyBounds.log) |
| 07:18:23 — Exploratory probe | An unnecessary tactic ran after the goal had closed, a natural-number cast normalization prevented a rewrite, and `Fin(n+1)` needed a separating space. | Remove the redundant tactic, control casts, and repair spacing; the resulting arguments were incorporated into production `Orthogonality.lean`. | [Receipt](evidence/20260908T071823.277586Z_OrthogonalityProbe.json), [log](evidence/20260908T071823.277586Z_OrthogonalityProbe.log) |
| 07:18:51 — Dependency availability | `FrequencyBounds.olean` was unavailable because its earlier compilation had failed. | Compile the repaired dependency before retrying FourierGrid. | [Receipt](evidence/20260908T071851.575239Z_FourierGrid.json), [log](evidence/20260908T071851.575239Z_FourierGrid.log) |
| 07:23:25 — FourierGrid | Two stencil/periodicity rewrites failed to match lambda applications against their beta-reduced forms. | Use explicit beta reduction and `congrArg` for the periodicity multiplication. | [Receipt](evidence/20260908T072325.148012Z_FourierGrid.json), [log](evidence/20260908T072325.148012Z_FourierGrid.log) |
| 07:23:41 — Dependency availability | `FourierGrid.olean` was unavailable while its source still required the preceding repair. | Retry after FourierGrid passed. | [Receipt](evidence/20260908T072341.571791Z_Orthogonality.json), [log](evidence/20260908T072341.571791Z_Orthogonality.log) |
| 07:28:24 — Orthogonality | The library theorem named with `_sq` states Pythagoras using `norm * norm`; rewriting a goal written with `norm ^ 2` failed. | Derive an explicit squared-norm equality with `simpa only [← pow_two]`, then use it in the finite-sum induction. | [Receipt](evidence/20260908T072824.347751Z_Orthogonality.json), [log](evidence/20260908T072824.347751Z_Orthogonality.log) |
| 07:44:11 — Controls, first attempt | The aliasing proof used `change` across natural/integer/real casts and the wrapped-vector representation; these expressions were not definitionally equal. | Unfold the lift and normalize the wrapper and integer casts explicitly. | [Receipt](evidence/20260908T074411.841083Z_Controls.json), [log](evidence/20260908T074411.841083Z_Controls.log) |
| 07:48:19 — Controls, second attempt | The remaining phase identity used `↑(n+1)` while simplification normalized the target to `↑n+1`. | Normalize the natural casts in the phase identity itself with `Nat.cast_add` and `Nat.cast_one` before the final simplification. | [Receipt](evidence/20260908T074819.943951Z_Controls.json), [log](evidence/20260908T074819.943951Z_Controls.log) |

The standalone [OrthogonalityProbe.lean](lean/OrthogonalityProbe.lean) is exploratory and superseded. Its failed receipt does not match the later edited probe file; no successful probe receipt is claimed. It is excluded from the combined production ordering. The integrated arguments are supported by the successful production Orthogonality receipt below.

## Independent runtime recovery and remote batches

The old `exp007-independent-check` Colab runtime was unavailable. The [recovery record](evidence/REMOTE_RECOVERY.json), timestamped `2026-09-08T07:15:39.161594+00:00`, records a session-lost response with `404/401` and cleanup of the local session mapping. This was an operational runtime expiration, not a Lean theorem failure. The action was to create `exp008-independent-check` and independently download the pinned compiler/libraries. The record states that predecessor evidence was already preserved locally and no proof rerun result was lost.

The retained [runtime preparation](remote_check/prepare_runtime.py), [bootstrap launcher](remote_check/start_bootstrap.py), [foundation launcher](remote_check/start_foundation.py), and [modular batch launcher](remote_check/start_modules.py) document the replacement workflow. Each modular batch receives a source archive and an exact source-hash request; it stops at the first failed module.

The separately retained [remote StageBridge failure log](evidence/remote_stage_controls_v1_StageBridge.log) shows that the initial residual simplification left two `‖0‖` terms and a syntactic `modeGenerator` mismatch. The repair adds `norm_zero` and closes the remaining expression with `simpa only [modeGenerator] using hb`. This is an elaboration/simplification repair; no residual estimate was introduced as an assumption. Because the runner stops on this StageBridge failure, the first batch does not certify its following Controls module.

Five retained batch archives were checked against their request archive hashes and complete per-source hash catalogs:

| Batch | Retained archive and request | Relation to final source |
|---|---|---|
| scalar_continuum_v1 | [Archive](remote_check/scalar_continuum_v1.tar.gz), [request](remote_check/scalar_continuum_v1_REQUEST.json) | Final FrequencyBounds and ContinuumModes bytes. |
| grid_closure_v1 | [Archive](remote_check/grid_closure_v1.tar.gz), [request](remote_check/grid_closure_v1_REQUEST.json) | Final FourierGrid, Orthogonality, and SuperpositionClosure bytes. |
| stage_controls_v1 | [Archive](remote_check/stage_controls_v1.tar.gz), [request](remote_check/stage_controls_v1_REQUEST.json) | Failed initial StageBridge and initial Controls snapshots; the StageBridge failure log is linked above. |
| stage_controls_v2 | [Archive](remote_check/stage_controls_v2.tar.gz), [request](remote_check/stage_controls_v2_REQUEST.json) | Repaired final StageBridge, with the same initial Controls snapshot. The matching initial Controls failure is retained in the local 07:44:11 receipt. |
| controls_v3 | [Archive](remote_check/controls_v3.tar.gz), [request](remote_check/controls_v3_REQUEST.json) | Final Controls bytes, including both cast-normalization repairs. |

An input archive/request proves which source was supplied, not that compilation passed. Remote per-batch results/logs are produced under `/content/exp008_check/development/batches/<batch>/`; their eventual exported copies and the final transfer receipt govern acceptance of independent evidence. The successful local receipts below are directly available and checked here.

## Successful matching modular receipts

All rows have **exit code 0**, `sources_unchanged = true`, and a source hash matching the final module. Hash prefixes aid identification; complete hashes are in each linked receipt and [FINAL_INPUTS.json](evidence/FINAL_INPUTS.json). Nonfatal deprecation/linter warnings in successful logs are not failed proofs.

| Module | Successful receipt / log | Source SHA-256 prefix | Compiler seconds |
|---|---|---|---:|
| ContinuumModes | [Receipt](evidence/20260908T071916.516190Z_ContinuumModes.json), [log](evidence/20260908T071916.516190Z_ContinuumModes.log) | `9d0f3b6a75aa17a6` | 123.428 |
| FrequencyBounds | [Receipt](evidence/20260908T072128.037182Z_FrequencyBounds.json), [log](evidence/20260908T072128.037182Z_FrequencyBounds.log) | `97cd20e3dd29cc9b` | 82.823 |
| FourierGrid | [Receipt](evidence/20260908T072815.119165Z_FourierGrid.json), [log](evidence/20260908T072815.119165Z_FourierGrid.log) | `c62e4d0498cb5a0a` | 183.475 |
| Orthogonality | [Receipt](evidence/20260908T073507.475654Z_Orthogonality.json), [log](evidence/20260908T073507.475654Z_Orthogonality.log) | `f5840adbd334be39` | 127.549 |
| SuperpositionClosure | [Receipt](evidence/20260908T073855.753619Z_SuperpositionClosure.json), [log](evidence/20260908T073855.753619Z_SuperpositionClosure.log) | `a793d4731fa9c01a` | 142.566 |
| StageBridge | [Receipt](evidence/20260908T074410.114413Z_StageBridge.json), [log](evidence/20260908T074410.114413Z_StageBridge.log) | `85f75baadcbe2c15` | 93.179 |
| Controls | [Receipt](evidence/20260908T075140.816938Z_Controls.json), [log](evidence/20260908T075140.816938Z_Controls.log) | `51732dae30719c18` | 129.459 |

The unchanged frozen predecessor also passed locally: [foundation receipt](evidence/20260908T071054.595701Z_Exp007Foundation.json), [log](evidence/20260908T071054.595701Z_Exp007Foundation.log), 370.769 seconds. Its source SHA-256 is `cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c`.

## Acceptance boundary

The repaired modules retain their intended statements: signed finite Fourier sums, the actual periodic stencil/Cayley maps, exact discrete Parseval with explicit alias exclusion, the fixed-cutoff global error, and the derived full-grid residual budget. Failed logs and archived drafts remain historical diagnostics. Only successful checks of matching final bytes count as modular evidence; the full combined reconstruction, complete 90-public-theorem axiom audit, isolated external-library checks, and independent transfer verification must satisfy their own final receipts.
