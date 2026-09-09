# Experiments 001–008 — additional fresh Colab VM verification

Completed September 8, 2026. **The additional VM check passed: 473 distinct
public theorem/control audits, four original anonymous positive examples, and
13 deliberately false claims rejected at their expected proof locations.**
The exact sealed Experiment 008 check also passed all 90 audits independently.
Those 90 are included in the 473 distinct count, not added to it.

The user requested another machine to double-check the completed work. The
new CPU runtime was `exp008-fresh-recheck-r2`, VM `m-s-kkb-usc1b1-2yftnii3g1zpd`,
distinct from `m-s-kkb-usc1c1-1p1nzzki4492q`. The initial runtime check
found no prior project directories. It downloaded its own pinned Lean 4.31.0
distribution, all nine dependency source revisions, and compatible library
cache. No local project build artifacts were uploaded.

## What the new machine checked

The exact sealed Experiment 008 source and verifier were rerun unchanged. The
compiler finished in **247.136 seconds**, and its result
was accepted at `2026-09-08T08:27:09.311646+00:00`. All 90 audit results agree with both the
original local run and the first independent Colab run. All **9,868 external
artifact hashes** agree across these three environments and remained unchanged
during each exact-source check.

The complete retained source contains 332 public declarations across
Experiments 002–008. An additional source file has the sealed source as its
exact prefix and adds only 242 axiom-print commands. Separate historical
checks restore Experiment 001 and older standalone controls omitted from that
retained source. Their mathematical statements and proof bodies are preserved;
external imports are collected at the beginning and old audit commands are
replaced with the complete fresh catalog. Existing import-only compatibility
copies are explicitly recorded in the provenance inventory.

| Experiment | Distinct public audits |
|---|---:|
| 001 | 16 |
| 002 | 65 |
| 003 | 103 |
| 004 | 30 |
| 005 | 40 |
| 006 | 41 |
| 007 | 88 |
| 008 | 90 |
| **Total** | **473** |

These counts include supporting lemmas and control witnesses; they are not
counts of independent mathematical endpoints. The four anonymous Experiment
001 positive examples are checked through successful elaboration. The six
negative drivers cover 13 deliberately false claims: four scalar claims,
seven operator claims, and two contraction claims. Each produced ordinary
Lean exit 1 with the exact expected error lines, counts, and mathematical
diagnostic fragments. Import failures, unknown identifiers, resource failures,
and unrelated errors would not satisfy the rejection criteria.

| Supplemental source check | Accepted outcome | Compiler seconds | Evidence |
|---|---|---:|---|
| AllCheckpointAudit | Passed | 260.119 | [log](downloaded_evidence/recheck_evidence/historical_verification/AllCheckpointAudit.log) |
| Exp001Historical | Passed | 126.399 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp001Historical.log) |
| Exp002To005Controls | Passed | 196.349 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp002To005Controls.log) |
| Exp001_NC01_FALSE_MODULUS | Expected rejection confirmed | 18.785 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp001_NC01_FALSE_MODULUS.log) |
| Exp001_NC02_WRONG_AMPLIFICATION | Expected rejection confirmed | 7.200 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp001_NC02_WRONG_AMPLIFICATION.log) |
| Exp001_NC03_DROP_REAL_ASSUMPTION | Expected rejection confirmed | 8.099 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp001_NC03_DROP_REAL_ASSUMPTION.log) |
| Exp001_NC04_REVERSED_STENCIL_SIGN | Expected rejection confirmed | 6.992 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp001_NC04_REVERSED_STENCIL_SIGN.log) |
| Exp002RejectedControls | Expected rejection confirmed | 17.829 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp002RejectedControls.log) |
| Exp003Step1RejectedControls | Expected rejection confirmed | 18.991 | [log](downloaded_evidence/recheck_evidence/historical_verification/Exp003Step1RejectedControls.log) |

The supplementary checks used **34,168** isolated
external artifacts because the original Experiment 001 source imports the full
`Mathlib` module. That larger library contains the same 9,868 artifacts used
by the exact Experiment 008 check. Both verification import paths exclude
project build artifacts. Every positive audit uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Numerical diagnostics and preservation

The unchanged Experiment 008 numerical script was also rerun on the new VM.
All **60 stage cases** and
**20 global-error cases** passed, including
Parseval, wrapped-grid intertwining, aliasing, and arbitrary-initialization
checks. The finest observed orders were
**1.999975** jointly,
**1.999994** temporally, and
**0.999673** for the unsymmetric Lie
control. These are supporting floating-point diagnostics, separate from proofs.

The original Experiment 008 review packet and all 254 sealed payload files
were checked unchanged. The earlier frozen predecessor manifests still match
all 889/21/99/217 entries. New evidence is saved in this separate recheck
folder and archive. No mathematical theorem was changed or extended.

## Evidence and scope

- [Validated transfer](FINAL_TRANSFER_CHECK.json): all
  **180** exported file hashes, all uploaded
  sources/tools, compiler logs, positive audits, and exact rejection diagnostics.
- [Cross-environment comparison](CROSS_ENVIRONMENT_COMPARISON.json).
- [Fresh VM allocation](VM_ALLOCATION.json) and [initial state](FRESH_VM.json).
- [Exact sealed-source result](downloaded_evidence/recheck_evidence/final_verification/RESULT.json).
- [Historical suite result](downloaded_evidence/recheck_evidence/historical_verification/RESULT.json).
- [Numerical result](downloaded_evidence/recheck_evidence/final_verification/NUMERICAL_RESULT.json).
- [Retained declaration inventory](ALL_PUBLIC_THEOREMS.json),
  [historical provenance](historical_inputs/ORIGINAL_SOURCE_INVENTORY.json),
  and [scope explanation](HISTORICAL_CHECK_PLAN.md).
- [Reproduction instructions](REPRODUCE.md) and [saved-file guide](SAVED_FILES.md).

The final qualification and package checks are recorded separately in
`FINAL_VERIFICATION.json` and the external `FINAL_PACKET_RECEIPT.json`.
The complete review ZIP is `Experiments_001-008_Fresh_VM_Recheck_20260908.zip`
in `/home/richman954/`, with a neighboring checksum file.

The compiler, core libraries, and compatible compiled external libraries remain
trusted inputs. This work does not rebuild Lean/Mathlib or prove
source-to-artifact correspondence. It checks the accepted Lean proof and
control chain through Experiment 008 plus its latest numerical diagnostics;
it does not rerun every historical Python/Julia assurance test, figure build,
or archive-restoration exercise. Experiment 008's mathematical scope remains
a fixed finite Fourier band with constant noncommuting internal matrices.

Sealed combined source SHA-256:
`5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0`.

Fresh independent evidence archive: `exp001_008_fresh_vm_recheck_20260908T084432Z.tar.gz`.
SHA-256: `d28f0ae365647d4386e7fc5e81f9499efae882709519a8360f2ff0e1e667f16c`.
