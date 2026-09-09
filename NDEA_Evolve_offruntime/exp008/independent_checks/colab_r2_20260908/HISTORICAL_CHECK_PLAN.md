# Historical supplement for the second fresh Colab verification

Prepared September 8, 2026. **These are prepared inputs and static checks, not a new Lean result.** The fresh-VM controller must record the actual outcomes before this supplement can be described as verified.

The exact sealed Experiment 008 combined source contains 332 public project theorem/lemma declarations from Experiments 002–008. Its normal final audit prints only the 90 Experiment 008 declarations. The separate retained-predecessor audit overlay adds the remaining 242 names without altering those proof bodies. Experiment 001, Experiment 002's standalone adversarial witnesses, and several older standalone control modules are absent from that combined source.

This supplement fills those omissions with two passing source-only combined checks and six expected-rejection checks. It adds **141 distinct public theorem audits**, disjoint from all 332 retained names, for **473 distinct public declarations across Experiments 001–008**. These counts include supporting lemmas and control witnesses; they are not counts of independent mathematical endpoints. Four anonymous Experiment 001 examples are additionally checked through successful elaboration.

## Prepared checks

All paths below are relative to `historical_inputs/`. Exact SHA-256 values, source provenance, external imports, audit names, generated source-line positions, exit-code expectations, and rejection diagnostic requirements are in [HISTORICAL_INPUTS.json](historical_inputs/HISTORICAL_INPUTS.json).

| Check file | Required result | Additional coverage |
| --- | --- | --- |
| `checks/Exp001Historical.lean` | Exit 0; 16 named axiom audits; four unchanged anonymous examples elaborate | All 16 public scalar Fourier-stability theorems, including the original 12 selected audits, plus the four accepted positive witnesses |
| `checks/Exp002To005Controls.lean` | Exit 0; 125 named axiom audits | 28 Experiment 002 adversarial-witness theorems, 65 Experiment 003 Step 2–5 control/helper theorems, 21 Experiment 004 controls, and 11 Experiment 005 controls |
| `checks/Exp001_NC01_FALSE_MODULUS.lean` | Exit 1; exactly one targeted `unsolved goals` diagnostic at line 192 | Original false zero-step modulus claim; residual goal `False` |
| `checks/Exp001_NC02_WRONG_AMPLIFICATION.lean` | Exit 1; exactly one targeted `unsolved goals` diagnostic at line 199 | Original wrong-amplification update claim; residual goal `0 = 1 - Complex.I` |
| `checks/Exp001_NC03_DROP_REAL_ASSUMPTION.lean` | Exit 1; exactly one targeted `unsolved goals` diagnostic at line 196 | Original invalid complex-step generalization; residual goal `False` |
| `checks/Exp001_NC04_REVERSED_STENCIL_SIGN.lean` | Exit 1; exactly one targeted `unsolved goals` diagnostic at line 192 | Original reversed-stencil nonnegativity claim; residual goal `False` |
| `checks/Exp002RejectedControls.lean` | Exit 1; exactly seven targeted type-mismatch diagnostics | Original seven false claims concerning Hermiticity, real steps, order sensitivity, defect sign, inverse ordering, zero-step equivalence, and scalar semigroup merging |
| `checks/Exp003Step1RejectedControls.lean` | Exit 1; exactly two targeted type-mismatch diagnostics | Original false strict contraction and non-Hermitian contraction claims |

The expected-rejection checks contain deliberately false theorems and must never be treated as passing production proofs. Their acceptance requires the exact false-claim locations, diagnostic counts, and mathematical mismatch text. Missing imports, unknown identifiers, compiler crashes, timeouts, unrelated errors, and resource failures do not count as successful rejection. The original rejection inputs and their expected failures are distinct from the passing theorems that prove counterexamples.

## Why two positive combined sources

No existing accepted combined file covers this union of historical omissions. The existing Experiment 005 combined-control file includes only its own standalone controls, and the accepted Experiment 004 and Experiment 003 Step 5 combined files likewise include only their own controls. Re-running each entire predecessor chain would repeat substantial work.

`Exp002To005Controls.lean` therefore inlines the exact accepted Experiment 005 foundation once, followed by the missing accepted positive modules. It repeats the smaller Experiment 002–005 production chain as the necessary source-only environment for those controls; it does not repeat the larger Experiment 006–008 chain. Its 125 printed audits belong only to the newly covered modules. The negative Experiment 002 and Experiment 003 Step 1 drivers use only the smaller foundations they require.

The original Experiment 001 source imports the broad `Mathlib` module. That import is retained. The fresh VM therefore needs the corresponding full compatible library cache; an import-only adaptation has not been substituted for this check.

## Accepted source provenance

- Experiment 001 sources and controls come from `exp001/final/extracted_131a89fc12a0f7ae/evidence_bundle/`. Every selected source, pin file, and original control receipt matches its accepted `PAYLOAD_SHA256SUMS` entry. The original passing witness receipt records exit 0; the original four rejection receipts record exit 1 with the intended diagnostics.
- Experiment 002–005 standalone sources come from the frozen `exp005/worktree/NDEA_Evolve/` release. Every selected original and compatibility-shadow source matches its entry in the 889-entry Experiment 005 final manifest.
- The inlined `Exp005Foundation.lean` is copied exactly from the accepted Experiment 006 source, with SHA-256 `40386d3848f338f4ea89869a39a920e127674f5a42a471dfbd969901599a8785`.
- The Experiment 002 operator/witness and Experiment 003 resolvent compatibility sources are the already accepted Step 2 shadow sources used in later releases. Each was compared with its original release source: after removing import lines, their complete bodies are byte-identical. These existing import-only compatibility changes are recorded, not silently presented as the literal original file bytes.
- [ORIGINAL_SOURCE_INVENTORY.json](historical_inputs/ORIGINAL_SOURCE_INVENTORY.json) records the original absolute paths, copied paths, byte sizes, SHA-256 values, manifest keys, and all three import-only body comparisons. Exact accepted copies remain under `historical_inputs/originals/`; original manifests remain under `historical_inputs/provenance/`.

The generator preserves mathematical declarations, statements, proof bodies, anonymous examples, and false-control tactics. It collects external imports at the beginning, omits project imports whose sources are inlined, blanks old `#check`/`#print` commands, and appends the declared fresh audit commands. Blank lines preserve each source body's line mapping. The generator and complete copied-source inventory are pinned by the generated metadata. No sealed predecessor file is edited.

## Compiler, libraries, and execution

All selected releases use Lean **4.31.0** and Mathlib commit **`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`**. All nine dependency revisions match the accepted Experiment 008 bootstrap manifest. The required compiler binary SHA-256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Complete dependency pins and each check's external import list are recorded in `HISTORICAL_INPUTS.json`.

Reproduce the prepared source files without changing them:

```sh
python3 -B historical_inputs/build_checks.py --verify
```

For each check, the controller should run the pinned compiler with one job and an import path containing only independently downloaded external library artifacts and the compiler's core libraries:

```sh
LEAN_NUM_THREADS=1 LEAN_PATH="$external_library_path:$lean_core_path" \
  "$pinned_lean" -j 1 historical_inputs/checks/Exp001Historical.lean
```

Use the same command form for every listed source and apply that source's `pass` or `reject` expectation from the metadata. No local or uploaded project `.olean` file is required. Record source and dependency hashes before and after each check, compiler identity, commands, elapsed time, complete stdout/stderr, final exit code, and parsed audit or rejection evidence. Passing audit dependencies must be subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The source inventory, regeneration, proof-policy scans, exact diagnostic-line mapping, dependency revision agreement, and disjoint audit-set union passed statically; see [STATIC_VALIDATION.json](historical_inputs/STATIC_VALIDATION.json). No Lean or network operation was performed while preparing this supplement.

Compatible compiled external libraries and the compiler remain trusted inputs. This verification does not rebuild Lean or Mathlib, and matching source revisions and artifact hashes do not establish source-to-artifact correspondence. This plan covers the accepted Lean proof and control claims; it does not by itself rerun every historical Python assurance test, Julia numerical diagnostic, figure-generation step, or archive-restoration exercise.
