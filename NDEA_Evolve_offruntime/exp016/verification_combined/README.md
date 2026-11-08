# Combined-source check of the verified Exp016 convergence closure

This is a complementary, bounded source check. It is not an Exp016 seal, a new theorem, or an independently implemented kernel result.

## Preserved successful baseline

Commit `5e2b5522bf7ddee673b040c64ba28e3863d94b38`, GitHub Actions run `42437947802`, passed both fresh modular checks and the final downloaded-evidence audit/comparison. Both jobs compiled 96 project modules, the four explicit theorem contracts, the 23-declaration axiom audit and four negative controls, and passed the pinned-toolchain preflight and fresh same-kernel replay. `VERIFIED_BASELINE.json` records the artifact identities and independently rehashed downloaded ZIPs. It does not replace the actual source, logs or kernel checks.

This branch does not change the successful branch, the Lean sources, theorem statements, existing verifier, existing workflow, main, dependency pins, historical acceptance ledgers, or sealed predecessor sources. All mathematical inputs and retained verifier bytes are compared against that exact successful commit before execution.

## Next check

`combined_check.py` gathers the same 96-module dependency closure and unchanged VerificationContracts file. It generates one source containing the same proof bodies. Only single-line import and diagnostic commands are removed. External imports are collected at the start; each original source is wrapped in a section, and its implicit end-of-file anonymous sections are closed explicitly. Every removed directive and source hash is recorded. Unsupported syntax, missing imports, mismatched scopes, duplicate public names and proof escapes stop generation.

The resulting 97 source units contain 1,017 catalogued public theorem/lemma declarations, including all 23 required target declarations. This is a public-theorem catalog, not a count of all definitions or private lemmas. The new workflow compiles the combined source with **no project object directory on LEAN_PATH**. External pinned library objects remain trusted inputs. It audits the complete generated public catalog, then replays the combined proof environment with the same pinned `leanchecker --fresh`. It records the exact source, compiler commands, logs, object hash and final receipts, and preserves failure evidence.

A successful combined run would establish this source-bound combined check only. The transformation is deliberately limited and reproducible, but independent semantic review remains required. This is the convergence dependency closure, not every standalone Exp016 control or every historical predecessor experiment. Do not call it complete experiment qualification.

## Local checks versus Lean execution

Sixteen Python generator tests pass locally, including nested-comment handling, exact body retention, scope closure, import ordering, duplicate names and rejection of proof escapes. Generation on all 97 actual source units succeeds and includes all 23 target declarations. Those checks do not compile Lean. The authoring container has no Lean/Lake executable and cannot resolve GitHub hosts directly; hosted Actions must supply actual compiler and replay evidence.

## Reproduce

Use the exact tested commit, including its history so the successful baseline commit is available. Choose a new output directory outside the checkout:

```sh
python3 -m unittest discover -s NDEA_Evolve_offruntime/exp016/verification_combined -p 'test_*.py' -v
python3 NDEA_Evolve_offruntime/exp016/verification_combined/combined_check.py prepare --repo "$PWD" --output /absolute/new/output
# Provision output/deps using its unchanged lean-toolchain and lake-manifest.json.
python3 NDEA_Evolve_offruntime/exp016/verification_combined/combined_check.py run --repo "$PWD" --output /absolute/new/output
```

Read COMBINED_RESULT.json only alongside the exact commit, COMBINED_INPUTS.json, the compile/replay logs, and evidence manifest. Missing/skipped checks are not passes. The original modular assurance checkpoint stays valid for its recorded source revision even if this additional source transformation exposes a packaging problem.

Remaining broader work includes a genuinely independent semantic review, the project's full controls and finalizer/transfer requirements, and continuous-time reconstruction where claimed. A finite-grid-time maximum does not imply convergence between steps without a separate argument. No automatic merge or acceptance promotion is performed.
