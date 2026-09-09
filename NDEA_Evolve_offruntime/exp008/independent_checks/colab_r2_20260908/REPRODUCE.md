# Reproduce the additional fresh VM double-check

This folder supplements the sealed Experiment 008 packet. It does not replace
any accepted source or mathematical result. The frozen accepted input archive
is `reused_inputs/final_sources_5fbcbcb39be7d681.tar.gz`.

## Verification sequence

1. Allocate a new Colab CPU session and run `initialize_vm.py` before uploading
   project inputs. The original additional session was
   `exp008-fresh-recheck-r2`, distinct allocation recorded in `VM_ALLOCATION.json`.
2. Upload `reused_inputs/bootstrap_inputs.tar.gz` to
   `/content/exp008_bootstrap_inputs.tar.gz` and `reused_inputs/bootstrap.py` to
   `/content/exp008_bootstrap.py`. Execute `reused_inputs/start_bootstrap.py`.
   Require `bootstrap/RESULT.json` to pass before continuing.
3. Execute `start_full_cache.py`; require `EXTRA_IMPORTS.json` exit 0. The full
   pinned Mathlib cache is needed because the exact Experiment 001 source
   imports `Mathlib`.
4. Upload the sealed final-source archive and `reused_inputs/FINAL_UPLOAD.json`
   to their recorded `/content/exp008_check/` paths. Execute
   `reused_inputs/start_final.py` and require its final result to pass.
5. The supplemental proof inputs are in `historical_suite_sources.tar.gz`;
   `SUITE_UPLOAD.json` records all file hashes and the suite runner hash.
   Upload both to the recorded paths. The execution-tool archive and upload
   request are identified by `TOOLS_UPLOAD.json`; upload them and execute
   `install_tools.py`, then execute `start_suite.py`.
6. Inspect `status_short.py` until `historical_verification/RESULT.json` passes.
   This requires three positive source checks and six rejection checks. Each
   rejection must return ordinary Lean exit 1, with its exact intended error
   lines, diagnostic forms, and expected false-claim fragments.
   Also upload the unchanged `numerical_checks.py` to
   `/content/exp008_check/final_verification/numerical_checks.py` and execute
   `run_numerical.py`. Its receipt must pass; these are the current Experiment
   008 floating-point diagnostics, separate from the Lean proofs.
7. Execute `export_recheck.py`, then download its `EXPORT_RECEIPT.json` and
   named evidence archive into this local folder. Run `python3 -B check_download.py`
   from a workspace with the unchanged Experiment 008 files and previous
   evidence. It requires a fresh extraction destination and refuses to
   overwrite successful transfer/comparison receipts.

The shared runtime path `/content/exp008_check` is deliberately reused only on
a newly allocated VM. Its initial absence is checked. For another run, choose
a new session name and new local evidence directory; keep this evidence intact.

## Reconstruction and coverage

`historical_inputs/build_checks.py --verify` validates reconstruction from the
retained exact historical sources. `build_audit_inventory.py` reconstructs the
retained public declaration inventory from the sealed source. Their provenance
records reference the unchanged predecessor workspace and its preserved files.

`AllCheckpointAudit.lean` in `suite_payload/` has the exact sealed Experiment 008
source as its prefix, followed only by 242 additional predecessor axiom prints.
It audits 332 public declarations. Two historical checks add 141 distinct
public audits; six negative drivers exercise 13 deliberately false claims.
Four original anonymous Experiment 001 positive examples are also elaborated.

The exact source and historical suites use isolated external library import
paths with no project build artifacts. The new VM downloads its own compiler
and compatible library cache from the pinned sources. Lean 4.31.0, its core
libraries, and compiled external dependencies remain trusted inputs. These
checks do not rebuild Lean/Mathlib or prove source-to-artifact correspondence.

The earlier `recheck_tools.tar.gz` and `TOOLS_UPLOAD_v1.json` are retained as
packaging history. Version 2 corrects export coverage for extensionless input
files; version 1 was not installed or used to run the checks. Neither version
changes a mathematical source or proof statement.
