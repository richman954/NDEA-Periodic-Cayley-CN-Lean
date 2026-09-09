# Second runtime-loss recovery note

Status: PARTIAL CHECKPOINT — NOT FINAL GREEN

The first `ndea-evolve` endpoint was lost earlier in Experiment 002. Under the
frozen recovery policy, one standard CPU-only replacement was created and the
verified Julia-green Git bundle was restored at commit
`0e913e9cadd5c25ff9c982c5be373cbe38618c50`.

On that replacement, the production universal Lean core reached two genuine
proof checks:

- direct Lean development attempt 5 returned exit code 0;
- a full verbose Lake build of `NDEAEvolve.Experiments.Exp002.OperatorCayley`
  returned exit code 0 after 8,558 jobs.

The replacement then returned 404/401 during a subsequent file operation and
the CLI removed its `ndea-evolve` name. A later read-only server listing showed
the same endpoint only as an unidentified `?` assignment. It was not stopped,
renamed, or reused. The authorized one-replacement ceiling was therefore
treated as exhausted.

The CLI's local execution history survived. The successful verbose build log
was recovered byte-for-byte as
`../../logs/verbose_lake_build_operator_attempt_001.recovered_exact.log`; its
SHA-256 exactly equals the remote-reported
`2eae3878f600b44ee9f6263e789e246f2374e39c73be8ddaa48569ed38921aa5`.
Development attempts 1–5 and the pre-build witness attempt were also recovered
byte-for-byte under `recovered_attempt_logs/`. The complete raw CLI history is
preserved outside this Git worktree at:

`/home/richman954/NDEA_Evolve_offruntime/exp002/recovery/20260905T_second_runtime_loss/colab_history_full.jsonl`

`OperatorCayley_attempt5_source_reconstructed.lean.txt` reconstructs the exact
source for direct attempt 5: its SHA-256 is
`19de0fa01d1a51397e55604ecefc5ff30c282aa018adb8d38af5b89959c09d09`,
exactly matching the independently recorded remote `source_sha256`.
`OperatorCayley_remote_verbose_source_reconstructed.lean.txt` applies the one
subsequent recorded edit (removal of an unused simp argument) and is the source
uploaded immediately before the verbose build. Its hash was not emitted by the
verbose wrapper, so that latter association is a documented provenance
reconstruction, not an independent hash binding.

The old remote build contained the same mathematical core but preceded the
subsequent header/style-only cleanup. The cleaned source in this checkpoint was
checked independently on the Chromebook with the exact pinned Lean 4.31.0 and
Mathlib revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; that direct
check returned exit code 0. This local check is not represented as a remote
Colab execution.

No second replacement was created. Exp001 artifacts were not modified.
