# Experiment 003 — Step 1 evidence

This directory belongs only to **Euclidean Resolvent Contraction**. It extends the
immutable Experiment 002 release without modifying it. The frozen statement is in
`FROZEN_SPECIFICATION.md`; the proof source is
`NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean`; its focused
instantiations and exact counterexample witnesses live in a nested namespace in the
same module so one qualifying compilation covers every positive declaration.

## Evidence map

- `mathematical_derivation.md` — short exact derivation.
- `dependency_and_reuse_map.md` — inherited versus newly proved declarations.
- `metadata/` — command records, environment bindings, and gate summaries.
- `logs/` — complete command output, including the qualifying verbose Lake build.
- `controls/lean/` — two isolated false statements, exact positive witnesses through
  the production witness module, strict batch runner, and preserved diagnostics.
- `assurance/` — source scan, declaration/dependency parser, packaging, and fresh
  delivery verification.
- `failure_and_repair_log.md` — failed/incomplete attempts and classifications.
- `final_evaluation_report.md` — claim boundaries and closure status.
- `FINAL_SHA256SUMS` — final internal inventory and final in-tree mutation before
  the release commit, annotated tag, packaging, and external-path verification.

## Replay boundary

The qualifying Lean/Lake records are the mathematical execution evidence. A fresh
delivery extraction verifies archive paths, bytes, Git identities, manifests, and
the semantics recorded in diagnostics. It is not described as a fresh kernel replay
unless Lean is actually executed from that extraction.

No fresh Julia run is part of this corollary. External review remains pending.
