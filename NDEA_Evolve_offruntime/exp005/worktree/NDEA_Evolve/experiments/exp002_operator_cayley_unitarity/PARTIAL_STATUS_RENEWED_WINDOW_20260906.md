# Renewed-window verified partial handoff — 2026-09-06

Status: **NEGATIVE CONTROLS GREEN; FINAL ROOT BUILD PENDING**.

Passed in or before this window:

- exact Julia discovery/certificate and 3/3 valid, 31/31 invalid validator suite;
- universal Lean core and strengthened positive/counterexample witness;
- 17/17 declaration/signature audit with axiom union exactly
  `[propext, Classical.choice, Quot.sound]`;
- production forbidden-token scan with zero matches;
- seven unique false Lean controls, all attributable type-mismatch rejections,
  using one natural exit-1 Lean process and one exit-0 runner invocation;
- renewed Experiment 001/assurance-v2 immutability post-check;
- hardened delivery-verifier and packager self-checks.

Not run because the measured 50–58 minute local Lean startup/build duration no
longer fit safely inside the renewed four-hour authorization:

- final verbose root `lake -v build`;
- final manifest, final annotated tag, release package, and fresh-extraction audit.

Exact next command from repository root:

```text
python3 experiments/exp002_operator_cayley_unitarity/assurance/run_logged.py --log experiments/exp002_operator_cayley_unitarity/logs/final_verbose_production_build.log --timing experiments/exp002_operator_cayley_unitarity/metadata/final_production_build_command.json --cwd /home/richman954/NDEA_Evolve_offruntime/exp002/worktree/NDEA_Evolve -- /usr/bin/timeout --signal=TERM --kill-after=10s 3600s /home/richman954/.elan/bin/lake -v build
```

Do not regenerate or rerun earlier green evidence. After that command exits 0,
create its production-build role metadata, finalize documents, then execute the
prepared manifest/tag/package/fresh-verification runbook. External review remains
**PENDING**.
