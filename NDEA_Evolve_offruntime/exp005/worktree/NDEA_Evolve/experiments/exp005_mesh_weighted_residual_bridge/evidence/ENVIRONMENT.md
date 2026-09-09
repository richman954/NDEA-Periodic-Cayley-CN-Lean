# Experiment 005 verification environment

The compiler is the existing pinned Lean 4.31.0 executable:

`/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean`

Its SHA-256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib is the clean tracked checkout at
`/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages/mathlib`,
commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The active cache is `/tmp/exp005_build`; `/tmp` is described as an ordinary
temporary-filesystem path, with no claim that tmpfs was used. The runner sets
`LEAN_PATH` to its `lib/lean` directory followed by the pinned toolchain library.
It holds `/tmp/exp003_lean_one_job.lock`, launches Lean with `-j 1`, and bounds
each command to 900 seconds by default. No root Lake build or dependency
download is part of this workflow.

## Verified development bootstrap

Bootstrap run `20260908T012444.267160Z_2` passed with exit zero in 42.18706
seconds. Its copy operation ran from 2026-09-08 01:24:44.346022 UTC to
01:25:26.299480 UTC and launched no Lean process.

The separate cache received 9,468 dependency artifacts totaling 1,746,661,568
bytes from `/tmp/exp004_build/lib/lean`. Every source artifact was checked
against its corresponding pinned-package cache artifact; every destination
SHA-256 matched the source. The old cache was read-only throughout.

Ten predecessor project `.olean` files totaling 5,422,680 bytes were also
copied for development. Current Exp005-inherited and original Exp004 source
hashes had to match the inputs of Exp004's final full serial run
`20260908T002534.597869Z_2`; each artifact had to match that run's recorded
output hash. Only explicitly recorded artifacts were copied. No additional
project sidecar files were claimed as verified outputs.

The complete records remain at the following relative evidence paths:

```text
27e5cf0ffd41e58ece80693730ad95d7a6ba59aba1143f64da57b8b79f77aa90  receipts/20260908T012444.267160Z_2_001_cache_bootstrap.json
c09beaaf1f8cbdbc18d9f33a48b3d88eb5ddb9f4d87ccd29e1f078318671346c  receipts/20260908T012444.267160Z_2_cache_bootstrap_manifest.json
752182b77e428d5da8d0198dc54ec0195b58105ebefdcabd9e9959ac99b7a4b4  logs/20260908T012444.267160Z_2_001_cache_bootstrap.log
```

The detailed manifest records every dependency and project source/destination
hash, source correspondence, final predecessor receipt hash, and byte count.
The bootstrap command receipt is explicitly classified as development.

## Final qualification remains separate

Before a fresh `production` or `controls` run, the runner moves all active
project cache artifacts into a run-specific retired directory outside
`LEAN_PATH`, records their hashes, and starts with an empty project cache.
Final `controls` verification rebuilds ten predecessor and three new modules,
then checks controls: fourteen serial Lean invocations. A separately generated
combined source must also pass without project `.olean` dependencies.

The release audit verifies the recorded cache reset, final source/receipt/log
hashes, binary and Mathlib pins, and predecessor preservation. Development
bootstrap success is not a final Experiment 005 verification verdict.
