# Step 5 verification environment

The isolated project retains the predecessor's `lean-toolchain`,
`lake-manifest.json`, and project configuration byte for byte.
The pinned Mathlib commit is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`;
the shared package checkout was checked against that revision.

The runner invokes the explicit Lean 4.31.0 binary at
`/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean`.
Each command receipt records its binary SHA-256, full command, source hashes,
start/end UTC times, elapsed time, timeout outcome, and log hash.
Commands use `-j 1`, `LEAN_NUM_THREADS=1`, and a shared exclusive process lock.
The default per-command timeout is 900 seconds.

Compatible transitive import artifacts are copied from
`/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages` into the
separate disposable cache `/tmp/exp003_step5_build/lib/lean`.
The initial closure contains 9,468 artifacts totaling 1,746,661,568 bytes;
later preparations include additional control imports and have their own
receipts. This run uses the ordinary temporary filesystem. It reuses the
predecessors' narrow-import shadow sources, but does not claim a tmpfs run.

No package download, dependency update, root-project build, Julia execution,
or numerical sampling is part of this proof chain. Numerical evidence is
unnecessary for the universal analytic results and exact compiled controls.
Development attempts and final qualifying attempts have separate receipts;
only successful final attempts whose source hashes match the delivered
sources can qualify the release.
