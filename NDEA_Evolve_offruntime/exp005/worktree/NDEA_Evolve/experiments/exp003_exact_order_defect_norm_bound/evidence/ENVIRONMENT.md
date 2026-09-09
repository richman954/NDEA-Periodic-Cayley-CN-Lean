# Verification environment

Recorded at `2026-09-07T09:16:29-04:00` in timezone
`America/New_York`.

- OS: Linux `6.6.135-09383-g1140e4f27e24`, x86_64.
- Lean: `4.31.0`, commit
  `68218e876d2a38b1985b8590fff244a83c321783`, release build.
- Lake: `5.0.0-src+68218e8`.
- Git: `2.39.5`.
- Toolchain library:
  `/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/lib/lean`.
- Pinned package cache:
  `/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages`.
- Step 2 worktree:
  `/home/richman954/NDEA_Evolve_offruntime/exp003_step2/worktree/NDEA_Evolve`.
- RAM verification root: `/dev/shm/exp003_step2_shadow`.
- Available RAM filesystem at the environment check: 3.2 GiB.

The ordinary broad-import path repeatedly blocked in host kernel filesystem
reads before reaching source diagnostics. The bounded workaround computes the
transitive closure of the exact required imports, copies the corresponding
Lean artifacts into `/dev/shm`, and invokes the pinned `lean` executable with
`-j 1`. The modular run used a 900-second bound per Lean invocation and a
3600-second outer bound. The combined run used a 900-second Lean bound and a
1500-second outer bound. Only one Lean/Lake job was active at a time.

No package, toolchain, `lakefile.toml`, `lake-manifest.json`, or
`lean-toolchain` file was modified.
