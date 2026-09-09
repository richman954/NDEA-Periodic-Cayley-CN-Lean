# Reproduce the Experiment 007 proof

The final proof consists of seven production/control modules plus the frozen
Experiment 006 combined foundation. `lean/Exp007Combined.lean` contains all
project proof source and imports only Mathlib/Lean libraries. The final audit
catalog contains every public theorem declared in the seven new files.
Development probes are excluded.

## Pinned environment

- Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`.
- Compiler SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- All nine package revisions are in `remote_check/bootstrap_inputs/lake-manifest.json`;
  the verifier checks its fixed SHA-256 and each repository revision/cleanliness.

Compatible external library artifacts are reused; Lean and Mathlib are not
rebuilt from source. The fresh Colab run independently downloaded the official
compiler distribution and library cache. No locally compiled project artifacts
were uploaded for that check.

## Verification

From an extracted packet, reconstruct the combined source and audit catalog:

```bash
python3 make_combined.py
```

Run the checker with the actual paths to the pinned installations. `--output`
must be a new directory. For a conventional local Lake package layout:

```bash
python3 verify_combined.py \
  --root /absolute/path/to/exp007 \
  --lean /absolute/path/to/lean-4.31.0/bin/lean \
  --mathlib /absolute/path/to/packages/mathlib \
  --other-packages /absolute/path/to/packages \
  --output /absolute/path/to/new-verification-output
```

For the fresh Colab layout, Mathlib is `/content/exp007_check/mathlib`, its
other packages are in `mathlib/.lake/packages`, and the compiler is
`/content/exp007_check/lean-4.31.0-linux/bin/lean`. The archived bootstrap scripts
record how that environment was created from pinned source metadata.

The checker reconstructs the combined source in memory, compares exact bytes
and the full audit catalog, checks proof policy, copies only external imported
library artifacts into a fresh isolated library, hashes them before and after,
and runs Lean with one worker. It rejects missing, duplicate, unexpected, or
unapproved axiom audits. A successful `RESULT.json` is required; a zero process
exit alone is not the full qualification.

Expected axiom set: `propext`, `Classical.choice`, and `Quot.sound` only.
The dependency artifact hashes are evidence of the bytes used during the run;
they are not a claim that the external libraries were rebuilt from source.

Run supporting numerical checks separately:

```bash
python3 numerical_checks.py
```

These diagnostics use only Python's standard library. The convergence figure
was rendered with Matplotlib from their saved results and is not proof evidence.
