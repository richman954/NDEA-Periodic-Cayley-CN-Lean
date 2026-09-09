
# Reproduction commands

All remote commands are run through the Chromebook Colab CLI against session
`ndea-evolve`. The active runtime is CPU-only. Exact timestamps, working directories,
elapsed times, stdout paths, hashes, and exit codes are in `logs/command_run.log` and
the adjacent JSON metadata files.

## Toolchain

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd /content/NDEA_Evolve
elan --version
lean --version
lake --version
/usr/local/bin/julia --version
git -C .lake/packages/mathlib rev-parse HEAD
```

Expected identities: elan 4.2.4, Lean 4.31.0, Lake 5.0.0-src+68218e8, Julia
1.12.6, and Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## Julia discovery and independent certificate validation

```sh
/usr/local/bin/julia --startup-file=no   experiments/exp001_fourier_stability/evidence_bundle/sources/julia/discover_fourier_stability.jl   /tmp/fourier_certificate_reproduced.json
/usr/bin/python3   experiments/exp001_fourier_stability/evidence_bundle/sources/tools/validate_certificate.py   /tmp/fourier_certificate_reproduced.json   experiments/exp001_fourier_stability/evidence_bundle/sources/julia/discover_fourier_stability.jl
```

Both expected exit codes are 0. A rerun timestamp changes the outer certificate and
run ID; the deterministic core hash and source binding remain auditable.

## Lean direct check and required verbose build

```sh
/root/.elan/bin/lake env lean   NDEAEvolve/Experiments/Exp001/FourierStability.lean
/root/.elan/bin/lake -v build   NDEAEvolve.Experiments.Exp001.FourierStability
```

Both expected exit codes are 0. The current complete verbose log has 8,694 lines,
564666 bytes, and SHA-256 `05c52e64892b2d6b4513c50f0b897d5ad0ce4cde22d8075d0ae90c80b887dae1`. The
separately preserved predecessor-runtime verbose log also has 8,694 lines and SHA-256
`9ca34494c57e057619e39c908e8d1fcc425f5f3f98cdcb4ff998f1e7b63841c6`.

## Signature and logical-dependency audit

```sh
/root/.elan/bin/lake env lean   experiments/exp001_fourier_stability/evidence_bundle/assurance/PrintAndAxiomAudit.lean
```

Expected exit code: 0. Complete output is
`assurance/theorem_signature_and_axiom_output.log`.

## Negative controls

The exact commands are stored in each control metadata JSON. Every command is
`lake env lean /tmp/<control>.lean` and is expected to exit 1 for the preserved,
mathematically relevant rejection shown in the corresponding `.rejection.log`.
An exit 0 is a control failure, not success.

- `NC01_FALSE_MODULUS` — false modulus claim: exit `1`, `PASS_EXPECTED_REJECTION`; diagnostic `negative_controls/NC01_FALSE_MODULUS.rejection.log`.
- `NC02_WRONG_AMPLIFICATION` — altered amplification expression: exit `1`, `PASS_EXPECTED_REJECTION`; diagnostic `negative_controls/NC02_WRONG_AMPLIFICATION.rejection.log`.
- `NC03_DROP_REAL_ASSUMPTION` — dropped real-parameter assumption: exit `1`, `PASS_EXPECTED_REJECTION`; diagnostic `negative_controls/NC03_DROP_REAL_ASSUMPTION.rejection.log`.
- `NC04_REVERSED_STENCIL_SIGN` — reversed stencil sign: exit `1`, `PASS_EXPECTED_REJECTION`; diagnostic `negative_controls/NC04_REVERSED_STENCIL_SIGN.rejection.log`.

Temporary false files are removed after capture; the archived `.lean.txt` files are
evidence only and are outside production sources.

## Manifest verification

From the evidence-bundle directory:

```sh
sha256sum -c PAYLOAD_SHA256SUMS
sha256sum -c SHA256SUMS
sha256sum -c SHA256SUMS.meta
```

All expected exit codes are 0. See the three verification logs.
