
# NDEA-Evolve Experiment 001 evidence bundle

This bundle records a complete Julia → Lean discovery-and-verification experiment
for periodic one-dimensional Fourier-mode stability of the centered negative discrete
Laplacian with a Cayley–Crank–Nicolson modal update.

Final mathematical outcome:

`lambda_h(theta) = (4/h^2)*sin(theta/2)^2`

`G(theta) = (1-i*(k/2)*lambda_h(theta))/(1+i*(k/2)*lambda_h(theta))`

and Lean proves `|G(theta)| = 1` for real `h,k,theta` with physical assumption
`h > 0`. Julia 1.12.6 independently emitted an exact/numerical certificate, and
Lean 4.31.0 independently proved the general result without trusting that certificate.

## Start here

- `experiment_goal.md` — mission and acceptance contract
- `mathematical_derivation.md` — transparent derivation
- `julia_lean_mapping.md` — exact trust boundary
- `reproducibility.md` — exact commands and expected exit codes
- `final_evaluation_report.md` — five-way claim classification
- `manifest_protocol.md` — layered hash design and causal exclusions
- `local_intake_reconciliation.md` — additive Chromebook intake status
- `recovery/README.md` — two runtime losses and verified recovery chain

## Primary artifacts

- Julia source: `sources/julia/discover_fourier_stability.jl`
- Julia stdout: `logs/julia_stdout.log`
- JSON certificate: `certificates/fourier_certificate.json`
- independent validator: `sources/tools/validate_certificate.py`
- Lean production evidence copy: `sources/lean/FourierStability.lean`
- project production source: `/content/NDEA_Evolve/NDEAEvolve/Experiments/Exp001/FourierStability.lean`
- current complete verbose Lake log: `build/verbose_lake_build.log`
- prior-endpoint complete verbose log: `build/verbose_lake_build_runtime_002.log`
- theorem/signature/dependency output: `assurance/theorem_signature_and_axiom_output.log`
- four negative controls: `negative_controls/`
- command ledger: `logs/command_run.log`
- failure/repair ledger: `logs/failure_and_repair.log`
- toolchain/dependency metadata: `metadata/`
- runtime-loss/checkpoint evidence: `recovery/`

## Exact environment

- elan: 4.2.4
- Lean: 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`
- Lake: 5.0.0-src+68218e8
- Julia: 1.12.6
- Mathlib: v4.31.0, revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- current pre-manifest Git checkpoint: `b3f775638b697001e7dd83bde8aa3bbf9f1c9933`
- tags at that checkpoint: `['exp001-preclosure-green-runtime-003']`

## Integrity

Run the three commands in `reproducibility.md`. `PAYLOAD_SHA256SUMS` covers every
substantive file, `SHA256SUMS` covers the payload plus stable payload-verification
receipts, and `SHA256SUMS.meta` authenticates the final manifest and its check log.

The historical baseline directory was lost with the original ephemeral VM and was
not recreated. Its verified identities remain in `metadata/baseline_reference.txt`.
No incoming research archive or transcript was used as proof input.
