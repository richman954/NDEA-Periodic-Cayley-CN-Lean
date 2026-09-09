# Fourier coefficient representation bridge

Status: accepted modular development check at 2026-09-09T13:00 UTC. Lean exited
0 in 7.100 seconds with four explicit axiom reports containing only `propext`,
`Classical.choice`, and `Quot.sound`; no warnings or errors. Current source and
imported artifacts remained unchanged. The transferred archive passed SHA-256,
CRC, source/log/runner/artifact bindings, and matching local artifact installation.
Source SHA-256:
`0b550fad136360d5bbb2f9c68f595cf5a2f274a33c0f1bd393cb3b9c50d44918`.
Receipt: `../evidence/remote_development/2026-09-09T130009.044711_0000_FourierCoefficientBridge/RESULT.json`,
SHA-256 `0bab210adf0b5ce26130de4c9e62bdc9b85e652511627c1572277cbc44ea7647`.
Its adjacent `compiler.log`, `TRANSFER_VALIDATION.json`, and `MODULE_AUDIT.json`
retain the complete evidence. Independent qualification remains pending.

The transferred proof pattern is the direct specialization of Mathlib's
`fourierCoeffOn_eq_integral` used by
`NavierStokes.SmoothFourierData.unitCoeff_eq_integral`, lines 29–32 of
`NavierStokes/SmoothFourierData.lean`, external commit
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`. That source has SHA-256
`980b746ca551345d88351dd961d30b69876c68c84f0c758445593025d9dbc642`.
The upstream root LICENSE is Apache-2.0; no root NOTICE file was present.
The parent task preserves the original license separately. No external Lean
module is imported and no external toolchain or Mathlib version is adopted.

Local changes use the physical interval `[0, 2*pi]`, a real normalization
factor `(2*pi)⁻¹`, and complex scalar action on normed-space values. A private
lemma identifies Mathlib's character with the existing NDEA
`phase (-(n : ℝ) * x)`. There is no unit-period rescaling argument.

The main accepted consumer is
`physicalFourierCoefficient_reconstruction M h y m`: the normalized continuum
coefficient of `fourierReconstruction M h y` at `oddFrequency M m` equals the
computed finite-grid `fourierCoefficient M h y m`. The general finite-synthesis
formula extracts exactly matching frequencies, and its immediate corollary
vanishes outside `Set.range (oddFrequency M)`.

The integral formula needs only a complex normed space. The mode-integral
argument additionally uses completeness, satisfied by the spinor space `E 2`.
Finite synthesis supplies its own continuity. No mesh, smoothness, summability,
or assumed band-representation hypothesis is added to the coefficient identity.
For the same synthesis to recover arbitrary original grid values, the separate
accepted node-fidelity theorem still requires `(2*M+1)*h = 2*pi`.

This is a coefficient representation bridge for future spatial, aliasing and
tail analysis. Continuum/discrete Parseval was already proved in FourierNorm.
No new refinement, convergence, derivative-decay, or independent-qualification
claim follows from this module.

The initial transport failure, missing AddCircle artifact failure, interrupted
lock wait, and two rejected elaboration drafts are preserved separately. The
pinned AddCircle cache restoration passed; all 228 new artifacts match local
pinned Mathlib hashes. Its original helper retained a notebook-global lock;
the exact executed bytes and receipt are preserved, and an additive helper uses
a context manager. A single Python-kernel restart released that lock while
retaining the VM, compiler, dependencies, and accepted project files. The final
Lean repair expands Mathlib's character before simplifying its dependent circle
period, then applies the explicit phase identity. No mathematical assumption
or normalization changed during these repairs.

## Reproduce the development check

Use the unchanged NDEA Lean 4.31.0 / Mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f
environment and the accepted predecessor/module artifacts named in the receipt.
From the existing local recovery layout, the standalone pinned runner is:

```sh
python3 /home/richman954/NDEA_Evolve_offruntime/exp016/run_lean.py lean/FourierCoefficientBridge.lean
```

It writes a new dated compiler log and source-bound receipt, checks the pinned
compiler hash, and prints the module's four transitive axiom reports. Require
exit 0, the accepted source SHA above before/after, and only the three standard
axioms. This is an incremental development replay, not isolated qualification.
The actual accepted run's exact command, LEAN_PATH, runner, source/import/artifact
hashes and bootstrap receipt are recorded in RESULT.json and its captured runner.
For the existing Colab development layout, use `remote_dev/prepare_check.py
FourierCoefficientBridge`, execute its generated command with `colab exec`, then
validate the downloaded result archive with `remote_dev/accept_result.py` and
the printed archive SHA. The full isolated/fresh-runtime milestone procedure
remains the unchanged Exp016 qualification gate; do not replace it with this
incremental replay. No upstream build, upgrade or .olean transfer is required.
