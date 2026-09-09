# Exp006 progress checkpoint

2026-09-08 05:04 UTC.

Checked locally with pinned Lean 4.31.0:
- PeriodicGrid: 5 theorems including Hermitian cyclic matrix and endpoint wraps.
- PeriodicModeResidual: complete file passes, including periodic nonconstant PDE
  solution, exact centered stencil, spatial symbol estimate and actual scalar
  Cayley residual estimate. Three selected scalar audits are clean; the final
  combined run will audit all 40 new production/control theorems.

Remaining: compile the actual Exp005 matrix-factor bridge and controls, then
fresh combined verification with project artifacts excluded from its imports.
The frozen Exp005 foundation is being rebuilt in an independent Colab VM.
No full Exp006 completion verdict has been issued.

Prior failed development attempts and logs are preserved. Broad tactic-import
probes timed out. Narrow imports and a copied dependency closure made normal
runs bounded. The real-to-complex derivative issue was repaired with Mathlib's
`using!` elaboration, validated both with and without PiL2 imports; no local
instance workaround remains in production source.
