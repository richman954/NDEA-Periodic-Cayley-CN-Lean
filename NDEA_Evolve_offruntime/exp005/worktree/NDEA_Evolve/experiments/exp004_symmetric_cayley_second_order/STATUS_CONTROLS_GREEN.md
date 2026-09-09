# Controls verified — 2026-09-08 00:24 UTC

The complete controls source passed Lean in run
`20260908T002238.924155Z_2_001_NegativeControls`, exit zero,
112.081212 seconds, with unchanged input source hashes.

All twenty-one public control declarations have compiled axiom rows containing
only `propext`, `Classical.choice`, and `Quot.sound`.
Source SHA-256:
`ec418e29f664fbe0d5fcb785256344b65c1cca9f2105a4fd792376e5b3928f6f`.

The controls cover the edge cases, exact scalar conventions and their
production representation bridges, a finite-step exponential inequality,
and a noncommuting Hermitian Pauli quadratic-coefficient witness.
The one development repair was an explicit matrix type annotation. Harmless
linter warnings and a tactic suggestion are retained verbatim in the log.

All new production and control sources have now passed individual Lean
checks. The final full-chain modular and combined-source verification,
integrity audit, manifest freeze, and release recovery remain pending.
This historical snapshot does not claim final release closure.
