# Experiment 002 resumable state

Checkpoint target: JULIA-GREEN.

- Frozen mission remains unchanged.
- Original Experiment 001 is reference-only.
- Exact Julia certificate generation: PASS.
- Strict independent certificate validator: PASS.
- Valid configurations: 3/3 accepted.
- Unique invalid fixtures: 31/31 rejected.
- Total validator process invocations: 34.
- Universal Lean formalization: PENDING.
- External human review: PENDING.

Next smallest task: create a clean Experiment 002 Lean module importing Mathlib and
the narrow Cayley wrapper, reconstruct finite-dimensional denominator invertibility,
then prove unitary Cayley factors before ordered products and the defect theorem.

Do not import the recovered global theorem chain that transitively contains
`native_decide`; reconstruct the positive-definite invertibility step cleanly.
