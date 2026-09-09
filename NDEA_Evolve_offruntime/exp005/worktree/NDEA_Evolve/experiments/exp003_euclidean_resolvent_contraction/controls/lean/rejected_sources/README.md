# Rejected Lean controls

These two files are deliberately false and are never imported by a production
module. Each uses `exact` with a separately compiled proof of the proposition's
negation. The batch runner reconstructs both files from pinned hashes, executes one
bounded Lean process, and accepts only the two expected proposition-level type
mismatches with a natural child exit code of one.

- `01_strict_bound_false.lean`: falsely replaces the universal `≤ 1` conclusion by
  `< 1`; the one-dimensional zero generator makes the resolvent identity.
- `02_dropped_hermiticity_false.lean`: falsely drops Hermiticity; the exact scalar
  `A = i/2` makes the resolvent `2I`.

An import, parser, tactic, timeout, signal, or unrelated elaboration failure is not
accepted as a mathematical rejection.
