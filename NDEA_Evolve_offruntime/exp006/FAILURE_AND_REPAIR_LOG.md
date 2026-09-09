# Development failures and repairs

All attempts remain in `evidence/` with per-command source hashes and logs.
None of these attempts is presented as the final qualification run.

1. Broad tactic imports caused two 240-second import timeouts. Production
   imports were narrowed; the transitive pinned dependency artifacts were
   copied into a flat campaign-owned cache. Subsequent scalar/grid runs took
   roughly 30–100 seconds on this workstation.
2. The real-to-complex phase derivative exposed an elaboration mismatch among
   Mathlib scalar instances. A proposed local instance workaround was removed.
   The repair uses Mathlib's own `using!` elaboration pattern; both a narrow
   probe and a PiL2-loaded probe passed before the complete scalar file passed.
3. Scalar proof repairs supplied explicit nonnegativity to an absolute-value
   rewrite and used the cosine inequality's implicit argument correctly.
4. The finite-grid matrix proof required `Equiv.Perm.inv_def` to normalize
   permutation inverse and `Equiv.symm`. Endpoint wrap and Hermitian proofs
   passed, and the repaired whole grid module passed all five audits.
5. Bridge repairs added required type-application spaces, unfolded a lambda
   in the shifted periodicity proof, removed a no-progress `dsimp`, and used
   the explicit scalar coordinate identity for the reference samples. The
   actual budget, fixed-time theorem and varying-mesh theorem passed together.
6. The admissible-grid control used `Real.pi_le_four`, already in the selected
   imports, instead of the unavailable stricter theorem. All six controls
   passed. No extra numerical premise was introduced.
7. The initial combined-check import sandbox exposed external namespace
   directories but omitted root artifacts such as `Aesop.olean`. Its setup
   now includes each external namespace's root artifact/sidecars as well as
   its directory. No project artifact is exposed by that import path.
