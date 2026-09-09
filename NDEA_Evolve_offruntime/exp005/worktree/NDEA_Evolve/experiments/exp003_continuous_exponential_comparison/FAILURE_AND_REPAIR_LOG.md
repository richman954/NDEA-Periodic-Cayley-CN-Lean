# Step 5 development failures and repairs

Every compiler invocation has an attributable timestamped receipt and complete
log in `evidence/`. Failed attempts are excluded from final qualifying evidence.

## Comparison attempt 1 — failed

Run `20260907T221848.294825Z_2` freshly compiled the predecessor chain and
the new exponential remainder. The comparison module then failed because
the exponential unitarity and power APIs required an explicit rational-scalar
normed-algebra instance on the complex continuous endomorphisms. There were
also triangle-inequality API mismatches, an overly broad absolute-value
rewrite, and unsuccessful polynomial simplification.

Repair: install a local instance via `NormedAlgebra.restrictScalars ℚ ℂ`, use
the three-point norm triangle lemma, target the denominator's absolute value
explicitly, and normalize the quadratic scalar polynomial.

## Comparison attempt 2 — failed

Run `20260907T223110.606852Z_2` accepted the scalar restriction and time-scaling
proofs. The remaining failure was in the quadratic polynomial normalization:
unfolding concrete continuous-linear-map operations prevented scalar-power
rewrite lemmas from matching, leaving inconsistent tactic atoms.

Repair: prove the polynomial identity in an arbitrary complex algebra with
an abstract variable, then specialize it to the operator. The mathematical
statement, constants, dimension generality, and small-step restriction were
unchanged.

## Comparison attempt 3 — passed

Run `20260907T223449.865617Z_2` accepted the full comparison source. Its four
requested axiom audits reported only `propext`, `Classical.choice`, and
`Quot.sound`. The remaining warnings concern tactic formatting suggestions.

Earlier failed logs may display `sorryAx` or placeholder declarations as a
consequence of Lean's error recovery. Those runs exited nonzero and cannot
qualify any mathematical claim. Final assurance requires successful runs,
current source hashes, and clean compiled dependency reports together.

## First controls run — two endpoint normalization failures

Run `20260907T223928.026678Z_2` accepted the scalar matrix-entry bridge,
sign-reversal and half-step controls, negative-time and zero-dimensional
instantiations, and both finite-equality counterexamples. The zero-time and
zero-generator proofs left expressions containing scalar multiplication of
zero inside the exponential after overly broad unfolding.

Repair: simplify the zero scalar and zero generator before unfolding the
Cayley definitions, and apply the exponential-zero identity explicitly.
No control proposition or production theorem was changed.

Run `20260907T224153.745723Z_2` showed that the initial direct rewrite still
did not match the concrete operator expressions. The final repair proved
each zero operator equality pointwise before rewriting the exponential.

Run `20260907T224412.105972Z_2` accepted all controls. The convergence module
had already passed on its first check, `20260907T223658.063025Z_2`.

Final closure uses the later fresh full modular and combined runs selected
by the integrity audit; these successful development checks alone do not
substitute for that final verification.

Some successful control logs retain an informational suggestion about using
`ring_nf`, alongside ordinary linter warnings. It is not a Lean `error:`
diagnostic. Qualification requires exit code zero, unchanged source hashes,
absence of actual error diagnostics and placeholder dependencies, and the
expected compiled axiom reports. Logs are retained verbatim.
