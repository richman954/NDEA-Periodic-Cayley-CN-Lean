# Development failures and repairs

This log distinguishes failed proof invocations from source review changes,
deliberate assurance-tool rejection tests, and harmless warnings. Full compiler
receipts and logs are retained separately, including unsuccessful attempts.

## Initial source review

Before the first stability compilation, ambiguous left/right additive-order
helper calls were replaced by explicit `add_le_add` arguments. Before the
first family compilation, constants in the limit proof were made explicit.
Neither change followed a failed Lean invocation; theorem statements were
unchanged.

## Accepted initial modules

Weighted stability passed its first compilation (run
`20260908T012630.694700Z_2`). The stage-residual module also passed its first
compilation (`20260908T013150.342988Z_2`). Its existing
`ContinuousLinearMap.mul_apply` call triggered a deprecation warning in the
pinned library, not a proof failure or an unapproved axiom dependency.

The family module passed its first compilation
(`20260908T013638.233420Z_2`). Lean notes that the positive-spacing premise
is not referenced by the proof: the algebraic bound is valid more generally,
while the statement deliberately restricts physical mesh spacings to positive
values. This is an unused-hypothesis warning, not a missing proof obligation.

## Assurance rejection control

The assurance tooling was checked to reject nonexistent qualifying run
identifiers. That deliberate rejection is a tool control, not evidence that
a mathematical negative control failed to compile. Python syntax and shell
wrapper checks passed. No Lean invocation was launched by the cache bootstrap
or the assurance tooling's read-only tests.

## Control attempt 1

Run `20260908T014033.831027Z_2` exited 1. Ten control theorem audits succeeded;
the final outer-only versus single-Cayley witness encountered a coercion
mismatch between the matrix star-algebra equivalence and its underlying ring
equivalence. The failed declaration's diagnostic axiom row includes Lean's
error-placeholder `sorryAx`; this failed invocation cannot qualify the
release. No placeholder was written into source or accepted as a proof.

The repair makes the `Chat` representation explicit in that conversion.
The missing-time-factor witness was also strengthened to include its zero
initial-error term directly in the strict inequality; its intended mathematical
counterexample is unchanged. The unused recurrence index was renamed `_j`.
The complete failed log and receipt are preserved.

Control attempt 2 (`20260908T014609.379899Z_2`) still encountered the inherited
ring-equivalence coercion mismatch after unfolding `Chat`. The next repair
selects `EquivLike.injective` explicitly for the star-algebra equivalence,
rather than dot notation selecting the inherited ring-equivalence theorem.
All other controls, including the strengthened initial-error inequality,
compiled in this second attempt. Both failed invocations remain excluded
from release qualification.

Control attempt 3 (`20260908T015115.937664Z_2`) passed with exit 0 and all 11
audits restricted to the accepted standard axioms. The explicit
`EquivLike.injective` repair resolved the conversion mismatch. Harmless
deprecated identity-application warnings remain in the pinned environment.

Further proof attempts and final run qualification are recorded in the
timestamped evidence and final evaluation report.
