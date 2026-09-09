# Failure and repair log

## Attempt 001 — infrastructure record loss

The first targeted invocation did not yield a command-session handle or a completed
timing record. Its empty log is preserved. No live process remained when checked.
This is classified as an infrastructure interruption, not a proof failure.

## Attempt 002 — bounded timeout

The original proof candidate was run with a 600-second outer timeout. It exited 124
after 600.433 seconds and emitted no diagnostic. Because an import-only probe later
also timed out after 180.279 seconds without output, this result does not attribute a
mathematical or proof-script error.

## Import-only probe — bounded timeout

An import-only source for the unchanged Experiment 002 production module exited 124
at its 180-second bound with an empty log. It confirms that the local import path can
take much longer than a small probe budget. No cache was cleared and no theorem was
weakened.

## Attempt 003 — bounded timeout

The same mathematical proof route was resubmitted once with a longer 1,800-second
bound. It exited 124 after 1,800.371 seconds with an empty log. This remained shorter
than historical 40–58 minute loads of the pinned environment, so it is classified as
another insufficient execution window, not a proof-script or mathematical failure.

## Qualifying build attempt 001 — attributable witness normalization failure

The first verbose production-target build ran from
`2026-09-06T11:44:51.880763Z` through `2026-09-06T12:43:33.324089Z`, exited 1
after 3,521.443 seconds, and is preserved in
`logs/final_verbose_production_build.log` (SHA-256
`b3856b186a718ed2ffbaee6fab951c31fdf4982578df0c0035c095cd03facf5a`).
The three headline declarations elaborated and printed, but the exact
non-Hermitian positive witness left the scalar goal `2 + Complex.I ^ 2 = 1` at
line 142. This is an attributable proof-script normalization failure, not a
mathematical counterexample and not a qualifying build.

The repair added Mathlib's exact theorem `Complex.I_sq` to the existing
normalization list. It does not change any statement, assumption, example, or
headline proof. The repaired source has SHA-256
`b95c08b2f3dae99464b42276249be7f4c76fce80df76fd9f21d5602202be1561`
and was committed as `83ce4ae4dccd45fb913a07fb86b9f4318bbf0a08` before the next build.

To avoid multiple redundant large-environment loads, all required positive
instantiations and exact counterexample witnesses remain consolidated into the
same production module. No proposition or frozen target was changed.

No timeout, import error, malformed source, tactic failure, or interrupted process is
counted as a mathematical negative-control pass.

## Assurance preflight repairs before control execution

A read-only closure audit found that the planned negative-control execution receipt
would have stored the detailed `global_diagnostic_checks` mapping inside a field for
which both release validators require scalar Boolean predicates. No control had yet
run and no false result was accepted. The isolated Python runner was repaired to keep
the detailed mapping in semantic results and store its fail-closed conjunction in the
receipt. A dedicated Python-only self-check now exercises both the all-true and one-
false cases.

The same audit found that the validators did not yet enforce the exact pinned Lake
path and source working directory for that control process, and that the complete
historical Experiment 002 evidence tree was omitted from the final Git-object
immutability set. The packager and fresh verifier now enforce those identities.
These repairs change only Experiment 003 assurance tooling; no Lean production
source, predecessor file, theorem statement, or proof was modified.

## Qualifying build attempt 002 — repeated normalization failure

The first normalization repair (`norm_num [..., Complex.I_sq]`) did not rewrite the
remaining power in that tactic context. The distinct second verbose build exited 1
after 3,371.020 seconds and preserved the same sole goal. Its complete log is
`logs/final_verbose_production_build_attempt002.log`, SHA-256
`e12c9afe94430bf6259a12031bdfa38086ed186bf560053c0f71a0b2c8d0f85b`.

Before another full build, the explicit sequence `rw [Complex.I_sq]; norm_num` was
checked in the minimal `Mathlib.Data.Complex.Basic` probe
`proof_attempts/ImaginarySquareProbe.lean`. The probe exited 0 after 29.283 seconds;
its source SHA-256 is
`fe22b1a39e2c04761397bf77292c7d1de1179693f2ba6885fbed1c203d06cc9f`.
Production was then changed only to use that exact checked rewrite after the existing
matrix normalization. The resulting production source SHA-256 is
`0618edd22fa0e36f9c3b28baa0bf97a22a068abafb6ae18810ac40b8f5f78ad6`.

## Qualifying build attempt 003 — syntactic rewrite mismatch

Attempt 003 ran from `2026-09-06T13:44:00.518181Z` through
`2026-09-06T14:36:45.191920Z`, exited 1 after 3,164.674 seconds, and is preserved in
`logs/final_verbose_production_build_attempt003.log` (582,869 bytes; SHA-256
`f045f33b5804bad38608bfa70668d49de5abee885248cc9abbf5b76d5d414767`).
All three headline declarations elaborated, printed, and reported only
`propext`, `Classical.choice`, and `Quot.sound`. The build failed later at line 150:
`rw [Complex.I_sq]` could not find `Complex.I ^ 2` in
`(1 + Complex.I * (Complex.I / 2)) * 2 = 1`. This is an attributable tactic-pattern
mismatch in the exact positive witness, not evidence against a mathematical claim.

The exact residual expression was isolated in `ImaginaryProductProbe.lean`. The
replacement `rw [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]; norm_num` exited 0
after 20.595 seconds. Production changed only to that sequence; no statement,
assumption, definition, or counterexample changed. The resulting source SHA-256 is
`19d6ffadd0e134f0becb39d6838335455409730b4683e7a408e03f9825861bd2`.
No remaining time was risked on another 52–59 minute target build in that window, so
the repair and both isolated rejection controls were explicitly untested at the
preserved partial checkpoint.

## Qualifying build attempt 004 — repaired module succeeds

The exact source saved at the partial checkpoint was built once in the renewed
window. The named target exited 0 after `3211.401704511998` seconds. Its complete
verbose log is `logs/final_verbose_production_build_attempt004.log` (582,939
bytes; SHA-256
`3d5f230bcc42d7fba67049e255cfe4655e4397c1db5c0f074c331e667d2aa2bc`).
This confirms the witness-only repair in the complete production module without
changing any headline theorem or assumption.

## Attempt-004 signature parser — source-prefix mismatch

The first parser invocation exited 1 and wrote no accepted audit because Lean
4.31's verbose output rendered each `#check`/`#print` informational first line as
`info: NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean:<line>:<column>:`.
The parser had expected an unprefixed marker and therefore returned an empty
signature sequence. The failing log and timing record are preserved.

The parser was repaired narrowly: it now requires exactly one begin/end pair
carrying that exact production-source prefix, strips only that prefix before the
existing strict parsing, and records the normalized-prefix count. It then passed
the real attempt-004 log and found no unexpected dependency. This did not modify
Lean production.

## Assurance self-check 010 — stale expected error text

The first self-check after the parser repair passed 12/13. Its missing-marker
case still expected the former error text. The test fixture already used the new
realistic source-prefixed format; only its expected diagnostic was updated.
Self-check 011 then passed 13/13. Both runs and their actual exit codes are
preserved. This is a repair of assurance-test bookkeeping, not a weakened gate.

## Final mathematical controls

One batched Lean invocation exited naturally with code 1 and exactly two
attributable proposition-level type mismatches. The strict runner accepted 2/2
unique controls and exited 0. It rejected the possibilities of timeout, truncated
output, source drift, wrong paths/lines, import or infrastructure errors, syntax
errors, and tactic/elaboration errors. The compiled positive witnesses remain in
the successful production target; no failure is counted merely because a tactic
failed.
