# Experiment 003 Step-1 terminal in-tree state

- Original authorization: `2026-09-06T10:53:19Z` through
  `2026-09-06T14:53:19Z`; it ended with a verified partial checkpoint.
- Integration/closure authorization: `2026-09-06T15:29:53Z` through
  `2026-09-06T18:29:53Z` (`2026-09-06T11:29:53-04:00` through
  `2026-09-06T14:29:53-04:00`), monotonic interval
  `108435.76`–`119235.76` seconds from `/proc/uptime`.
- Frozen specification: unchanged.
- Predecessor: Experiment 002 commit
  `207cf3650499d69102dbfc21d26e68a7b7ac8b09`; post-check 61/61 PASS.
- Production source SHA-256:
  `19d6ffadd0e134f0becb39d6838335455409730b4683e7a408e03f9825861bd2`.
- Qualifying build: attempt 004 exited 0 after `3211.401704511998` seconds.
  It used the pinned Lake target
  `NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction`, compatible
  cache reuse, and did not build the project root. The complete 582,939-byte
  verbose log has SHA-256
  `3d5f230bcc42d7fba67049e255cfe4655e4397c1db5c0f074c331e667d2aa2bc`.
- Mathematical scope compiled in that target: the averaging identity,
  pointwise Euclidean nonexpansiveness, induced Euclidean operator norm at
  most one, alpha-zero/zero-generator/negative-alpha instantiations, and both
  positive counterexample witnesses. The declarations remain universal in
  finite dimension (including `n = 0`) and every real alpha.
- Negative controls: one Lean invocation exited naturally with code 1 after
  `3117.263893973999` seconds; exactly 2/2 unique false claims were rejected
  by attributable proposition-level type mismatches. The runner exited 0 and
  its strict acceptance contract passed. No timeout, import, syntax, tactic,
  or infrastructure error was counted as mathematical rejection.
- Signature/axiom audit: PASS for all three exact headline declarations;
  dependencies are exactly `[propext, Classical.choice, Quot.sound]`, with no
  unexpected dependency.
- Prohibited-token scan: PASS, 0 matches in the sole production source for
  `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, and `sorryAx` as whole
  case-sensitive tokens (comments and strings included).
- Assurance tooling: the first attempt-004 parser invocation failed because
  Lean 4.31 verbose output prefixes informational lines with source locations.
  A narrow, fail-closed parser normalization for the exact production-source
  prefix was added. Its first self-check exposed one stale expected diagnostic;
  the test was corrected, the repaired parser passed the real log, and the final
  Python-only self-check passed 13/13. Neither repair altered Lean production.
- Pre/post build source and dependency identity logs are byte-identical.
- Julia: not installed or executed; no fresh Julia evidence is claimed.
- Delivery: in-tree evidence is ready for the final manifest, commit/tag,
  package, and fresh-extraction verifier. Those necessarily post-date this
  manifest-bound status and are recorded in adjacent off-tree receipts.
- External assistant review: candidate advice only; no supplied draft is
  counted as compiler evidence. Human peer review and independent external
  review of this release remain PENDING.
- Steps 2–5: NOT STARTED.
- Verso: parked separately and not part of this environment.

Historical failed attempts and their exact diagnostics remain preserved; none
is promoted into qualifying evidence. This file is terminal for the in-tree
payload and must not be edited after `FINAL_SHA256SUMS` is written.
