# Experiment 009 development failures and repairs

This note records the completed repair cycles for `InfiniteReference.lean`,
`CutoffSchedule.lean`, and the full-error bridge. Failed logs and receipts remain preserved.
They are development attempts, not accepted proof evidence. The final
[qualification](evidence/FINAL_VERIFICATION.json) selects the accepted modular
receipts for the final source hashes and records the combined checks.

## Import resolution

The first two runs requested additional Mathlib imports. The development
import path selected the earlier Experiment 006 Mathlib artifact directory,
where those additional module artifacts were absent. Both runs exited before
checking their new proof bodies.

| Source | Failed receipt | Resolution |
|---|---|---|
| `InfiniteReference.lean` | [08:56:27 receipt](evidence/20260908T085627.133402Z_InfiniteReference.json), [log](evidence/20260908T085627.133402Z_InfiniteReference.log) | Removed the unnecessary direct `Mathlib.Order.Filter.AtTopBot.Interval` import; the required API was already available. |
| `CutoffSchedule.lean` | [08:56:28 receipt](evidence/20260908T085628.981903Z_CutoffSchedule.json), [log](evidence/20260908T085628.981903Z_CutoffSchedule.log) | Removed the additional `Mathlib.Analysis.Real.Pi.Bounds` import and used the existing `Real.pi_le_four` bound. |

No predecessor file or external library artifact was changed for these repairs.
The portable final combined check uses its separately constructed external
dependency directory.

## Elaboration repairs

`InfiniteReference.lean` then exposed four local inference/representation
issues: converting integer absolute value to natural absolute value, fixing
the constant in a limit, specifying the integer index of an infinite sum,
and matching continuous coordinate projections to function evaluation.
The repairs used `Int.abs_eq_natAbs`, an explicit limit constant and integer
type annotation, and the projection identities in their evaluation form.

Failed attempt: [08:57:36 receipt](evidence/20260908T085736.380030Z_InfiniteReference.json)
and [compiler log](evidence/20260908T085736.380030Z_InfiniteReference.log).
The repaired source passed in **162.412 seconds**:
[09:03:05 receipt](evidence/20260908T090305.374216Z_InfiniteReference.json)
and [compiler log](evidence/20260908T090305.374216Z_InfiniteReference.log).

`CutoffSchedule.lean` exposed three local algebra/inference issues: arranging
a quotient before applying its inequality lemma, cancelling the denominator
in the exact final-time identity, and specifying the constant in the
consistency-cost limit. The repairs normalized the quotient, used field
cancellation, and supplied the explicit real constant. Power comparisons
were also simplified to the standard monotonicity lemmas.

Failed attempt: [08:57:24 receipt](evidence/20260908T085724.968768Z_CutoffSchedule.json)
and [compiler log](evidence/20260908T085724.968768Z_CutoffSchedule.log).
The repaired source passed in **152.247 seconds**, with all 22 printed axiom
audits restricted to `propext`, `Classical.choice`, and `Quot.sound`:
[09:03:06 receipt](evidence/20260908T090306.121731Z_CutoffSchedule.json)
and [compiler log](evidence/20260908T090306.121731Z_CutoffSchedule.log).

The repaired statements retain the infinite-reference hypotheses and the
same explicit cutoff, mesh, step, and horizon. These repairs introduce no
additional mathematical assumptions or proof axioms.

The full error bridge's first run found one namespace-resolution issue in
`add_le_add_right`: an opened predecessor namespace supplied the opposite
constant-summand orientation from the intended application. Replacing it with
the explicit two-argument `add_le_add` proved the same inequality. The parallel
weighted-error wrapper received the same explicit form before its first check.
No statement or assumption changed.

Failed bridge attempt: [09:08:31 receipt](evidence/20260908T090831.045197Z_InfiniteClosure.json)
and [compiler log](evidence/20260908T090831.045197Z_InfiniteClosure.log).
The repaired bridge passed in **158.185 seconds**:
[09:16:21 receipt](evidence/20260908T091621.054930Z_InfiniteClosure.json).

## Reading the receipts

Every completed attempt described above records unchanged before/after source
hashes, its actual exit code, compiler-log hash, and measured Lean execution
time. Receipt filenames and `start_utc` precede acquisition of the serial
compile lock; queue time is not part of `elapsed_seconds`. The longer wall
waits during development therefore do not imply compiler timeouts.

The accepted source SHA-256 values for this repair cycle are:

- `InfiniteReference.lean`:
  `ef31378a27fb871f22d662303a86cc8c90c1cc2ea18bb959b770d5cef71a38e1`.
- `CutoffSchedule.lean`:
  `41604c9d77be7780e933258a640deeacfbc3ddd0823aa2663667d1fc077be8f4`.

Later module attempts remain in `evidence/2026*.json` and their matching logs.
Use the final qualification for the complete accepted module set; this repair
note does not itself assert completion of checks that were still pending
when it was written.

## Colab runtime replacement

The earlier `exp008-fresh-recheck-r2` runtime became unavailable during source
delivery, before the Experiment 009 independent Lean check could start. The
Colab client reported a `404/401` session error for the source upload and a
separate plotting connection. This infrastructure failure produced no
Experiment 009 proof result on that runtime.

The prepared [verification request](remote_check/lost_runtime/FINAL_UPLOAD.json),
[environment record](remote_check/lost_runtime/ENVIRONMENT_EXPECTED.json), and
original initialization/launch scripts remain in `remote_check/lost_runtime/`.
Accepted local proof sources and receipts, numerical data, and earlier sealed
experiment evidence remained intact. This failure required no mathematical
assumption or proof change.

A new replacement CPU allocation, session `exp009-independent-check`, supplies
the independent environment under `/content/exp009_check`. Its bootstrap
downloads the pinned compiler and external libraries independently. The final
qualification selects the accepted check and transfer receipts from this
replacement environment.
