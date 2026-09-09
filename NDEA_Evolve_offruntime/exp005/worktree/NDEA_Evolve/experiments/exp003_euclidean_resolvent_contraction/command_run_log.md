# Command and run log

The machine-readable records in `metadata/` are authoritative for argv, working
directory, monotonic elapsed duration, timestamps, actual exit code, and log hash.

## Development attempts

1. Targeted attempt 001: infrastructure session record incomplete; preserved and not
   classified as a proof result.
2. Targeted attempt 002: `lake env lean` on the first candidate, outer timeout 600s;
   exit 124, empty output, not a mathematical failure.
3. Import-only probe: `lake env lean` on an import-only source, outer timeout 180s;
   exit 124, empty output, establishing that the small bound was insufficient.
4. Targeted attempt 003: the revised candidate with an outer 1800s bound; exit 124
   after 1,800.371 seconds with empty output, not a mathematical failure.

## First verbose production-target result

Attempt 001 used the exact qualifying argv below but exited 1 after 3,521.443 seconds
because one positive witness left `2 + Complex.I ^ 2 = 1` unsolved. The complete
583,193-byte log has SHA-256
`b3856b186a718ed2ffbaee6fab951c31fdf4982578df0c0035c095cd03facf5a`;
the exact timing and exit record is
`metadata/final_verbose_production_build_command.json`. It is preserved as a failed
attempt, not reused as qualifying evidence.

## Qualifying sequence

The block below was the planned sequence. Its first paths were occupied by failed
attempt 001 and must not be replayed verbatim. Attempt 003 instead used
`logs/final_verbose_production_build_attempt003.log` and
`metadata/final_verbose_production_build_command_attempt003.json`; any future parser
may consume that log only if the timing record says exit code 0.

The final sequence uses the pinned `/home/richman954/.elan/bin/lake`, one Lean/Lake
process at a time, and distinct no-overwrite evidence paths:

```text
PYTHONDONTWRITEBYTECODE=1 python3 experiments/exp003_euclidean_resolvent_contraction/assurance/run_logged.py \
  --log experiments/exp003_euclidean_resolvent_contraction/logs/final_verbose_production_build.log \
  --timing experiments/exp003_euclidean_resolvent_contraction/metadata/final_verbose_production_build_command.json \
  --cwd /home/richman954/NDEA_Evolve_offruntime/exp003/worktree/NDEA_Evolve -- \
  /usr/bin/timeout --signal=TERM --kill-after=10s 3600s \
  /home/richman954/.elan/bin/lake -v build \
  NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction

NDEA_LAKE=/home/richman954/.elan/bin/lake \
NDEA_EXP003_NEGATIVE_CONTROL_TIMEOUT_SECONDS=3600 \
PYTHONDONTWRITEBYTECODE=1 python3 \
  experiments/exp003_euclidean_resolvent_contraction/controls/lean/run_negative_controls.py

PYTHONDONTWRITEBYTECODE=1 python3 experiments/exp003_euclidean_resolvent_contraction/assurance/run_logged.py \
  --log experiments/exp003_euclidean_resolvent_contraction/logs/final_signature_axiom_audit_parser.log \
  --timing experiments/exp003_euclidean_resolvent_contraction/metadata/final_signature_axiom_audit_parser_command.json \
  --cwd /home/richman954/NDEA_Evolve_offruntime/exp003/worktree/NDEA_Evolve -- \
  python3 experiments/exp003_euclidean_resolvent_contraction/assurance/parse_signature_axiom_audit.py \
  --log experiments/exp003_euclidean_resolvent_contraction/logs/final_verbose_production_build.log \
  --output experiments/exp003_euclidean_resolvent_contraction/assurance/final_signature_axiom_audit.json

PYTHONDONTWRITEBYTECODE=1 python3 experiments/exp003_euclidean_resolvent_contraction/assurance/run_logged.py \
  --log experiments/exp003_euclidean_resolvent_contraction/logs/final_forbidden_scan.log \
  --timing experiments/exp003_euclidean_resolvent_contraction/metadata/final_forbidden_scan_command.json \
  --cwd /home/richman954/NDEA_Evolve_offruntime/exp003/worktree/NDEA_Evolve -- \
  python3 experiments/exp003_euclidean_resolvent_contraction/assurance/run_forbidden_scan.py \
  --repo /home/richman954/NDEA_Evolve_offruntime/exp003/worktree/NDEA_Evolve \
  --output experiments/exp003_euclidean_resolvent_contraction/assurance/final_forbidden_scan.json
```

Wrapper argv, outer timeouts, cache status, logs, and actual results are recorded
beside the corresponding evidence. A wrapper pass does not override a child timeout
or unexpected Lean exit.

The qualifying target compiles the complete Step-1 theorem, edge-case, and positive
counterexample-witness module. The unchanged project root is not rebuilt; this avoids
a separate large-environment load and is not represented as root-target coverage.

## Verbose production-target attempt 003 and final probe

Attempt 003 ran from `2026-09-06T13:44:00.518181Z` through
`2026-09-06T14:36:45.191920Z`, exited 1 after 3,164.674 seconds, and produced a
complete 582,869-byte log with SHA-256
`f045f33b5804bad38608bfa70668d49de5abee885248cc9abbf5b76d5d414767`.
It used the pinned Lake, canonical cwd, compatible cache, and source SHA-256
`0618edd22fa0e36f9c3b28baa0bf97a22a068abafb6ae18810ac40b8f5f78ad6`.
Every headline declaration elaborated and printed; the final positive witness failed
because `Complex.I ^ 2` was not syntactically present. This is a proof-script error,
not a theorem counterexample.

`ImaginaryProductProbe.lean` then ran from `2026-09-06T14:37:23.397801Z` through
`2026-09-06T14:37:43.993173Z`, exited 0 after 20.595 seconds, and checked the exact
remaining scalar expression. Its SHA-256 is
`201c31714feb41b9ad787bf9df41311c74e7bc0cb499a0e61b533705eb0d7508`.
The corresponding production repair is SHA-256
`19d6ffadd0e134f0becb39d6838335455409730b4683e7a408e03f9825861bd2`
and was untested in the complete module at the preserved partial checkpoint.

## Integration and closure continuation

The renewed window began at `2026-09-06T15:29:53Z`
(`2026-09-06T11:29:53-04:00`), with monotonic start `108435.76` seconds and
deadline `2026-09-06T18:29:53Z` (`119235.76` monotonic seconds).

Attempt 004 ran the exact required named target:

```text
/usr/bin/timeout --signal=TERM --kill-after=10s 3600s \
  /home/richman954/.elan/bin/lake -v build \
  NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction
```

It ran from `2026-09-06T15:31:03.209801Z` through
`2026-09-06T16:24:34.611225Z`, exited 0 after `3211.401704511998` seconds,
and emitted the complete 582,939-byte verbose log
`logs/final_verbose_production_build_attempt004.log` with SHA-256
`3d5f230bcc42d7fba67049e255cfe4655e4397c1db5c0f074c331e667d2aa2bc`.
The source and dependency identity records before and after are byte-identical.

The batched control runner launched one pinned Lean process from
`2026-09-06T16:25:16.711983Z` through `2026-09-06T17:17:13.983731Z`.
The child exited naturally with code 1 after `3117.263893973999` seconds and
emitted exactly two intended type mismatches. The strict runner classified 2/2
unique cases PASS and exited 0; its outer logged-command duration was
`3117.4758307310112` seconds. `controls/lean/rejection_diagnostics/results.json`
and `execution_receipt.json` are the semantic records.

The first parser run over attempt 004 exited 1 because Lean's verbose
informational output included source-location prefixes. The parser was narrowed
to recognize and remove only the exact Exp003 production-source prefix while
requiring exactly one prefixed marker pair. The repaired invocation passed and
bound the three exact signatures and their transitive axiom sets to the build
log. The first tooling self-check after that repair passed 12/13 and identified
one stale expected diagnostic; after updating that test expectation, self-check
011 passed 13/13. These are Python-only assurance repairs, not Lean proof edits.

The final source scan, predecessor post-check, and pre/post identity comparison
all passed. Machine-readable timing records alongside each named log remain
authoritative for argv, cwd, timestamps, exit code, and SHA-256.
