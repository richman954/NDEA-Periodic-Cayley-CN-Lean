# Lean and second-runtime failure-and-repair log

This additive log begins after the immutable Julia-green checkpoint. The
historical `failure_and_repair_log.md` remains byte-for-byte covered by
`JULIA_GREEN_SHA256SUMS`.

## Lean universal-core development

Remote direct attempts 1–4 returned exit code 1 while the proof was developed.
Their byte-exact diagnostics and source hashes are preserved under
`recovery/second_runtime_loss/recovered_attempt_logs/`. Repairs included using
the available finite-matrix positive-definiteness/injectivity bridge, replacing
brittle rewriting with explicit ordered cancellation lemmas, and preserving the
four two-sided inverse laws in the noncommutative identity.

Attempt 5 returned exit code 0. Its reconstructed source independently matches
the remote-recorded SHA-256. One unused simp argument was then removed, after
which the full verbose remote Lake target build returned exit code 0. That
complete log was recovered byte-exactly from CLI history after endpoint loss.

The first positive-witness run returned exit code 1 because the core `.olean`
did not yet exist in Lake's build directory. This is classified as build-order
failure, not rejection of a witness. The witness source was subsequently
strengthened to use the actual Cayley transform for both Pauli order sensitivity
and the dropped-Hermiticity counterexample.

## Second endpoint loss

After the successful verbose core build, the sole authorized replacement
returned 404/401 and the CLI removed the `ndea-evolve` name. A read-only server
listing later displayed the same endpoint only as `?`. It was neither stopped
nor adopted, and no second replacement was created. Work continued only against
the already-installed local pinned Lean/Mathlib environment. The style-cleaned
core passed that local direct check with exit code 0.

## Strengthened positive-witness attempt 003

The current controls were strengthened so the wrong-sign witness uses the
actual Pauli `cayley` factors and the inverse-order witness uses actual
`cayleyR` factors plus `commutator nilA nilB`. A full verbose build ran for
2,778.246 seconds and returned exit code 1. The exact diagnostic showed one
local proof-script problem: `rw [hSign]` rewrote both occurrences in an
auxiliary sum, leaving an unsolved equality. This does not refute the witness.

The full 569,225-byte log is preserved as
`logs/verbose_lake_build_witness_attempt_003.log`, SHA-256
`5c0066b47155b2a2911514853c09dbc0a158f74aea05e821618cabd3a5d10333`.
The executed source hash was
`60777d9585849ccf31735de46761813f46d9b23ad088c7b31a9a68020903d420`.

The proof was repaired by replacing the broad rewrite with `congrArg` under
only the right summand. The repaired source hash is
`ef71de8e6a7188aec8df817550fe848048358268cb1a2e63f4ba4be4b002dd17`.
It is deliberately labeled **NOT RUN / NOT GREEN** because the eight-hour
overnight ceiling had already expired; no second long build was started.

## Renewed-window strengthened-witness closure

Under the new four-hour authorization beginning 2026-09-05T22:00:08-04:00,
the repair was first reduced to a small algebraic probe. Early probes exposed
only harness/import issues, a bounded timeout, and the need to state the generic
torsion-free-module premise. The final isolated algebraic probe returned exit 0.
All sources, diagnostics, command receipts, and explicit no-result classifications
are preserved under `assurance/probes/`, `evidence/`, `logs/`, and `metadata/`.

The unchanged repaired production source (SHA-256 `ef71de8e...dd17`) was then
built in full verbose mode. It completed 8,559 jobs successfully, returned exit
code 0 after 3,132.158 seconds, and produced the 568,743-byte log
`logs/final_positive_witness.log` with SHA-256
`71f8725f733879403b58e0635f68736196fd083538358e40e271acc7c35eb0ad`.
This closes the repaired positive-witness gate. It does not by itself close the
seven rejection controls or the final audit/build/delivery gates.

## Negative-control execution repair

The original seven-process runner was started with a 900-second per-case bound.
Its first case reached that bound without emitting any Lean diagnostic and was
terminated; the runner was then interrupted once the second case began, rather
than spend up to another 90 minutes on repeated cold imports. The empty shape
probe, the first case's timeout receipt, and the interrupted outer-run evidence
are preserved. Neither timeout is classified as a mathematical rejection.

The same seven frozen false theorem targets and their compiling positive witnesses
were therefore reconstructed into one additive assurance input which shares a
single imported environment. The replacement gate still requires seven distinct,
ordered, attributable Lean type-mismatch diagnostics and an actual process exit
code of 1; it records seven unique cases separately from one total process
invocation. Static reconstruction and adversarial parser self-checks passed.

An unlogged CLI-discovery invocation was accidentally issued while this runner was
still being finalized (the script has no `--help` mode). Its output, if any, is an
attempt only because the runner source changed during execution. It cannot satisfy
the final gate. Its one Lean child timed out after 900.191 seconds, returned `-15`,
and emitted no diagnostic; the runner recorded 0/7 attributable results and returned
1. The complete directory and an explicit ineligibility record are preserved at
`controls/lean/rejection_diagnostics_attempt_002_unlogged_changing_source_timeout/`
before the immutable-source run.

## Axiom-audit parser repair

The bounded Lean audit itself returned exit 0 after 3,482.951 seconds and printed
all 17 frozen signatures and axiom reports. The first strict parser invocation
returned 1 because Lean line-wrapped the six longer witness axiom lists; it did not
challenge any theorem or reveal a new axiom. That exact failure is preserved.

The parser was repaired to accept only a bounded identifier/comma/whitespace payload
between the report brackets, validate every axiom identifier, reject duplicates, and
retain the exact declaration-set check. Reparse returned 0: all 17 declarations were
present, the union was exactly `propext`, `Classical.choice`, and `Quot.sound`, and
both unexpected-axiom and forbidden-dependency sets were empty.

The independent delivery verifier initially had the same single-line parsing
assumption. Before packaging, it was repaired separately to reconstruct bounded
multiline axiom blocks from the hash-bound Lean log, validate each identifier, and
retain exact sequence/duplicate checks. An isolated parse of the actual log returned
17 declarations with the exact allowed union, and the complete 18-case packager
self-test passed again against the repaired verifier.

## Eligible negative-control closure

The final stable-source batched runner used one Lean process for the seven frozen
false declarations. Lean returned natural exit code 1 after 2,972.770 seconds,
inside the 3,000-second bound; the strict runner returned 0. It found exactly seven
ordered error headers and independently attributed every case to its own compiling
positive witness and an actual/expected type mismatch. All global and per-case
infrastructure, malformed-source, mixed-witness, and extra-diagnostic guards passed.
The delivery verifier independently reclassified the preserved bytes successfully.
