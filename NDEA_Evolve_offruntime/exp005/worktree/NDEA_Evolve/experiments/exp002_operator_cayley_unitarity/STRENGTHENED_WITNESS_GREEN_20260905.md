# Strengthened-witness green checkpoint — 2026-09-05

Status: **POSITIVE WITNESS GREEN; FINAL LEAN ASSURANCE STILL PENDING**

This additive checkpoint closes the one pending repaired-source build from the
earlier time-ceiling handoff. It is not yet the experiment's Lean-green or final
checkpoint because rejection controls, the final signature/axiom audit, the final
forbidden-token scan, and the verbose root build remain to be executed.

## Concrete result

- Production witness source:
  `NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean`
- Source SHA-256:
  `ef71de8e6a7188aec8df817550fe848048358268cb1a2e63f4ba4be4b002dd17`
- Exact bounded command:
  `/usr/bin/timeout --signal=INT --kill-after=10s 3600s /home/richman954/.elan/bin/lake -v build NDEAEvolve.Experiments.Exp002.AdversarialWitnesses`
- Working directory:
  `/home/richman954/NDEA_Evolve_offruntime/exp002/worktree/NDEA_Evolve`
- Start UTC: `2026-09-06T02:22:14.881763+00:00`
- Finish UTC: `2026-09-06T03:14:27.039977+00:00`
- Wrapper elapsed: `3132.1584052649996` seconds
- Lake target report: `Built ...AdversarialWitnesses (3117s)`
- Jobs: `8559`
- Actual exit code: `0`
- Result: `Build completed successfully (8559 jobs).`
- Full verbose log:
  `logs/final_positive_witness.log`
- Log size: `568743` bytes
- Log SHA-256:
  `71f8725f733879403b58e0635f68736196fd083538358e40e271acc7c35eb0ad`
- Machine timing record:
  `metadata/final_positive_witness_command.json`
- Hash-bound role metadata:
  `metadata/final_positive_witness.json`

No `error:`, `warning:`, `SIGINT`, or `interrupted` line was present in the
preserved verbose log. The repaired `congrArg` proof therefore advances from
historical **NOT RUN** to an actual kernel-checked **PASS** without changing the
production theorem statement or the checkpoint source hash.

## Isolated repair evidence

The renewed-window probe sequence is preserved under `assurance/probes/`,
`evidence/logs/`, and `evidence/metadata/`. The smallest successful algebraic
probe makes `Module.IsTorsionFree ℂ V` explicit and exits 0. Import/path failures
and bounded timeouts are classified as infrastructure/no-result outcomes, not as
mathematical rejection or proof.

## Assurance hardening before final controls

The negative-control runner and final fresh-delivery verifier were hardened before
generating final control evidence. They require an anchored, case-insensitive Lean
`Type mismatch` at the intended fixture line, exact natural exit code 1, no timeout,
no import/syntax/infrastructure failure, strict booleans, hash-bound diagnostics,
and independent verifier reclassification. Timeout capture uses bounded Linux
process termination with temporary-file-backed output, avoiding unbounded pipe EOF
waits. The axiom parser/verifier accepts Lean's explicit `@name :` signature spelling
while preserving the frozen 17-declaration sequence and independently checking the
hash-bound Lean log.

Python compilation and the packaging helper's eight isolated self-tests passed
under captured exit-0 commands. No final rejection, axiom, forbidden-token, root
build, manifest, or delivery claim is made by this checkpoint.
