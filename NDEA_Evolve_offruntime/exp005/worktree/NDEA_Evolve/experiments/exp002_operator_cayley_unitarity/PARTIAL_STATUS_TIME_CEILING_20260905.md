# Experiment 002 partial status at overnight time ceiling

Recorded: 2026-09-05T19:45:00-04:00 (America/New_York)

Status: **PARTIAL — DO NOT LABEL LEAN-GREEN OR FINAL**.

The authorized continuation began at 2026-09-05T09:57:21-04:00 and its
eight-hour ceiling was 2026-09-05T17:57:21-04:00. The already-running verbose
witness build was allowed to finish. No further long operation was started.

## Preserved green layers

- Exp001 assurance-hardening v2: locally closed; external review PENDING.
- Exp002 preflight manifest: 7/7 PASS at this handoff.
- Exp002 Julia-green manifest: 68/68 PASS at this handoff.
- Julia exact/certificate layer: unchanged and green.
- Universal Lean core: unchanged and previously kernel-checked under Lean
  4.31.0 / Mathlib revision
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Pre-strengthening positive-witness build: PASS at commit
  `3cf2ddc06449b8771b137f2cff2979b7a877e670`.

## Current strengthened control branch

The two assurance controls now target actual definitions:

1. the sign control uses
   `commutator (cayley 1 pauliX) (cayley 1 pauliZ)`;
2. the inverse-order control uses actual `cayleyR` factors and
   `commutator nilA nilB`, with exact link lemmas for the displayed matrices.

Verbose attempt 003 ran 2,778.246 seconds and returned exit code 1. Its only
reported error was an overly broad `rw [hSign]` inside the newly added
wrong-sign helper. Full log SHA-256:

`5c0066b47155b2a2911514853c09dbc0a158f74aea05e821618cabd3a5d10333`

That local proof step was replaced with a targeted `congrArg`. Repaired source
SHA-256:

`ef71de8e6a7188aec8df817550fe848048358268cb1a2e63f4ba4be4b002dd17`

The repaired source has not been compiled. Its status is **NOT RUN**, not PASS.

## Deferred final assurance

- current-source positive-witness build: NOT RUN after repair;
- seven Lean negative controls: PENDING;
- 17-declaration signature/axiom audit: PENDING;
- strict final forbidden-token artifact: PENDING (a direct source check found
  no matches, but the final bound scanner has not run);
- final verbose root build: PENDING;
- final manifest/package/fresh-extraction verifier: PENDING.

The delivery verifier source has been hardened and preserved at
`assurance/verify_exp002_final_delivery.py`, but no final package exists yet.

## Runtime and exact restart

Read-only Colab inspection at handoff reports no active server sessions and no
active local session. No replacement may be created automatically because the
single authorized replacement allowance was already used.

Smallest next command:

```text
cd /home/richman954/NDEA_Evolve_offruntime/exp002/worktree/NDEA_Evolve
/home/richman954/.elan/bin/lake -v build NDEAEvolve.Experiments.Exp002.AdversarialWitnesses
```

Preserve its full output under a new, non-overwriting attempt name. If and only
if it passes, proceed to the seven controls, axiom audit, forbidden scan, and
final verbose root build. Do not launch inverse-integrator, QGI, or a new
experiment.
