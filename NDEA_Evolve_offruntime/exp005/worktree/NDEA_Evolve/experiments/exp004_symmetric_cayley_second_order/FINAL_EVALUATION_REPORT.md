# Experiment 004 — final evaluation

**Mathematical and source-assurance verdict: VERIFIED.** Both final compiler
routes and the integrity audit passed on 2026-09-08 UTC (2026-09-07 in
America/New_York). Final commit/tag identity and archive/bundle recovery are
recorded separately in the off-tree release `DELIVERY_RECEIPT.json`, written
after the source commit so artifact hashes cannot create a checksum cycle.

## Mathematical result

For arbitrary complex Hermitian matrices A and B of finite dimension n, write
`M = ‖operatorOf A‖ + ‖operatorOf B‖` and define the symmetric step

`S_h = Chat A (h/4) * Chat B (h/2) * Chat A (h/4)`.

The established Cayley convention is `(I-iαHhat)(I+iαHhat)⁻¹`, so the exact
physical-time step is `exp((-i*h) • operatorOf (A+B))`. Every norm is the
induced operator norm on `E n →L[ℂ] E n`.

The local theorem proves error at most `1000 |h|³ M³` under `2|h|M≤1`.
Exact ordered quadratic cancellation requires no commutativity assumption.
The implemented estimates total `62+100+2+18 = 182` times `(|h|M)³`, then
weaken to the frozen coefficient 1000.

Unconditional unitarity and the inherited telescoping theorem give linear
accumulation over every natural N, including N=0. For every real t and
positive N satisfying `2|t|M≤N`, the fixed-time theorem proves

`‖S_(t/N)^N - exp((-i*t) • operatorOf (A+B))‖ ≤ 1000 |t|³ M³/N²`.

The threshold holds eventually for fixed t,A,B, yielding operator-norm
convergence. The scope includes zero and negative time, zero generators,
and n=0; it does not assume that identity has norm one in dimension zero.

## Qualifying verification evidence

[Production status](STATUS_PRODUCTION_GREEN.md) records successful individual
Local and Global module invocations.
[Controls status](STATUS_CONTROLS_GREEN.md) records the successful complete
controls invocation. Source hashes remained unchanged during these checks.
The nine principal production declarations and twenty-one public control
declarations reported only `propext`, `Classical.choice`, and `Quot.sound`.
Failed development attempts remain in the evidence history.

Final qualifying records:

- Fresh full-chain modular run: `20260908T002534.597869Z_2`, all eleven
  serial invocations passed without skipping existing outputs.
- Combined-source controls run: `20260908T004439.799434Z_2`, Lean exit zero
  after 208.935575 seconds; the exact 2,135-line source is retained.
- Source, proof-policy, environment, and predecessor integrity: the candidate
  audit passed with no errors; `evidence/FINAL_ASSURANCE_AUDIT.json` is the
  final staged audit and `evidence/SELECTED_EVIDENCE_SHA256SUMS` selects its
  source and compiler evidence.
- The full delivered-tree manifest is `evidence/FINAL_SHA256SUMS`, excluding
  itself. The off-tree release receipt identifies the final commit and hashes
  and verifies archive/bundle recovery against that manifest.

Verification uses pinned Lean 4.31.0 and Mathlib, one worker and one active
Lean job, bounded commands, and the ordinary `/tmp/exp004_build` cache.
Eight predecessor modules precede the new sources; the first two use inherited
import-only shadows with unchanged proof bodies. The integrity audit confirmed
all 717 inherited tracked files unchanged, the original Step 5 worktree clean,
its commit and raw tag object preserved, and its release hashes matching the
baseline. The pinned Lean executable hash and clean Mathlib revision also
passed. No prohibited source shortcuts or unapproved compiled axioms were found.
Raw linter warnings and informational tactic suggestions remain in the logs.

The release tag is
`exp004-symmetric-cayley-second-order-verified-final-20260907`.
The source archive, Git bundle, and delivery receipt are located under
`NDEA_Evolve_offruntime/exp004/releases/20260907_verified_final`.
No remote publication was performed.

## Controls and limits of the conclusion

Controls instantiate edge cases, connect scalar and matrix witnesses to the
production operator representation, detect incorrect outer-step scaling, and
distinguish symmetric from nonsymmetric finite compositions. Hermitian Pauli
matrices exhibit the nonsymmetric quadratic commutator defect. The A=0, B=I,
t=π witness rejects exact finite-step exponential equality; it does not
contradict the small-step bound or convergence.

“Second order” denotes the proved upper rate. Neither sharp constants nor a
universally nonzero leading error coefficient are claimed. No PDE theorem,
unbounded-generator limit, spatial-mesh-uniform estimate, or higher-order
splitting result is included.

Local kernel verification and the in-session source review are distinct from
independent human review or external reproduction of the release artifacts;
neither independent review nor external reproduction is claimed here.
