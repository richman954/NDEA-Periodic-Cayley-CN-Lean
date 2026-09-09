# Experiment 003 Step 3 — Pre-closure verified snapshot

Timestamp: 2026-09-07T14:36:01-04:00

The exact split-versus-unsplit Cayley identity and its induced operator-norm
bound have compiled successfully in two bounded, serial RAM-backed Lean runs.
The qualifying modular run compiled the actual immutable Step 2 production
module, the actual Step 3 production module, and the actual Step 3 controls as
separate modules, then emitted their exact signatures and clean axiom audits.

The Julia exact-arithmetic discovery run generated a canonical JSON certificate.
The independent Python validator reconstructed it and passed 407 checks. The
commutative-collapse witness compiled. The requested small-step counterexample
to a bound with `|alpha|` was proved impossible for `|alpha| <= 1`; a corrected
large-step counterexample compiled at `alpha = 10` and
`A = B = (1/10) I`.

The required Step 2 commit and annotated tag remain intact, its separate
worktree is clean, and protected predecessor sources, evidence, release data,
and project manifests have zero diff. No forbidden proof mechanism is present.

This is a historical pre-closure snapshot. At this point all mathematical and
pipeline checks are verified, but the final checksum manifest, release
commit/tag, and external release bundle have not yet been created.

Only Experiment 003 Step 3 was executed. No telescoping or
continuous-exponential work was started.
