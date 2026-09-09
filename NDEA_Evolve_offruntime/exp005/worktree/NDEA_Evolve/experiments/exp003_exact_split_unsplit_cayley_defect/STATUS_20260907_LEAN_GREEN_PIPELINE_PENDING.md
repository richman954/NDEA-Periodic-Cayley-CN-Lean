# Experiment 003 Step 3 — Lean-green, pipeline-pending snapshot

Timestamp: 2026-09-07 (America/New_York)

The Step-3 production module now contains the arbitrary-matrix exact
split-versus-unsplit identity and the induced continuous-linear-map
operator-norm bound. A bounded combined RAM-backed Lean run passed with exit
code 0 on attempt 3. The first two rejected logs are retained and attributable
to control-only arithmetic normalization repairs.

The compiled controls establish:

- commuting Hermitian generators can have nonzero local defect;
- for `|alpha| <= 1`, the verified quadratic bound implies the proposed
  `|alpha|` bound, proving that the requested small-step counterexample cannot
  exist;
- the globally quantified `|alpha|` replacement is false at the corrected
  large-step witness `alpha = 10`, `A = B = (1/10) I`.

This snapshot remains **UNVERIFIED** overall. The Julia certificate, independent
Python validation, qualifying modular Lean run, assurance manifest, and release
commit/tag are still pending. No Step 4 or Step 5 work has begun.
