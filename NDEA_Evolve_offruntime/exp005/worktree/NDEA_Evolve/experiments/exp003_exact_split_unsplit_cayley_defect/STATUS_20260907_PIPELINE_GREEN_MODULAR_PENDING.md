# Experiment 003 Step 3 — Pipeline-green, modular-pending snapshot

Timestamp: 2026-09-07T14:18:23-04:00

The exact Julia 1.12.6 discovery run passed and generated the canonical JSON
certificate and run receipt. It verified five Gaussian-rational cases, every
matrix residual, the free noncommutative expansion, the commuting nonzero
defect, and the corrected global linear-scaling counterexample. The Julia
archive matched the official published SHA-256 before execution.

The independent Python 3.11 validator reconstructed the certificate using
`fractions.Fraction`, repeated 407 strict checks, verified source/certificate/
receipt hashes, and exited 0. The combined Lean run also exited 0.

This is still a historical **UNVERIFIED** pre-release snapshot. The qualifying
module-by-module Lean run, final proof-policy and predecessor audits, checksum
manifest, release commit/tag, and external archive remain pending. Steps 4–5
have not begun.
