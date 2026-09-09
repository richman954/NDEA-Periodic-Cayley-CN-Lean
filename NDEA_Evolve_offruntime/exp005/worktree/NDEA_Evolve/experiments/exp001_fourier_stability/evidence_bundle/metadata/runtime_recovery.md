NDEA-Evolve recovered runtime provenance
=======================================

This file is a recovery record, not a byte-for-byte replacement for the immutable
baseline evidence that existed on the original ephemeral Colab VM.

Original verified baseline endpoint: m-s-kkb-usc1a1-35dczkazprg9n
Original endpoint pruned UTC: 2026-09-05T10:44:44.202603+00:00
Recovery CPU endpoint: m-s-kkb-usc1b1-2rn1s57wbiaz9
Recovery endpoint created UTC: 2026-09-05T10:47:36.209697+00:00

Original immutable baseline identities:
- report SHA-256: f8077108504b13bf5ae160a239f5e9985b2780992d69c4ebe28ef25599b0351f
- manifest SHA-256: c020ce7ecb25a6ea87411805428058bf2d9458335f642ebea9edd7dd162e5a12
- report-hash-file SHA-256: b25cb7617e2015af1781d250ca17b4c0a388df0f4d6976ed9511ab3a01aa48a1
- verification-log SHA-256: ea86d66dd769ab52fb18addf8d1617ebac221be2d4caa0e3cc31098c4a69d28d
- Git commit: 01ac3a3837f221a378e71f4d8de4f02534238532
- Git tag: baseline-verified-lean4.31-mathlib-v4.31.0
- manifest verification: 21/21 PASS

The historical path /content/NDEA_Evolve/evidence was lost when Google pruned
the original VM. It is intentionally not recreated or overwritten. The exact
toolchain/project dependency graph was reconstructed from preserved scripts:
- Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783
- Lake 5.0.0-src+68218e8
- elan 4.2.4
- Julia 1.12.6 remained preinstalled and was not reinstalled
- Mathlib v4.31.0 at fabf563a7c95a166b8d7b6efca11c8b4dc9d911f

All new evidence is confined to experiments/exp001_fourier_stability.
Recovery record generated UTC: 2026-09-05T10:59:22.530931+00:00
