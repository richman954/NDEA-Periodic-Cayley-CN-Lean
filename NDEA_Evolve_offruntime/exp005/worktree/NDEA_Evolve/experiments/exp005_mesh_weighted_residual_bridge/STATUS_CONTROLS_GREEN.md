# Control milestone

All 11 controls compiled in run `20260908T015115.937664Z_2`, exit 0 in
120.73154 seconds, with unchanged source and only the allowed standard axioms.
Together with production, 40 new public theorem audits have now succeeded.

Control source SHA-256:
`4b302428c2815a9a1668e2caed13051106981b84cad2597928d601429326e5d6`.

Two earlier control invocations failed solely at the final scalar matrix-to-
operator conversion. Selecting `EquivLike.injective` explicitly resolved the
inherited-equivalence mismatch. Both failed logs and receipts are preserved;
neither qualifies the release. The successful source contains no prohibited
proof placeholders, and the accepted axiom rows contain no error-placeholder
dependency. The log retains harmless deprecated identity-application warnings.

Controls reject stability-implies-consistency, omitted time-step scaling,
an omitted middle residual, positive definiteness at zero weight, and equality
of two half Cayley steps with one full step. Empty dimension/count and zero/
negative-step endpoint checks are included.

Combined-source and fresh full-chain verification, final audit, manifest,
and recovery-checked delivery remain outstanding at this historical snapshot.
