# Finalization evidence copied off the command boundary

The six manifest-check and production-role log/timing files are byte-identical
copies of immutable command records first written under the off-runtime
continuation directory `continuations/20260906T015529-0400/`.
`read_only_prepackage_results.json` is the verifier-native snapshot generated at
that check boundary, when the selected tree contained 220 regular files; later
additive evidence/status files explain the current larger count.
`SOURCE_SHA256SUMS` binds all seven records. The final package-wide
`FINAL_SHA256SUMS` separately covers this entire directory.

The authorization record is preserved at
`metadata/finalization_authorization_window_20260906.json`, SHA-256
`9613733929f391b0dbd21ebf1eb4c4f384386f7e3ed49738f18d2b21f1e3ee63`.

`read_only_prepackage_results.json` records verifier-native checks performed
without running Lean or Julia: historical manifests 4/4, evidence-role checks
72/72, production-role checks 13/13, and negative-control recomputation 33/33,
with no failures.
