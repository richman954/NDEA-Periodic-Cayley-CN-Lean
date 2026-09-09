# Final staging and evidence preservation

Both compiler verification routes and the integrity audit passed before
release staging. The staging whitespace check then identified spaces emitted
by Lean in verbatim diagnostic output. The source proofs were unaffected.

`evidence/logs/.gitattributes` now exempts only raw `.log` files in that
directory from Git whitespace diagnostics. Logs were not edited; source and
documentation whitespace checks remain active. The staged whitespace check
and the post-staging integrity audit both passed.

The initial 711-file checksum snapshot was preserved byte for byte as
`evidence/CANDIDATE_SHA256SUMS_BEFORE_RAW_LOG_ATTRIBUTES`. Its SHA-256 is
`83caa06903a01c652ef00c6244cddba822ea5314111d0a58a762bd927114d7f6`.
Every file covered by that snapshot still passes its checksum. Later additions
are covered by the final full-tree manifest; no earlier manifested file was
rewritten to make room for the staging update.

The post-staging checks are recorded in
`evidence/FINAL_ASSURANCE_AUDIT_STAGED.json` and
`evidence/SELECTED_EVIDENCE_STAGED_SHA256SUMS`. The earlier audit remains valid
and retained. `evidence/FINAL_SHA256SUMS` is the final complete delivered-tree
manifest, excluding itself.

After the final commit and annotated tag, the delivery helper creates an
off-tree source archive and Git bundle containing all repository refs. Its
external receipt records fresh archive and bundle recovery, full checksum
verification in both recovered copies, and preservation of the Step 4 tag.
This receipt is external so its archive/bundle hashes do not form a circular
in-tree checksum dependency.
