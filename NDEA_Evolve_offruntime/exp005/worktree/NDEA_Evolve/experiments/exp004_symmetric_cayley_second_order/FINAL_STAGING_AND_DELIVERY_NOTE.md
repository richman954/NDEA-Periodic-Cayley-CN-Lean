# Final staging and evidence preservation

Both final compiler routes passed before release staging. The first staged
integrity audit passed and is preserved as
`evidence/CANDIDATE_ASSURANCE_AUDIT_20260908.json`. The final staged audit is
`evidence/FINAL_ASSURANCE_AUDIT.json`; its selected-source/evidence manifest
is `evidence/SELECTED_EVIDENCE_SHA256SUMS`.

All raw logs are retained verbatim, including unsuccessful development
attempts, linter warnings, and informational tactic suggestions. The new
logs directory's `.gitattributes` exempts only `.log` files from Git whitespace
diagnostics. Source, controls, scripts, and documentation remain checked.

The full `evidence/FINAL_SHA256SUMS` is frozen only after all intended files
are staged. It covers every indexed deliverable except itself. No earlier
manifest is rewritten, and historical status snapshots remain unchanged.
No delivered source or evidence file is edited after this freeze.

After the final commit and annotated tag, the delivery helper creates a new
off-tree source archive and Git bundle. It verifies the bundle, extracts the
archive and clones the bundle into fresh temporary directories, checks the
full manifest in both recovered trees, and verifies preservation of the
Step 5 tag. Recovery directories are retained and named in the receipt.

The off-tree `DELIVERY_RECEIPT.json` is the authority for final commit/tag
identity, archive/bundle hashes, and completed recovery results. Keeping it
outside the committed tree avoids circular checksum dependencies. Recovery
checks verify source identity and integrity; they are separate from the two
recorded Lean verification routes and do not claim external reproduction or
independent human artifact review.
