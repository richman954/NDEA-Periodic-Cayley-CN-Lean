# Final staging and evidence preservation

Release qualification requires both the combined-source check and a fresh
full modular build. The combined check precedes the modular build in this
campaign; it does not replace it. The final modular run starts from an empty
active project cache, with the former development artifacts moved to a
recoverable off-path directory recorded in its reset manifest.

The candidate staged integrity audit passed and is retained as
`evidence/CANDIDATE_ASSURANCE_AUDIT_20260908.json`. The final audit is
`evidence/FINAL_ASSURANCE_AUDIT.json`, with
its selected-source/evidence manifest at
`evidence/SELECTED_EVIDENCE_SHA256SUMS`. The final evaluation report identifies
the concrete qualifying compiler runs and the proof verdict.

Raw logs are preserved verbatim, including the two unsuccessful development
conversion attempts and all linter/deprecation warnings. The logs directory's
local `.gitattributes` exempts only `.log` files from whitespace diagnostics;
proof source, scripts, controls, and documentation remain checked.

After every intended deliverable is staged, freeze the full
`evidence/FINAL_SHA256SUMS`, covering all indexed files except itself. No prior
manifest or historical status snapshot is rewritten. Nothing in the delivered
source/evidence tree is edited after this freeze.

The final commit and annotated tag are then packaged into a new off-tree
source archive and Git bundle. The delivery helper verifies the bundle,
extracts the archive and clones the bundle into fresh temporary directories,
checks the complete manifest in both recovered copies, and confirms the
preserved Experiment 004 tag. The recovery directories are retained.

The off-tree `DELIVERY_RECEIPT.json` is the authority for the actual final
commit/tag identity, archive/bundle hashes, and completed recovery results.
Those values cannot be inserted into a source file covered by its own final
commit and archive hashes without circularity. Consult the receipt rather
than interpreting this pre-packaging note as a completed recovery claim.

Recovery establishes local source identity and integrity, separate from the
recorded Lean checks. It is not an independent human review, remote
reproduction, or publication. The result remains the conditional mesh-weighted
residual bridge described in PLAN.md, not a full smooth-PDE consistency proof.
