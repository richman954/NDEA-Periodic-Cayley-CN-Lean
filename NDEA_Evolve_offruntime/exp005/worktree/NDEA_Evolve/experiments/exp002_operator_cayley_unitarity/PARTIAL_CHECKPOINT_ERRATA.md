# Erratum for the 2026-09-05 overnight partial checkpoint

This erratum applies only to the immutable package tagged
`exp002-overnight-partial-handoff-20260905` at commit
`6bd9b958a90d3c607e399d279c718b3843e68ab4`.

The package's outer three-artifact delivery check passed. However, a later
nested-manifest audit found that the archived copy of
`failure_and_repair_log.md` did not match its immutable Julia-green manifest:

- hash required by `JULIA_GREEN_SHA256SUMS`:
  `e3e5ae1ae584cfb2b716a00de97dc84dad343fef9f794b62b23e7dbdd73e3324`;
- hash actually archived in that partial package:
  `3ed52a9a7904f321a674b674c919784734d234f3f2cf8421297266b08487fd92`.

Therefore that historical partial archive is not an internally green recovery
point, despite its valid outer hashes. It remains preserved unchanged as
failure evidence and must not be relabeled.

The live worktree restored the Julia-green version of that file byte-for-byte;
subsequent Lean notes were moved to `lean_failure_and_repair_log.md`. Fresh
checks on 2026-09-05 passed all 7 preflight entries and all 68 Julia-green
entries. The first later archive whose fresh-extraction verifier confirms both
nested manifests is the valid recovery successor.
