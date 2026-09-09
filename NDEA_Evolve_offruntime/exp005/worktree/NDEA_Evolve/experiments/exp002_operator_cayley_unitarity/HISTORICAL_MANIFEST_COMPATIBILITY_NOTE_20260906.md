# Historical Julia-green manifest compatibility note

During finalization on 2026-09-06, the strict historical-manifest precheck found
that `JULIA_GREEN_SHA256SUMS` verified 67 of 68 entries. The sole mismatch was
`STATE.md`: later legitimate progress updates had changed a path that the
immutable Julia-green manifest binds to its earlier checkpoint bytes.

The later preclosure contents were first preserved byte-for-byte as
`STATE_PRECLOSURE_PRESERVED_20260906.md` (SHA-256
`4e12cbc60c071af8d2c3837989faaf8a23d60b60a59094a9b76368dd9ef1d46d`).
`STATE.md` was then restored to its exact Julia-green content from commit
`0e913e9cadd5c25ff9c982c5be373cbe38618c50`, whose SHA-256 is
`0787189e8da83a406a315bfc16471f009ded47d942fb39527d41352150ea5509`.

No historical manifest, theorem, proof, certificate, policy, or control was
changed. Current status belongs in additive state and closure-report files so
that historical checkpoint paths remain reproducible.

The exact failed and passing checksum logs and timing records are preserved
inside the final selected tree under `evidence/finalization_20260906/`, together
with a source-hash inventory.
