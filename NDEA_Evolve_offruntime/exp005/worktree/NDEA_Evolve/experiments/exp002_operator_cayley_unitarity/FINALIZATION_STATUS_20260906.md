# Experiment 002 in-tree finalization status

Status at the manifest boundary: **ALL FROZEN MATHEMATICAL AND ASSURANCE GATES
PASS; OUTER DELIVERY RECEIPT REQUIRED**.

The required verbose root build returned exit code 0 after
`2846.7023403430067` seconds and 8,562 jobs. It used the compatible existing
cache; it was not a clean-runtime rebuild. The complete log, timing record, and
production-role metadata bind the unchanged Operator and witness sources.

The strict historical Julia-green manifest precheck initially returned 67/68
because later legitimate progress text had changed `STATE.md`. The later text is
preserved byte-for-byte as `STATE_PRECLOSURE_PRESERVED_20260906.md`; `STATE.md`
was restored to its historical bytes and the postcheck passed 68/68. See
`HISTORICAL_MANIFEST_COMPATIBILITY_NOTE_20260906.md`.

This file is frozen before the final manifest and archive are created, so it
cannot truthfully contain their own hashes or claim their verification. Consult
the adjacent off-runtime final delivery receipt and timestamped closure report
for the authoritative final local-closure status. External human review remains
**PENDING**.
