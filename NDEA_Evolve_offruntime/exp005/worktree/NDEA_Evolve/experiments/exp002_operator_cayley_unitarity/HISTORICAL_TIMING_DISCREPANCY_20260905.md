# Historical authorization-timing discrepancy

This additive note preserves the earlier records without alteration.

- Recorded earlier authorization deadline:
  `2026-09-05T17:57:21-04:00`.
- Recorded strengthened-witness completion:
  `2026-09-05T19:43:39-04:00`.
- Recorded elapsed duration: `2778.246` seconds.
- Subtracting that duration from the completion timestamp gives an inferred
  command start near `2026-09-05T18:57:21-04:00`, about 3,600 seconds after the
  recorded authorization deadline.

Inspection found the same contradiction in the preserved attempt records and no
recorded timezone conversion, renewed authorization, or other evidence that
resolves it. The discrepancy therefore remains **UNRESOLVED**. No historical
timestamp, duration, deadline, or budget was rewritten. Work in this continuation
uses only the separate renewed four-hour window recorded in
`metadata/renewed_authorization_window_20260905.json`.
