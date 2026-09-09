# Experiment 002 partial status — 2026-09-05

Classification: DURABLE PARTIAL CHECKPOINT, NOT LEAN-GREEN, NOT FINAL

## Closed before this checkpoint

- Frozen mission and preflight receipt preserved.
- Julia exact derivation and numerical exploration: PASS.
- Strict independent certificate validator: 530 exact/schema checks.
- Validator regression: 3/3 valid accepted, 31/31 unique altered fixtures rejected.
- Julia-green commit: `0e913e9cadd5c25ff9c982c5be373cbe38618c50`.
- Julia-green local bundle, archive, and fresh replay: PASS.

## Lean progress proved so far

The production core in
`NDEAEvolve/Experiments/Exp002/OperatorCayley.lean` independently formalizes:

- denominator invertibility for finite complex Hermitian matrices and real steps;
- two-sided unitarity of each Cayley transform;
- standard Euclidean inner-product and norm preservation;
- chronological, variable-step products with changing generators, with no
  pairwise commutativity hypothesis;
- the exact noncommutative order-defect identity with multiplication order
  preserved;
- Cayley-factor commutation iff generator commutation for nonzero real steps,
  including the Hermitian corollary where inverse laws are derived.

Evidence status:

- Remote direct proof-development attempt 5: PASS, exit 0.
- Remote verbose Lake core build: PASS, exit 0, 8,558 jobs; the full log was
  recovered byte-exactly from local CLI history after runtime loss.
- Style-cleaned mathematical-equivalent core: local pinned direct Lean check
  PASS, exit 0.
- Production forbidden-token scan over the core and witness source: PASS.

## In flight / not yet closed at this checkpoint

- The strengthened positive witness module is locally staged. A bounded
  integrated verbose local Lake build rebuilt the core successfully, but was
  interrupted during silent witness compilation at the authorized time ceiling;
  no witness result was obtained and none is claimed.
- Seven isolated false Lean units and a strict rejection runner are staged but
  have not yet been executed against a compiled positive witness module.
- Headline declaration/axiom audit source is staged but its output has not yet
  been captured.
- The Lean-green, preclosure, and final manifests/packages do not yet exist.
- Independent external review is PENDING.

## Runtime state

The authorized standard CPU replacement returned 404/401 and lost its local
session name. A subsequent read-only listing showed the endpoint as an
unidentified `?` assignment. It was not stopped or reused. The one-replacement
ceiling is exhausted; no additional runtime was created.

See `recovery/second_runtime_loss/README.md` for exact recovery provenance.
