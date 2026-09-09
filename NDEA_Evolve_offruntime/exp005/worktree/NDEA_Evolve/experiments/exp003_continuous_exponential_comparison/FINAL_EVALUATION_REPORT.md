# Experiment 003 Step 5 — final evaluation

## Verdict

Verified on 2026-09-07. The split Cayley evolution converges in induced
operator norm to the continuous exponential at every fixed real time,
for arbitrary finite-dimensional complex Hermitian matrices A and B.
Dimension zero, zero time, and negative time are included.

Let `Hhat = operatorOf (A+B)` and `α_N = t/(2N)`. For N>0 satisfying
`2|t|‖Hhat‖ ≤ N`, Lean proves

`‖(Chat A α_N * Chat B α_N)^N - exp((-i*t) • Hhat)‖`
`≤ (t²/N)‖Ahat‖‖Bhat‖ + (9/4)|t|³‖Hhat‖³/N²`.

Every displayed norm is the induced norm on
`EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`.
The explicit small-step condition is eventually satisfied for fixed t, A,
and B, so the convergence theorem itself needs no step restriction.
The constants are sufficient bounds, without an optimality claim.

## What was proved

- A cubic exponential remainder from geometric domination of its convergent
  power series, with an explicit norm-of-identity bound that permits dimension zero.
- The exact quadratic Cayley remainder and a local error bound
  `18|α|³‖Hhat‖³` when `4|α|‖Hhat‖≤1`.
- Exponential unitarity and the exact accumulated time identity, with the
  negative sign and factor of two dictated by the existing Cayley convention.
- The unsplit finite-N error and, using Step 4, the split fixed-time bound above.
- Convergence of the operators and convergence of the numerical error norm to zero.

The principal declarations are `split_cayley_fixed_time_error_le`,
`split_cayley_fixed_time_tendsto_exp`, and
`split_cayley_fixed_time_error_tendsto_zero`.
The source-to-theorem mapping and derivation are provided separately.

## Verification and assurance

- Fresh modular run `20260907T224538.229598Z_2`: all nine serial Lean
  invocations exited zero, covering the preserved predecessor chain,
  all three Step 5 production modules, and the actual controls source.
- Independent combined run `20260907T225346.750467Z_2`: the full concatenated
  source and controls exited zero. The exact generated source is retained.
- Both routes used the pinned local Lean/Mathlib environment, narrow imports,
  one Lean worker, and bounded timeouts. No root-project Lake build is claimed.
- The final integrity audit passed with no errors. Eighteen principal/control
  declarations were checked against compiled axiom reports; there are no
  dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.
- The source-policy scan found no prohibited proof shortcuts.
- All 634 tracked predecessor files remain unchanged. The original Step 4
  worktree, tag, and release archive hashes passed preservation checks.
- Both predecessor shadow sources match their originals after removing only
  import lines. The temporary artifact cache and narrow-import provenance
  are disclosed in the evidence.

Failed development attempts and their diagnostics remain separately recorded.
Only the successful final runs with matching current source hashes qualify
this release. Informational tactic suggestions and linter warnings are retained.

## Controls

Compiled controls cover zero time, zero generators, zero dimension, zero powers,
and negative time. Exact scalar controls, linked to the actual one-by-one
Cayley matrix entry, detect reversal of the sign, omission of half-step scaling,
and a false finite-refinement equality. At physical time π, a compiled scalar
witness also distinguishes the finite Cayley approximation from the exact
exponential. It does not purport to violate the small-step error estimate.

## Scope and delivery

This closes the planned continuous-exponential Step 5. It establishes a
finite-dimensional result for fixed generators and physical time. It does not
establish an unbounded-operator or PDE limit, uniformity under spatial mesh
refinement, or a generally second-order rate for nonsymmetric splitting.

The release tag is
`exp003-step5-continuous-exponential-comparison-verified-final-20260907`.
The mathematical evidence is selected by `evidence/FINAL_ASSURANCE_AUDIT.json`
and `evidence/SELECTED_EVIDENCE_SHA256SUMS`. The full delivered tree is covered
by `evidence/FINAL_SHA256SUMS`, excluding that manifest itself.
The final commit, archive and bundle hashes, and fresh-recovery checks are
recorded in the adjacent off-tree release `DELIVERY_RECEIPT.json`.
