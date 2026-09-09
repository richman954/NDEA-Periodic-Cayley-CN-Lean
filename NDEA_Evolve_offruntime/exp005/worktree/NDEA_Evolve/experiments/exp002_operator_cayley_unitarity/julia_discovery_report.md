# Julia discovery report — Experiment 002

Status: JULIA-GREEN; universal theorem verification remains pending in Lean.

## Exact layer

Julia 1.12.6 uses a hand-written Gaussian-rational matrix layer. It constructs the
three Pauli generators, their Cayley denominators/numerators/inverses, exact unitary
factors, the chronological product `U3 * U2 * U1`, vector inner-product checks, and
the noncommutative order defect. It also checks six edge cases, eleven exact
adversarial witnesses, and all 81 real 2-by-2 matrices with entries in `{-1,0,1}`.

The frozen factorization

`[C_a(A),C_b(B)] = -4ab R_a R_b [A,B] R_b R_a`

passes exactly for the Pauli X/Z witness. Exact algebra during repair also revealed
that `R_b R_a [A,B] R_a R_b` is an equivalent universal factorization, not a bad
ordering. The negative control therefore swaps only the left inverse pair, which is
genuinely false for the witness.

The sparse star-polynomial record establishes the one-generator identities used for
unitarity. It is not a proof of the two-generator universal noncommutative theorem.

## Counterexample search

The exhaustive finite search found 2 singular Cayley denominators after Hermiticity
was dropped and 52 invertible non-Hermitian examples whose Cayley factors were not
unitary. Finite search is evidence about this bounded domain, not a universal proof.

## Numerical layer

The separately classified Float64 experiment uses seed 20260905, dimensions 2, 3,
and 4, and three same-sized factors per ordered product. It checks 4,608 individual
factors and 1,536 products. Residuals use the Euclidean induced operator 2-norm.
The acceptance limit `1e-10` is fixed in source and independently fixed in the
validator; it is not supplied by the certificate. Observed maxima were approximately
`6.65e-15` for factors and `7.16e-15` for products.

These floating-point observations are not proofs or long-time error bounds.

## Trust boundary

The JSON certificate is data, not an oracle. A separate Python validator rebuilds
Gaussian-rational operations, inverses, determinants, Cayley records, compositions,
vector norms, the defect identity, adversarial examples, and the exhaustive search.
It also binds source hashes and checks the numerical receipt against an independent
limit. Lean must still prove every universal headline claim without trusting Julia or
the validator.
