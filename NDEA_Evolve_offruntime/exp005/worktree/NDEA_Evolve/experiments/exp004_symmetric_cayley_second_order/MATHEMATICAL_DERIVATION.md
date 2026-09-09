# Symmetric Cayley comparison — derivation

This document records the mathematical route. Verified status and qualifying
build receipts are reported separately, not inferred from this derivation.

## Convention and quadratic cancellation

Let X = i(h/4)Ahat and Y = i(h/2)Bhat, with multiplication the composition
ring of continuous endomorphisms. Write

`C(X) = (1-X)(1+X)⁻¹`, `P(X) = 1-2X+2X²`.

Experiment 003 Step 5 gives the exact identity

`C(X)-P(X) = -2X³(1+X)⁻¹`

and, for a Hermitian generator, the unconditional resolvent bound gives
`‖C(X)-P(X)‖ ≤ 2‖X‖³`.

The terms of degrees zero, one, and two in `P(X)P(Y)P(X)` are

`1 - 4X - 2Y + 8X² + 4XY + 4YX + 2Y² = P(2X+Y)`.

The ordered XY and YX terms are both retained: this is a noncommutative
identity. The remaining terms have degree at least three. In contrast,
nonsymmetric `P(X)P(Y)` has a quadratic mixed term `4XY`, not
`2XY+2YX`. This is the cancellation that permits the improved upper rate.

Since `2X+Y = i(h/2)(Ahat+Bhat)`, the exact step is
`exp(-2(2X+Y)) = exp((-i*h) • operatorOf (A+B))`.

## Bounding the local remainders

Let `r=|h|(‖Ahat‖+‖Bhat‖)`. The frozen small-step condition gives
`0≤r≤1/2`. Both ‖X‖ and ‖Y‖ are bounded by r, so ‖P(X)‖ and ‖P(Y)‖
are at most 5, using ‖1‖≤1. This inequality remains valid in dimension zero.

Replace the three Cayley factors by their quadratics, one at a time. Unitary
norm transport for the unmodified Cayley factors, and the polynomial bounds
for the replaced factors, give a total bound at most

`2r³ + 10r³ + 50r³ = 62r³`.

The degree-at-least-three polynomial terms have total absolute coefficient
sum 100. Submultiplicativity and r≤1 bound the polynomial tail by `100r³`.
The implementation may group these terms to avoid a large expanded proof.

Finally put W=2X+Y. The implementation compares P(W) back to the unsplit
Cayley step, with bound `2r³`, and then invokes Step 5's already verified
Cayley-to-exponential comparison, bounded by `18r³`. Its small-step
hypothesis holds because `4|h/2|‖operatorOf (A+B)‖≤2r≤1`.
The four comparisons total `182r³`, implying the frozen conservative local
bound `1000r³`. A more direct exponential-remainder argument could reduce
this coarse constant; no best-constant claim is made or needed.

## Finite powers, physical time, and convergence

Every Cayley factor is unitary, and so is their symmetric product S_h.
The exact exponential is unitary as well. The verified telescoping identity
and unitary norm transport therefore give, for every natural N,

`‖S_h^N - exp(-ih(Ahat+Bhat))^N‖ ≤ N ‖S_h-exp(-ih(Ahat+Bhat))‖`.

This includes N=0. For positive N take h=t/N and use the exact exponential
power identity. The step condition becomes `2|t|(‖Ahat‖+‖Bhat‖)≤N`, and

`N * 1000 |t/N|³ (‖Ahat‖+‖Bhat‖)³`
`= 1000 |t|³ (‖Ahat‖+‖Bhat‖)³ / N²`.

For fixed t,A,B the threshold holds eventually and the right side tends to
zero. Squeezing the operator-norm error proves convergence. No limit of
generators or spatial discretizations is involved.
