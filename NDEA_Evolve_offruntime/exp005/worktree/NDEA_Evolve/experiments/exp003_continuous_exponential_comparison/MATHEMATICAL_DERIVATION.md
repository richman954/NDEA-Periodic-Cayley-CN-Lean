# From the Cayley step to continuous evolution

The following derivation explains the statements in `PLAN.md`. Compiler
acceptance is recorded separately in the final evaluation and evidence.

Let H be a finite-dimensional complex Hermitian matrix. All the following
operators act on the standard complex Euclidean space, and all norms are
induced operator norms. Write

`X = iα Hhat`, `R = (I+X)⁻¹`, and `C = (I-X)R`.

Step 1 supplies `‖R‖ ≤ 1`, for every real α and in every dimension.

## Local rational and exponential remainders

The exact noncommutative identity is

`C - (I-2X+2X²) = -2X³R`.

It follows just from `(I+X)R=I`: multiply the polynomial `I-2X+2X²`
by `(I+X)R-I` and expand. No interchange of unrelated factors is used.
Submultiplicativity and resolvent contraction therefore give

`‖C-(I-2X+2X²)‖ ≤ 2‖X‖³`.

For a complete normed complex algebra with `‖I‖≤1`, the exponential series
has terms `(1/m!) Z^m`, of norm at most `‖Z‖^m`. Subtracting the first
three terms and bounding the remaining geometric tail yields

`‖exp Z-(I+Z+Z²/2)‖ ≤ ‖Z‖³/(1-‖Z‖) ≤ 2‖Z‖³`

when `‖Z‖≤1/2`. With `Z=-2X`, the two quadratic polynomials coincide.
Thus, when `4|α|‖Hhat‖≤1`,

`‖C-exp(-2iα Hhat)‖ ≤ (2+16)‖X‖³ = 18|α|³‖Hhat‖³`.

The constants are explicit upper bounds from geometric domination; they
are not asserted to be sharp.

## Accumulating the error

Hermiticity makes `-2iα Hhat` skew-adjoint, so its exponential is unitary.
The Cayley operator is also unitary by Experiment 002. Step 4's fan theorem
then gives

`‖C^N-exp(-2iα Hhat)^N‖ ≤ 18N|α|³‖Hhat‖³`.

For H=A+B, adding Step 4's split-versus-unsplit estimate gives

`‖(C_A C_B)^N-exp(-2iα Hhat)^N‖`
`≤ 4Nα²‖Ahat‖‖Bhat‖ + 18N|α|³‖Hhat‖³`.

Unitarity enters through left/right norm preservation. This remains valid
in dimension zero, where the operator identity has norm zero rather than one.

## Physical time and convergence

Set `α=t/(2N)` with N>0. The factor of two and negative sign follow from
the linear term `-2iα Hhat` in the Cayley expansion. The exponential identity
`exp(N • Z)=exp(Z)^N` identifies the exact N-fold reference with
`exp(-it Hhat)`.

The local small-step restriction becomes `2|t|‖Hhat‖≤N`. The bound simplifies to

`‖(Chat A (t/(2N)) Chat B (t/(2N)))^N-exp(-it Hhat)‖`
`≤ (t²/N)‖Ahat‖‖Bhat‖ + (9/4)|t|³‖Hhat‖³/N²`.

For fixed t, A, and B, the step restriction is eventually satisfied. Both
terms tend to zero; squeezing the norm proves convergence in operator norm.
Negative times are included by absolute values in the cubic term and in the
threshold. N=0 is handled separately as a zero-power identity; a fixed-time
division formula at N=0 is not used to justify arbitrary-time evolution.

This is a finite-dimensional continuous-time result for fixed generators.
It makes no assertion about uniformity under spatial refinement, unbounded
operators, an infinite-dimensional PDE limit, or a second-order rate for
the nonsymmetric split product in general.
