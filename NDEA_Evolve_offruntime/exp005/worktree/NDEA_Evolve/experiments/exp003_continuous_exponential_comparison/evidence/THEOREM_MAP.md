# Step 5 theorem map

This map describes the source contract. Verification status is recorded
separately in the final evaluation and qualifying command receipts.

| Result | Declaration | Hypotheses |
| --- | --- | --- |
| Cubic exponential Taylor remainder | `exp_quadratic_remainder_opNorm_le` | Complete normed complex algebra, norm of identity at most one, `‖Z‖ ≤ 1/2` |
| Exact quadratic Cayley remainder | `cayley_quadratic_remainder` | Hermitian generator, every real step |
| Cubic local Cayley/exponential error | `cayley_exp_local_opNorm_le` | Hermitian generator, `4|α|‖Hhat‖ ≤ 1` |
| Unsplit finite-N error | `cayley_exp_global_opNorm_le` | Same local step restriction, every natural N |
| Split finite-N error | `split_cayley_exp_global_opNorm_le` | Hermitian A and B, step restriction for A+B |
| Correct accumulated exact time | `exactStepHat_fixed_time_pow` | `N > 0`, every real t and every generator |
| Explicit fixed-time rate | `split_cayley_fixed_time_error_le` | Hermitian A and B, `N > 0`, `2|t|‖Hhat‖ ≤ N` |
| Operator-norm convergence | `split_cayley_fixed_time_tendsto_exp` | Hermitian A and B, every real t |
| Error norm tends to zero | `split_cayley_fixed_time_error_tendsto_zero` | Same unrestricted fixed-time assumptions |

All matrix dimensions are arbitrary naturals, including zero. Here
`Hhat = operatorOf (A+B)`, a continuous endomorphism of complex Euclidean space.
The fixed-time approximation uses `α=t/(2N)` and targets `exp((-i*t) • Hhat)`.

The proof uses a geometric domination of the exponential series, an exact
noncommutative rational remainder, resolvent contraction, unitary norm
preservation, finite telescoping, and an eventual squeeze. It does not assume
commutation of A and B or diagonalize them.

Scalar controls detect changed sign, omitted half-step scaling, a false
finite-refinement equality, and a false finite-step equality to the continuous
exponential. They are linked to the actual one-by-one matrix Cayley entry.
The transcendental counterexample is a scalar statement at t=π, outside the
small-step condition; it does not claim a failure of the error estimate.
