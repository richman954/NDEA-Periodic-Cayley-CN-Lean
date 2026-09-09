# Failure and repair log

## Endpoint recovery

The original named Colab endpoint returned 404/401 and then disappeared from named
status on a bounded recheck. One authorized standard CPU replacement was created.
The verified preflight Git bundle was restored at commit
`57e519300ce3d03e2ceb8f658c8752561b0f801c`; exact pins were reinstalled only because
the replacement lacked them. Unidentified sessions were not stopped or adopted.

## Recovered Julia attempt 0

The pristine recovered source exited 1 while trying to record the non-Hermitian
counterexample. `cayley_data(...; require_hermitian=false)` still asserted a
Hermitian-only unitarity residual. The pristine bytes and full rejection log remain
under `recovery/`.

Repair: always check inverse/update/polynomial structure, but check adjoint, Gram, and
unitarity residuals only when the Hermitian premise is asserted.

## Repaired Julia attempt 1

The next run exited 1 because the proposed “wrong inverse order” was actually equal
to the correct defect expression. Exact audit showed that reversing both inverse
pairs is a second valid resolvent-commutator identity.

Repair: preserve the equivalent identity and use a one-sided inverse permutation as
the false control. Add the frozen false Cayley-semigroup witness.

## Repaired Julia attempt 2

The next run exited 1 under Julia 1.12 because top-level counter mutations inside
loops had ambiguous soft scope.

Repair: isolate exhaustive search and numerical trials in explicit functions.

## Numerical repair

The recovered code multiplied leading principal blocks cut from independently sized
unitary matrices and assigned PASS without a limit. A principal block need not be
unitary.

Repair: generate three full factors at each common dimension, form their ordered
product, use the Euclidean induced operator 2-norm, require finite results, and enforce
the source-fixed `1e-10` limit.

All failed attempts and repairs are evidence; no failed state is labeled green.
