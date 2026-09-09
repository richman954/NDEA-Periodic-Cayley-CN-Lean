# Experiment 003 Step 3 — Frozen Specification

Predecessor commit: `b28aabe00cc6a65da8043f71353cf8d496b27379`

Predecessor tag:
`exp003-step2-exact-order-defect-opnorm-bound-verified-final-20260907`

For finite complex Hermitian matrices `A`, `B` and every real `α`, define

`E_local(α) = C_α(A) * C_α(B) - C_α(A + B)`.

Required exact matrix identity:

`E_local(α) = 2 * α^2 *
  (R_{A+B} * B * A * R_A * R_B - A * R_A * B * R_B)`.

Required induced continuous-linear-map operator-norm bound:

`‖E_local(α)‖ ≤ 4 * α^2 * ‖Ahat‖ * ‖Bhat‖`.

The result must cover zero and negative `α`. The discovery chain is Julia exact
Gaussian-rational arithmetic → JSON certificate → independent Python validator
→ arbitrary-matrix Lean proof. Requested controls are a commuting but nonzero
local defect and a proposed counterexample to replacing `α^2` by `|α|` at a
small step; each control must be mathematically checked before certification.

Only Step 3 is in scope. Telescoping and continuous-exponential work are
excluded.
