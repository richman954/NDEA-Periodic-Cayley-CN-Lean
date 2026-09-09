# Experiment 003 Step 4 — Frozen Specification

Predecessor commit: `e4dc7128c4651974bbab405726e586b04fb9b3dc`

Predecessor tag:
`exp003-step3-exact-split-unsplit-cayley-defect-verified-final-20260907`

For finite complex Hermitian matrices `A`, `B`, every real `alpha`, and every
natural `N`, define

- `S_hat = Chat A alpha * Chat B alpha`;
- `U_hat = Chat (A + B) alpha`.

Required algebraic identity:

`S_hat^N - U_hat^N =
  sum k in Finset.range N,
    S_hat^(N - 1 - k) * (S_hat - U_hat) * U_hat^k`.

Required induced continuous-linear-map operator-norm bound:

`‖S_hat^N - U_hat^N‖ <=
  (N : Real) * 4 * alpha^2 * ‖Ahat‖ * ‖Bhat‖`.

The identity and bound include `N = 0` and all real `alpha`. All norms are the
induced norm on `E n ->L[Complex] E n`.

Requested focused controls are: a non-unitary scalar blowup witness at `N = 2`,
`S = 2I`, `U = I`; and a proposed `N^2` scaling trap, to be mathematically
checked before formalization. The latter request uses strict slack as its
proposed witness and therefore concerns sharpness rather than falsity of an
upper bound.

Only Step 4 is in scope. Continuous-exponential work is excluded.
