# Experiment 006: concrete nonzero periodic Fourier residual

Date: 2026-09-08. Exp005 is frozen and read-only.

The first bounded milestone derives, rather than assumes, the three-stage
residual budget for the smooth, nonconstant mode
`U(t,x) = exp(i*(x-2*t))` on the circle of length `2*pi`, solving
`i*U_t = -2*U_xx`, split into `A = B = -d_xx`.
The discretization is the centered negative second difference, and the exact
reference split stages have phase increments `k/2`, `k`, `k/2`.

Planned checks:
1. Prove the concrete solution is periodic and solves its PDE.
2. Derive the symbol from actual neighboring field samples.
3. Derive `|lambda_h-1| <= h^2/8` for `0<h<=1` from a library Taylor bound.
4. Derive the actual Cayley factor residual bound
   `2*alpha^3 + alpha*h^2/4` for `0<=alpha<=1`.
5. Sum all three unscaled residuals for `0<=k<=2`, obtaining
   `sqrt(L)*k*((5/16)*k^2 + (1/4)*h^2)` when `n*h=L`.
6. Connect the explicit residual vector to Exp005's operator interface if
   feasible; record exactly where the checked boundary lies.

Scope is one nonzero Fourier mode and a commuting split. It does not settle
noncommuting operators, variable potentials, arbitrary smooth solutions,
interpolation convergence, or sharp constants. Both split generators act
nontrivially. The spatial consistency term is present and derived. Bounds
restrict h and k directly, not through mesh-dependent generator norms.

All new source, logs, receipts, and status are written under exp006. Pinned
Lean v4.31.0 and the existing local Mathlib cache are used without downloads.
