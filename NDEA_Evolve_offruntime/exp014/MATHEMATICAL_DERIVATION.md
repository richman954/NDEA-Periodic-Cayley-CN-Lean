# Experiment 014 construction — mathematical description

This document explains the construction. Accepted modular, combined and
independent receipts determine which formal claims have completed verification.

Let H be a complete complex Hilbert space, let w(m)=(1+|m|)^2 for integer m,
and assume

    Σ_m w(m) ‖a(m)‖ < ∞,       Σ_j w(j) ‖v(j)‖ < ∞.

Here a(m) lies in H and v(j) is a bounded complex-linear operator on H. The
potential is V(x)=Σ_j exp(i j x) v(j). The symmetry v(-j)=v(j)* makes V(x)
selfadjoint. The potential may vary with position and couple infinitely many
Fourier modes. No commutation with the spatial Laplacian is required.

The target is a unique global classical 2π-periodic solution of

    i u_t = -u_xx + V(x)u,       u(0,x)=Σ_m exp(i m x) a(m),

where time ranges over all real numbers. Uniqueness is among all functions in
Experiment 013's classical periodic solution class, without requiring the
competing solution to have this Fourier construction.

## Complete state and bounded convolution

Store b(m)=w(m)a(m) in ℓ¹(ℤ;H), and decode coefficients by a(m)=b(m)/w(m).
The elementary weight inequality w(m+n)≤w(m)w(n) bounds the shifted operator

    (T_j b)(m) = w(m)/w(m-j) · v(j)b(m-j)

by ‖T_j‖≤w(j)‖v(j)‖. Hence C=Σ_j T_j converges in operator norm. Its decoded
coefficients are the ordinary convolution of v with a. Reindexing each single
shift and then applying bounded synthesis to the convergent operator sum gives
synth(Cb,x)=V(x)synth(b,x). This route does not assume an unproved exchange of
an arbitrary double series.

## Global interaction evolution

The free group S(t)b(m)=exp(-i m²t)b(m) is isometric, obeys the group law and
is jointly continuous in (t,b). Operator-norm continuity is not assumed.
Define B(t)=-i S(-t) C S(t). The map (t,b)↦B(t)b is continuous and
‖B(t)‖≤‖C‖ for every real t.

The reusable real Banach-space evolution theorem constructs b'=B(t)b by
iterated integrals P₀(t)=b₀ and Pₙ₊₁(t)=∫₀ᵗ B(s)Pₙ(s)ds. Its bound is

    ‖Pₙ(t)‖ ≤ (K|t|)^n/n! · ‖b₀‖.

The sum converges for every real time. On a neighborhood of each time, the
series of derivatives has a factorial summable majorant, so differentiating
the sum gives the actual ODE. Negative time is included in the same integral
argument. This constructs the solution without a finite-mode cutoff.

## Actual PDE derivatives

Write q(t)=S(t)b(t) and u(t,x)=Σ_m exp(i m x)q(t,m)/w(m). The multipliers
for u, u_x and u_xx are respectively exp(i m x)/w(m), i m times that factor,
and -m² times that factor. Each has norm at most one. They define bounded
maps from ℓ¹ to H, and each is jointly continuous in position and state.
Termwise spatial differentiation is justified with the summable majorant
‖q(m)‖ for a fixed state.

For fixed b, differentiating synth(S(t)b,x) is justified by the same ℓ¹
majorant since m²/w(m)≤1. It gives i·synthSecond(S(t)b,x). A separately proved
strong-operator product rule handles the differentiable interaction state
b(t); it needs joint continuity of the evaluation (t,b)↦A(t)b and the
fixed-state derivative, not differentiability in operator norm. This avoids
requiring an unintended fourth Fourier moment.

The resulting time derivative is

    u_t = i u_xx - i V(x)u.

All actual derivatives in the classical predicate are identified with these
continuous synthesized expressions. Periodicity and the initial field follow
from the Fourier characters and S(0)=identity. Experiment 013's positive-period
selfadjoint uniqueness theorem then changes existence into unique existence.

## Limits of this milestone

This is a regular linear periodic Schrödinger class with a time-independent
operator-valued potential. It does not assert existence for arbitrary nonlinear
PDEs, arbitrary irregular coefficients, rough L² initial data, or other boundary
conditions. Numerical convergence for this enlarged class needs additional
consistency and approximation estimates beyond this existence construction.
