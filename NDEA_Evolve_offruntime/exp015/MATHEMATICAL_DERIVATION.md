# Experiment015 — forcing, residual, and solution error

The intended endpoint concerns the actual periodic linear Schrödinger equation
`i u_t = -u_xx + V(t,x)u + f(t,x)` in an arbitrary complete complex Hilbert
space. The period is positive. The two fields being compared satisfy the
unchanged Exp013 classical predicate, have the same pointwise selfadjoint
potential, and have a jointly continuous forcing difference. This continuity
is an explicit assumption: it is not implied by the generic classical
predicate for an unrestricted potential. The initial implementation assumes
global joint continuity; the estimate is evaluated on any finite interval
`s <= t`. No extension to rough or merely distributional solutions is claimed.

For a continuous spatial field define

```text
N(q) = sqrt(integral_[b,b+L] ||q(x)||^2 dx).
```

1. Subtract the two actual PDEs using Exp013's classical subtraction result.
   The error `w=u-v` has forcing `h=f-g` and the same potential.
2. Exp013's energy identity gives
   `E'(r) = integral 2 Re <w(r,x), -i h(r,x)> dx`, where `E=N(w)^2`.
   Pointwise selfadjointness cancels the potential term; periodicity cancels
   the spatial flux. No size bound on the common potential enters this step.
3. The pointwise inner-product bound and spatial Cauchy–Schwarz give
   `E'(r) <= 2 sqrt(E(r)) N(h(r))`. Spatial Cauchy–Schwarz is proved from
   nonnegativity of the integral of a real square. Joint continuity supplies
   the spatial integrability and continuity of `N(h(r))` in time.
4. For positive epsilon, differentiate `sqrt(E+epsilon^2)`. Its derivative
   is at most `N(h)`, since `sqrt(E) <= sqrt(E+epsilon^2)`. Integrate this
   inequality and use `sqrt(E(s)+epsilon^2) <= sqrt(E(s))+epsilon`.
   A positive-gap argument removes epsilon. There is no division by a possibly
   zero error norm and no assumption that initial error is positive.

The resulting target is the coefficient-one estimate

```text
N(u(t)-v(t)) <= N(u(s)-v(s)) + integral_s^t N(f(r)-g(r)) dr.
```

For a regular periodic approximate field `w`, its PDE residual is defined by
its actual derivatives:

```text
R_V[w] = i partial_t w + partial_xx w - V w.
```

The regularity predicate lists differentiability, joint continuity of the
field and its required derivatives, and periodicity. These properties imply
that `w` is a classical forced solution with forcing exactly `R_V[w]`.
Consequently the same estimate compares it with a given forced solution using
`R_V[w]-f`, or with an unforced solution using `R_V[w]`. For a jointly
continuous operator potential, residual continuity follows from the field's
regularity. A uniform residual bound `delta` gives accumulated error at most
`(t-s)*delta`, while retaining the full initial error.

The variable-potential bridge uses the actual global solution constructed in
Exp014, with its original weighted absolute Fourier regularity and Hermitian
coefficient symmetry. It preserves arbitrary initial mismatch and also covers
exact initialization from the prescribed infinite Fourier series.

An active constant forcing control uses `w(t,x)=t` as a complex field with
zero potential on a unit spatial period. Its residual is `i`, its initial
error against zero is zero, and at time1 both the error and integrated
residual norm equal1. This tests the coefficient and forcing sign. A nonzero
stationary field checks preservation of initial error when the residual is zero.

The proof is a continuum L2 error estimate. Applying it to actual discrete
iterates requires a suitable regular reconstruction and a derived bound on
that reconstruction's residual. In particular, an arbitrary discontinuous
piecewise-constant reconstruction does not satisfy this regularity predicate.
The discrete consistency and refinement argument remains later work.

Read actual modular, combined, independent, and transfer receipts before
treating the intended result as accepted. Compiler and compatible compiled
library artifacts remain trusted inputs in the verification setup.
