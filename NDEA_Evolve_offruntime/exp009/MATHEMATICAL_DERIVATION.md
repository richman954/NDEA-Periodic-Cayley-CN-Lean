# Infinite Fourier data and a growing cutoff

This document describes the Experiment 009 target and derivation. Accepted
verification status is recorded separately in the final receipts.

The existing two-component mode evolution is
`u_m(t)=exp[-it(m²I+Z+X)] a_m`, with Hermitian `Z+X`. Its norm is
exactly `‖a_m‖`, uniformly in time. Multiplication by `exp(imx)` also
preserves that norm. If `A=Σ_m ‖a_m‖<∞`, then

```text
U(t,x) = Σ_m exp(imx) u_m(t)
```

is an actual absolutely convergent vector series for every `t,x`. It is
periodic with period `2π` and has the indicated initial Fourier series. Its
grid reference is the convergent series of the actual sampled mode lifts.
Continuous coordinate projections commute with this sum, identifying the
grid reference with pointwise samples of `U`.

Let `B_M={m∈ℤ:|m|≤M}`, `U_M` be its finite partial sum, and
`τ_M=A-Σ_{m∈B_M}‖a_m‖`. Absolute summability proves that this difference
equals the sum of the omitted nonnegative norms and tends to zero as `M→∞`.
The exact single-mode weighted grid norm is `√(2π)‖a_m‖` when `dh=2π`.
Applying the triangle inequality to the omitted series yields, at every time,

```text
√h ‖R_h U(t) - R_h U_M(t)‖ ≤ √(2π) τ_M.
```

This bound allows arbitrary aliasing among omitted frequencies. It does not
use an infinite discrete Parseval identity. The finite reference band still
satisfies Experiment 008's `d>2M` restriction, so its established coefficient
ℓ² error estimate applies. Its coefficient ℓ² norm is at most the finite ℓ¹
sum, hence at most `A`.

For an arbitrary numerical initial state `W₀`, its discrepancy from the
finite reference is bounded by its discrepancy from the full reference plus
one tail. The final discrepancy adds a second tail. Combining these two
triangle inequalities with the established finite-grid theorem gives

```text
e_N ≤ e_0 + √(2π) [ T (Ct(M) k² + Cs(M) h²) A + 2 τ_M ],
Ct(M)=1000(M²+2)³,  Cs(M)=M⁴/8,  Nk≤T.
```

Here both `e_N` and `e_0` compare actual grid states with the full infinite
reference. For exact initialization by its full samples, `e_0=0`. No
truncation premise is assumed in place of the proved tail estimate.

The generic convergence argument squeezes the nonnegative error between zero
and this upper bound. It requires a growing cutoff, vanishing explicit
consistency cost, and vanishing full-reference initial error. It retains all
finite-band mesh and step restrictions on every member of the sequence.

One admissible sequence is

```text
M=q+1, d=8M³, h=π/(4M³), k=1/(6M⁴), N=6M⁴, T=1.
```

It has `d>2M`, `Mh≤1`, `2k(M²+2)≤1`, and `Nk=1`. Direct algebra gives

```text
Ct(M)k² + Cs(M)h²
  = [ (1000/36)(1+2/M²)³ + π²/128 ] / M² → 0.
```

Thus the theorem has a concrete sequence of grids, timesteps and integer
step counts that reaches the same final time. It is not merely conditional
on finding such a sequence.

For a summable weighted moment
`A_r=Σ_m (1+|m|)^r ‖a_m‖`, `r∈ℕ`, the omitted terms satisfy
`(M+1)^r τ_M≤A_r`. This supplies a quantitative tail estimate and implies
absolute summability. For `r≥2`, the displayed schedule therefore has an
upper bound of order `M⁻²` when the initial error has that order. Absolute
summability alone gives convergence without a universal polynomial tail
rate. The schedule does not establish a uniform second-order mesh rate for
arbitrary infinite data.

The infinite reference evolves each Fourier mode of the same constant-matrix
noncommuting spinor model. This milestone does not interchange infinite sums
with time or second-space derivatives, assert a classical PDE under ℓ¹ alone,
handle variable spatial potentials, or construct a continuum interpolation of
the numerical grid. Those remain separate extensions.
