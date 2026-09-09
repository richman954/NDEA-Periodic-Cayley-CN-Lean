# Experiment 010 numerical derivative diagnostics

`python3 -B numerical_checks.py` passed. The results are saved in
[`evidence/numerical_checks.json`](evidence/numerical_checks.json).

The diagnostic uses the same infinite signed geometric datum as Experiment 009,
with unit spinors

\[
v_0=(3/5,4i/5),\quad v_+=(3/5,4/5),\quad v_-=(4i/5,3/5),
\]

and coefficients

\[
a_0=v_0,\qquad a_m=(i/2)^m v_+\ (m>0),\qquad
a_m=(-i/2)^{-m}v_-\ (m<0).
\]

Every signed integer frequency has a nonzero coefficient. Their norm sum is 3,
and the second weighted norm moment is explicitly finite:

\[
\sum_{m\in\mathbb Z}(1+|m|)^2\|a_m\|=23.
\]

This is a different example from the encoded geometric datum used by the formal
nonvacuity controls. The experiment's theorem covers either datum when its
regularity hypothesis is established; the numerical calculation does not prove
that hypothesis in Lean for this particular diagnostic datum.

For each mode the exact evolution used in this calculation is

\[
U_m(t,x)=e^{i(mx-m^2t)}
\left[\cos(\sqrt2t)I-\frac{i\sin(\sqrt2t)}{\sqrt2}(Z+X)\right]a_m.
\]

The derivative sums use the analytic factors
\(i m\), \(-m^2\), and \(-i[m^2I+(Z+X)]\). The reference sums include
\(|m|\le80\). At 12 space-time points (including negative time, zero time,
positive time, and positive and negative positions), the check compares
\(iU_t+U_{xx}-(Z+X)U\), periodicity, centered finite differences, and
independent closed geometric formulas for the initial value and spatial
derivatives. Existing time-stepping checks are not repeated.

| Check | Result |
| --- | --- |
| Analytic PDE identities | 12 points; maximum residual \(6.38\times10^{-16}\) |
| Periodicity of the value and all three derivatives | Maximum discrepancy \(1.46\times10^{-14}\) |
| Derivative truncation comparisons | 192 cases across cutoffs 4, 8, 12, and 20 |
| Centered finite differences | 36 refinement series, 216 cases; all errors decreased |
| Finest observed finite-difference orders | 1.9374 to 2.0523 |
| Closed initial geometric value/derivative identities | 12 cases |
| Independently summed geometric moment identities | 15 cases |
| Wrong time sign, wrong Laplacian sign, and omitted potential | 36 controls; minimum incorrect residual 0.545 |

For an omitted cutoff \(M\), write \(n=M+1\), \(q=1/2\), and define

\[
S_0(M)=\frac{2q^n}{1-q},
\]
\[
S_1(M)=2q^n\left(\frac n{1-q}+\frac q{(1-q)^2}\right),
\]
\[
S_2(M)=2q^n\left(\frac {n^2}{1-q}+
\frac {2nq}{(1-q)^2}+\frac {q(1+q)}{(1-q)^3}\right).
\]

These are exact-real formulas for
\(2\sum_{m>M}m^j q^m\). Uniform in \(t,x\), the omitted norm tails for
\(U,U_x,U_{xx},U_t\) are bounded by
\(S_0,S_1,S_2,S_2+2S_0\), respectively. The last majorant uses
\(\|Z+X\|\le2\). The recorded comparisons include the reference sum's own
omitted tail; their largest error-to-bound ratio is 0.807.

The tail formulas concern truncation in exact arithmetic. Their displayed
floating-point values, finite-difference orders, and residuals are supporting
diagnostics, not interval-arithmetic or Lean certificates. Cancellation affects
the finest second spatial differences, accounting for the small spread around
order two. The formal proof establishes the infinite derivatives and PDE from
the weighted summability assumption independently of these computations.
