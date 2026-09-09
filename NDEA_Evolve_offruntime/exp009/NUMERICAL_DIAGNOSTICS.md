# Experiment 009 numerical diagnostic

Run `python3 -B numerical_checks.py` from this directory. The standalone script
uses only the Python standard library and writes `evidence/numerical_checks.json`.
These are floating-point diagnostics; the Lean sources carry the formal claims.

The datum is a genuinely infinite signed Fourier series. With `q=1/2` and the
three unit spinors displayed in the result file, its coefficients are

```text
a_0 = v_zero,
a_m = (i q)^m v_plus,       a_{-m} = (-i q)^m v_minus   (m >= 1).
```

Every positive and negative frequency is active and both spinor components are
active. The coefficient norm sum is `3`; the norm sum outside `[-M,M]` is
`2 q^(M+1)/(1-q) = 2^(1-M)`. Closed geometric sums for congruence classes modulo
the grid size evaluate the full sampled initial datum. They retain aliasing,
including aliases from frequencies above the grid size.

The reference at terminal time `T=1` sums modes `-48,...,48`. Norm preservation
of the continuum spinor orbit and the triangle inequality give the analytic
weighted sample-tail bound

```text
sqrt(2*pi) * 2 q^49/(1-q) = approximately 1.7810665117899306e-14.
```

This controls omitted terms in exact arithmetic. It does not bound roundoff,
and the displayed error intervals are not interval-arithmetic certificates.
After combining alias contributions, the script uses the ordinary finite
discrete Fourier norm identity on the grid. It assumes no infinite Parseval
identity and no sampling estimate from the infinite coefficient l2 norm.

The six refinement levels use `M=1,2,3,4,6,8`, `d=8M^3`, `N=6M^4`, and `k=1/N`.
At each level the script checks both endpoint truncation discrepancies, the
finite-cutoff comparison, and the proposed full-data bound

```text
e_N <= e_0 + sqrt(2*pi) * [T (Ct(M) k^2 + Cs(M) h^2) * 3 + 2 tail_M(a)],
Ct(M) = 1000 (M^2+2)^3,    Cs(M) = M^4/8.
```

There are twelve trajectory cases: exact full sampled initialization and a
perturbation at alias residue `d/2` with coefficient norm `1/(100 M^2)`.
The entire perturbation contributes to `e_0`. Errors, both tail budgets, and
consistency budgets decrease over the tested schedule. At the finest level,
the exact-initialization error is approximately `3.23627e-5`; the perturbed
error is approximately `3.92995e-4`.

The observed orders approximately `6.02` and `2.10` are measured with respect
to increasing cutoff **M**, not with respect to the time step or mesh spacing.
Here `h` decreases like `M^-3`; the displayed theorem bound remains much more
conservative than the measured error.

Two small-grid checks compare closed initial samples, finite alias norms,
the actual wrapped centered stencil, the first two Cayley stage residuals,
and numerical norm preservation. Three sensitivity controls put coherent
coefficients of norm `1/K` at frequencies `d,2d,...,Kd`, for `K=4,16,64`.
All these frequencies lie outside the cutoff, their coefficient l2 norm is
`1/sqrt(K)`, and their weighted sample norm remains `sqrt(2*pi)`. Thus the
naive l2 sample-tail estimate fails while the l1 sample-tail bound stays valid.

The local run passed all twelve trajectory cases, twelve endpoint-tail checks,
two small-grid cases, and three aliasing controls. Its largest measured
small-grid discrepancy was approximately `3.07e-13`.
