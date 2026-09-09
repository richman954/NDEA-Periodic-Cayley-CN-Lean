# From numerical grid iterates to a uniformly convergent space-time field

Retain Experiment 010's classical periodic spinor solution
`U(t,x)=Σ_m exp(imx) exp[-it(m²I+Z+X)] a_m`, with
`A₂=Σ_m(1+|m|)² ‖a_m‖<∞`. Let `A=Σ_m ‖a_m‖`; then `A≤A₂`.
Its actual derivative series satisfy uniform bounds

```text
‖Ux(t,x)‖ ≤ A₂,          ‖Ut(t,x)‖ ≤ 2A₂.
```

The mean value inequality gives
`‖U(t,x)−U(t,y)‖≤A₂|x−y|` and
`‖U(t,x)−U(s,x)‖≤2A₂|t−s|`. These bounds are derived from the actual
derivatives and their summable majorants; they are not additional assumptions.

## Explicit reconstruction

Write `d=n+1` and let `v_j=S_h(k)^j sample(U(0))` be the actual full-grid
symmetric Cayley iterate with exact sampled initial values. For
`0≤x≤dh` and `0≤t≤Nk`, define

```text
i(x)=min(floor(x/h),d−1),       j(t)=min(floor(t/k),N),
R(t,x)=the two spin components of v_j(t) at node i(x).
```

The proof establishes `0≤x−i(x)h≤h`, `0≤t−j(t)k≤k`, and `j(t)≤N`.
All definitions are explicit functions of the actual iterates. The finite
reconstruction is piecewise constant. At `x=dh` it uses the last node rather
than a separate periodic identification; its endpoint discrepancy is included
in the spatial error bound.

Extracting one spinor block cannot increase the full Euclidean grid norm.
For the mesh-weighted grid error `e_j=sqrt(h)‖v_j−sample(U(jk))‖`, this gives

```text
‖R(t,x)−U(t,x)‖ ≤ e_j(t)/sqrt(h) + A₂*h + 2A₂*k.
```

This is a triangle inequality through `U(jk,ih)` and `U(jk,x)` using the two
proved derivative bounds. The factor `1/sqrt(h)` is essential when converting
a weighted global norm to the value of a single spinor block.

## Bound for every scheduled step

Use the already proved schedule
`M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`.
It reaches `Nk=1` and satisfies every predecessor restriction. If `j≤N`,
then `jk≤1`, so the Experiment 010 error bound applies with common horizon one.
Exact sampling makes the initial grid error zero. It follows that

```text
e_j ≤ sqrt(2π) [ (Ct(M)k²+Cs(M)h²)A + 2A₂/(M+1)² ],
Ct(M)=1000(M²+2)³,       Cs(M)=M⁴/8.
```

Let `r=1/M` and
`G(r)=(1000/36)(1+2r²)³+π²/128+2`. The consistency identity from
Experiment 009, `A≤A₂`, and `(M+1)⁻²≤M⁻²` yield

```text
e_j ≤ sqrt(2π) A₂ G(r) r².
```

The exact nonnegative square-root identity
`sqrt(2π)r²/sqrt((π/4)r³)=sqrt(8r)` now gives

```text
e_j/sqrt(h) ≤ A₂ G(r) sqrt(8r).
```

This bound is independent of the chosen step `j≤N` and tends to zero as
`q→∞`: `r→0`, while `G(r)` tends to a finite constant. Thus the full field
satisfies the displayed bound in the [completion report](COMPLETION_REPORT.md)
uniformly for `0≤t≤1`, `0≤x≤2π`.

The formal endpoint is `TendstoUniformlyOn` for the actual reconstructed
`E 2`-valued functions on the closed space-time rectangle. It is paired with
Experiment 010's explicit classical-solution predicate, which includes the
existence and joint continuity of the required derivatives and the pointwise
PDE. Pointwise convergence throughout the rectangle is also exposed directly.

## Scope and controls

The full initial sample vector uses the infinite reference. Exact
initialization is part of this theorem. Merely knowing that weighted initial
error tends to zero would not justify division by `sqrt(h)`; an extension to
perturbed initialization needs additional control at that scale.

The rate bound is conservative and need not predict the observed refinement
order. Finite reconstructed fields may be discontinuous and need not have
matching endpoint values; the uniform limit is the periodic classical
solution. This theorem establishes convergence on a common continuum domain
without asserting a new uniqueness or variable-potential theorem.

Exact controls exercise node extraction, endpoint/time indices, the necessary
inverse-mesh factor, and an infinite-support regular coefficient witness.
[Numerical diagnostics](NUMERICAL_DIAGNOSTICS.md) separately check off-grid
reconstruction using exact-real geometric alias formulas and a qualified
truncated continuum reference. Their floating-point errors are supplementary.
