# Classical solution and its sampled numerical approximation

Let `Z=diag(1,-1)` and `X=[[0,1],[1,0]]`. The split generators are
`A=-∂xx+Z` and `B=X`; their matrix potentials do not commute. For integer
frequency `m`, set `G_m=m²I+Z+X`. We retain Experiment 009's actual reference

\[
U(t,x)=\sum_{m\in\mathbb Z} e^{imx}e^{-itG_m}a_m.
\]

Assume `Regular a`, meaning the real series
`A₂=Σ_m (1+|m|)² ‖a_m‖` is summable. This is a weighted absolute-summability
condition. It also implies `A=Σ_m ‖a_m‖<∞`. The existing mode norm theorem
gives `‖e^{imx}e^{-itG_m}a_m‖=‖a_m‖` for every real `t,x`.

For a mode `u_m`, the three derivative terms are

\[
v_m=-iG_mu_m,\qquad w_m=im u_m,\qquad z_m=-m^2u_m.
\]

The existing generator estimates imply `‖G_m‖≤m²+2`. Consequently, writing
`b_m=(1+|m|)²‖a_m‖`, the new regularity module proves

\[
\|v_m\|\le2b_m,\qquad\|w_m\|\le b_m,\qquad\|z_m\|\le b_m.
\]

These bounds are uniform on the entire time-space plane. Every series used
below is proved summable; the argument does not use the default value of an
undefined infinite sum.

The infinite-series differentiation theorem applies first to the time variable
and then to the space variable. It gives actual derivatives
`Ut=Σv_m` and `Ux=Σw_m`. Applying the same theorem to the already identified
first spatial derivative gives `Uxx=Σz_m`. The second step uses summability of
`Σw_m` at a base point and the summable bound for `z_m`; no fourth moment is
required. Uniform summable bounds and continuity of each mode also establish
joint continuity of `U`, `Ut`, `Ux`, and `Uxx`.

Each individual mode obeys `i v_m=-z_m+(Z+X)u_m`. Summing this identity and
commuting the bounded linear potential map with the summable series proves

\[
iU_t=-U_{xx}+(Z+X)U
\]

pointwise for every real `t,x`. The predicate `IsClassicalPeriodicSolution`
includes explicit derivative existence, all four joint continuity properties,
periodicity with period `2π`, and the PDE. The retained initial-value identity
is `U(0,x)=Σ_m e^{imx}a_m`.

## Connection to the actual grid

For `d=n+1`, define `sampleSolution n h U t` by evaluating each spin component
of `U(t,jh)` on the periodic grid. Under `Regular a`, this vector equals the
infinite grid reference used in Experiment 009. Thus `classicalGridError`
compares the actual `N`-step split Cayley iterate directly with samples of
the classical solution at time `Nk`; `classicalInitialError` uses time zero.

For the retained hypotheses
`M≥1`, `d>2M`, `dh=2π`, `h>0`, `Mh≤1`, `k≥0`,
`2k(M²+2)≤1`, and `Nk≤T`, the new classical endpoint yields

\[
e_N\le e_0+\sqrt{2\pi}\left[
T\{C_t(M)k^2+C_s(M)h^2\}A+\frac{2A_2}{(M+1)^2}\right],
\]

where `Ct(M)=1000(M²+2)³`, `Cs(M)=M⁴/8`. The two tails remain accounted for
at initial and final times. The constants grow with the retained cutoff.

The existing proved schedule
`M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`
reaches `Nk=1` exactly and satisfies all restrictions. The new endpoint pairs
classical PDE regularity with convergence of the actual sampled error as
`q→∞`, provided sampled initial error tends to zero. Exact sampled initial
values supply a concrete case with zero initial discrepancy.

## Controls and scope

The formal controls construct coefficients nonzero at every signed integer:
`a_m=2^(-encode(m))/(1+|m|)² * v₀`, with a fixed unit spinor `v₀`.
The second weighted norms cancel to a summable geometric sequence. Thus the
classical result has a proved infinite-support instance with positive tails
at every finite cutoff. Other controls check zero and finite data and the
signs of spatial derivatives. See [source](lean/Controls.lean).

The [numerical diagnostics](NUMERICAL_DIAGNOSTICS.md) use a separate signed
geometric sequence with explicit analytic derivative-tail bounds. They provide
floating-point comparisons and wrong-equation controls, without certifying
roundoff or replacing the formal derivative exchange proof.

No spatially varying potential, uniqueness theorem, interpolated norm
convergence, weakening to arbitrary absolutely summable data, or universal
second-order rate for arbitrary infinite data is claimed here.
