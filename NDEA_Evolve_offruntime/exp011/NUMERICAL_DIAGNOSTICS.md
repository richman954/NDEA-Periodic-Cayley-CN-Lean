# Off-grid space-time reconstruction diagnostics

The standalone [script](numerical_checks.py) checks the new reconstruction
using ordinary binary floating-point arithmetic. The current
[result](evidence/numerical_checks.json) records `passed: true`, its script
SHA-256, all cases, and a concise summary. These calculations support the
formal result; they do not prove a supremum estimate or certify roundoff.

The datum is the same infinite signed geometric example used in the previous
classical derivative diagnostics:

\[
a_0=(3/5,4i/5),\quad
a_m=(i/2)^m(3/5,4/5)\ (m>0),\quad
a_{-m}=(-i/2)^m(4i/5,3/5)\ (m>0).
\]

Its second weighted norm moment is exactly 23. All three seed spinors have
unit norm. The script checks the corresponding geometric moment formula.

Initial grid values use closed geometric sums over every Fourier congruence
class, including the aliases of arbitrarily high frequencies. Thus no finite
initial spectral cutoff is substituted for the definition of `gridState`.
The closed formulas are evaluated in floating point, with the usual rounding
and underflow limits. The numerical state uses integer powers of the actual
two-by-two modal symmetric Cayley step at every discrete frequency.

An independent dense computation builds the full spinor centered-difference
and potential matrices, with both periodic wraps, and solves their three
Cayley stages by complex Gaussian elimination. At 8 and 16 grid points it
checks the initial state and three subsequent steps against the modal state:
96 node comparisons and 32 off-grid block-extraction comparisons passed.
The largest dense/modal node discrepancy was approximately `2.02e-15`.
This is a focused check that the new reconstructed values belong to the
actual full-grid iterate.

For the formal refinement schedule `d=8M³`, `k=1/(6M⁴)`, and `Nk=1`, four
levels check 476 space-time points. The points include off-grid positions,
times between steps, both spatial endpoints, and the terminal time. Spatial
fractions `x/(2π)` and times are represented as exact rational numbers for
index selection, avoiding accidental boundary changes caused by dividing
rounded floating-point values. Values of the PDE and numerical state are
then evaluated in ordinary floating point.

| Cutoff `M` | Grid points | Time steps | Largest sampled reconstruction error |
| --- | --- | --- | --- |
| 1 | 8 | 6 | 0.969643 |
| 2 | 64 | 96 | 0.176699 |
| 4 | 512 | 1536 | 0.0191919 |
| 8 | 4096 | 24576 | 0.00257361 |

The finest sampled order with respect to mesh spacing is approximately
`0.9662`. Doubling `M` divides the mesh spacing by eight; the corresponding
order with respect to `M` is `2.8986`. These are sampled observations, not
proved rates or measurements of the full continuum supremum.

Each case checks the decomposition into nodal error, spatial holding error,
and temporal holding error. The spatial term is compared with `23*|x-y|`
and the temporal term with `46*|t-s|`, matching the actual derivative bounds.
The finite alias norm bounds the extracted spinor's nodal error after adding
the reference-tail allowance. The final error is also compared with the
formal, deliberately non-sharp uniform envelope. That envelope is much larger
than these observed errors.

Reference solution values retain frequencies `|m|≤80`. The omitted
pointwise series has the exact-real upper bound

\[
\sum_{|m|>80}\|a_m\|=
\frac{2(1/2)^{81}}{1-1/2}
=1.6543612251060553\times10^{-24}.
\]

The corresponding omitted sampled weighted norm is at most `sqrt(2π)` times
this quantity. These formulas concern mathematical truncation only. They
are not error certificates for evaluating the formulas or the finite sums.

Four endpoint pairs confirm the prescribed clamps: `x=2π` selects the last
spatial node, while `t=1` selects the last actual step. The finite reconstructed
field is defined on the closed rectangle; it need not agree at its two spatial
endpoints. Eight sensitivity controls compare the correct interior floors
with a wrong next spatial node or next time step. All differences were large
enough to detect those changes.

Run the focused diagnostics without external Python packages:

```sh
python3 -B numerical_checks.py
```

The matrix, geometric-alias, and closed mode formulas are adapted from the
previous experiments. The script is standalone and does not rerun their
unchanged stage-residual or derivative finite-difference suites.
