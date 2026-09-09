
# NDEA-Evolve Experiment 001 — final evaluation

Status: **COMPLETE / FULLY GREEN**, conditional only on the included manifest logs
remaining PASS when copied. Preclosure was 79/79 PASS and the final payload is covered
by the layered SHA-256 manifests.

## FORMALLY VERIFIED

Lean 4.31.0 with pinned Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` independently verifies:

- the unit complex phase has norm one;
- opposite phase exponentials sum to `2*cos(theta)`;
- the centered negative-Laplacian symbol equals `4*sin(theta/2)^2`;
- `lambda_h(theta) = (4/h^2)*sin(theta/2)^2`;
- nonnegativity for real `theta` and `h != 0`;
- the local Fourier-neighbor stencil eigen-relation;
- Cayley numerator and denominator squared norms equal `1+a^2` for real `a`;
- denominator nonvanishing, scalar update, and unit modulus;
- headline theorem `cayleyCN_fourier_mode_stability h k theta (hh : 0 < h)`.

The current verbose Lake build passed with 8,558 jobs, exit 0, 8,694 log lines,
and SHA-256 `05c52e64892b2d6b4513c50f0b897d5ad0ce4cde22d8075d0ae90c80b887dae1`. Twelve declarations were inspected. The
headline logical dependencies are exactly `['propext', 'Classical.choice', 'Quot.sound']`; no unexpected custom
logical assumptions and no `sorryAx` appeared. Four false/altered Lean controls were
rejected with exit 1 and relevant goals. The production forbidden-token scan found
zero matches across 3 declared production Lean files.

## EXACTLY DERIVED BY JULIA

Using `Rational{BigInt}` and `Complex{Rational{BigInt}}`, Julia exactly derived
or reconstructed:

- stencil Laurent coefficients `[-1 => -1, 0 => 2, 1 => -1]`;
- `(1-z)*(1-z^(-1)) = 2-z-z^(-1)`;
- the coefficient transformation to `4*s^2` after invoking the named half-angle identity;
- Cayley numerator/denominator coefficient arrays;
- exact scalar cross multiplication for the solved amplification factor;
- both norm-squared polynomials `1+a^2`;
- four rational sample identities;
- exact wrong-full-angle witness at `z=-1` (`4` versus `0`);
- exact reversed-stencil mismatch, wrong-numerator witness, and non-real parameter
  witness `a=i/2` giving amplification `3` and squared modulus `9`;
- the `h=0` domain guard.

The corrected Julia source hash is `20ee35c97ef47dc05a4b684630d1df4d519b3bc1a85984d914c4e027c6d49410`; the certificate hash is
`d842fc370f19f588cef2bbf5c824c00f4527918ac76073aadc86087080f326cc`. The independent validator reconstructed all named exact
components and returned exit 0.

## NUMERICALLY TESTED

- 4200 periodic-mode cases at 256-bit `BigFloat` precision.
- Maximum eigen residual: `5.856064689029755101450332912331364040279732632890941000517224976954509865960294e-73`.
- Maximum modulus-squared error: `3.454467422037777850154540745120159828446400145774512554009481388067436721264971e-77`.
- 256 deterministic Float64 counterexample-search cases,
  seed `1313097025`.
- Maximum Float64 eigen residual: `4.353521767397678e-8`.
- Maximum normalized eigen residual: `8.113937788932373e-10`.
- Maximum mixed-bound ratio: `0.45112563591790467`.
- Maximum modulus-squared error: `4.440892098500626e-16`.

These observations test finite periodic indexing, constant and Nyquist modes, positive
and negative nonzero `h`, and zero/positive/negative `k`; they are evidence, not proof.

## INFORMALLY INTERPRETED

- Euler's identity and the standard trigonometric half-angle identity connect Julia's
  exact coefficient manipulations to real-angle expressions; Lean proves the needed
  analytic identities independently.
- `theta = 2*pi*m/N` interprets the local phase theorem as a periodic grid mode.
- The scalar Cayley equation is interpreted as the modal Crank–Nicolson update.
- The Julia/JSON names are mapped to Lean definitions by transparent documentation
  and source hashes; no formal cross-language semantics theorem is asserted.

## NOT VERIFIED / OUT OF SCOPE

- an explicit finite `ZMod N` vector/matrix diagonalization or full DFT theorem in Lean;
- formal proof inside Lean of the quantization equation `theta = 2*pi*m/N`;
- derivation of the scalar Crank–Nicolson equation from a full PDE semidiscretization;
- convergence order, dispersion error, truncation error, nonlinear stability, or
  floating-point roundoff bounds;
- QGI, topology/geometry, inverse-integrator, or legacy restore work;
- treating the three identical geometry transcripts as independent evidence;
- reconstructing unavailable original baseline-report bytes or unavailable historical
  failed-source bytes beyond preserved hashes, executed-code history, and diagnostics.

## Assurance summary

- Julia discovery/certificate: PASS
- strengthened independent validator: PASS
- Lean headline theorem: PASS
- verbose build: PASS
- negative controls: 4/4 expected rejection
- theorem signature inspection: PASS
- logical-dependency audit: PASS; headline `['propext', 'Classical.choice', 'Quot.sound']`
- forbidden-token scan: PASS, zero matches
- final preclosure: 79/79 PASS
- local intake initial/append: 17/17 and 12/12 PASS; not proof inputs
- manifests: layered SHA-256 verification logs included
