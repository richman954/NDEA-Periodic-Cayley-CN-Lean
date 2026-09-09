# Experiment 014 Fourier state-space design

The proposed existence construction uses all integer Fourier modes in a
complete weighted sequence space. It does not need an assumption asserting a
Fourier basis or convergence of finite-dimensional approximations.

This document records API and mathematical design findings. The accepted Lean
receipts and final verification report, when available, determine which parts
have actually been checked.

## Complete state space and initial data

Set `weight m = (1 + |(m : ℝ)|)^2`. Store `b m = weight m • a m` in
`lp (fun _ : ℤ => H) 1`, with `H` a complex Banach space. Mathlib already
supplies the normed-space and completeness instances for this ℓ¹ space.
The decoded physical coefficient is `(weight m)⁻¹ • b m`.

`WeightedFourier.lean` exposes `FourierState`, `coefficient`,
`coefficientCLM`, `state_summable_norm`, and `state_tsum_norm`. Its weighted
norm identity is exactly

```text
sum_m weight m * norm (coefficient b m) = norm b.
```

The raw-data constructor `ofCoefficients a ha` accepts any integer-indexed
family satisfying `Summable (fun m => weight m * ‖a m‖)`.
`coefficient_ofCoefficients` recovers every original coefficient, and
`ofCoefficients_norm` gives the corresponding weighted sum. Thus a final
existence endpoint can quantify over the user's prescribed coefficients
without requiring them to supply a bundled state.

The bounds `1 ≤ weight m`, `|m| ≤ weight m`, and `m² ≤ weight m`
make the zeroth, first, and second spatial synthesis operators bounded.

## Free evolution and the correct continuity notion

`freeFlow t` multiplies coordinate `m` by `exp(-i*m²*t)`. It is a complex
linear isometry, forms a group, and is continuous in time at each fixed state.
Joint continuity in `(t,b)` follows from this strong continuity and the common
norm bound one. A summable single-coordinate expansion gives a direct proof
using `lp.hasSum_single` and `continuous_tsum`.

Operator-norm continuity of the free group is not available in general: its
frequencies are unbounded. The interaction operator
`freeFlow (-t) ∘ potentialConvolution ∘ freeFlow t` also need not be continuous
in operator norm. A nonzero frequency shift produces phases involving an
unbounded multiple of `t`. The Banach ODE construction should use joint
continuity of its action on a state and a uniform Lipschitz bound in the state.

Likewise, a continuous curve into ℓ¹ on a compact interval need not have a
summable coordinatewise supremum envelope. Compact families of shrinking
single-coordinate spikes demonstrate the obstruction. Derivative synthesis
for an evolving state should therefore use bounded synthesis maps and strong
operator differentiation, rather than assume a global coordinate majorant.

## Regular variable-potential multiplication

The weight is submultiplicative:
`weight (m+n) ≤ weight m * weight n`. For an operator Fourier coefficient
`V j`, define a weighted shifted action at coordinate `m` by

```text
(weight m / weight (m-j)) • V j (b (m-j)).
```

Its norm is at most `weight j * ‖V j‖`. Weighted absolute summability of the
potential coefficients therefore yields an absolutely convergent series of
bounded linear operators on the state space. This constructs the full
convolution without requiring a separate weighted Young inequality library.
Single-shift synthesis identities and continuity of bounded linear maps can
then identify convolution with multiplication by the synthesized potential.

## Pinned Mathlib APIs inspected

All paths below are relative to the pinned Mathlib checkout
`NDEA/workspace/NDEAMathlibGate/.lake/packages/mathlib`, revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

- `Mathlib/Analysis/Normed/Lp/lpSpace.lean`: `Memℓp`,
  `memℓp_gen_iff`, `Memℓp.mono'`, `Memℓp.summable`,
  `lp.norm_eq_tsum_rpow`, `lp.tsumCLM`, `lp.hasSum_single`,
  `lp.singleContinuousLinearMap`, `lp.evalCLM`, and `lp.completeSpace`.
- `Mathlib/Analysis/Normed/Lp/lpHolder.lean`: `lp.mapCLM`,
  `lp.norm_mapCLM_le`, and `lp.norm_tsumCLM_le`. The summation map's
  scalar/index arguments are `lp.tsumCLM ℂ ℤ H`.
- `Mathlib/Analysis/Normed/Group/FunctionSeries.lean`: `continuous_tsum`.
- `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean` and
  `Mathlib/Analysis/Complex/RealDeriv.lean`: complex-exponential
  differentiation for a real time parameter.
- `Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean` and
  `Mathlib/Analysis/Calculus/SmoothSeries.lean`: alternate local uniform
  derivative-limit APIs, whose hypotheses must be established for the
  particular evolving coefficient family.

Mathlib's AddCircle Fourier basis and inversion APIs exist, but the present
coefficient-first construction only needs absolutely convergent synthesis.
An extension starting from an arbitrary physical-space function would need
an additional theorem relating that function to the prescribed coefficients.
