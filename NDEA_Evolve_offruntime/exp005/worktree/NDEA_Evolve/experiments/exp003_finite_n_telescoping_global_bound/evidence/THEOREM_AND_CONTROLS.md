# Verified theorems and controls

The modular log emits the arbitrary-ring identity:

```text
@NDEAEvolve.Exp003.pow_sub_pow_telescoping :
  ∀ {R₀ : Type} [Ring R₀] (S U : R₀) (N : ℕ),
    S^N - U^N =
      ∑ k ∈ Finset.range N, S^(N-1-k) * (S-U) * U^k
```

Its Cayley specialization is
`cayley_split_unsplit_telescoping`, with
`S = splitStepHat A B alpha = Chat A alpha * Chat B alpha` and
`U = unsplitStepHat A B alpha = Chat (A+B) alpha`.

The public fan estimate and final theorem are:

```text
@NDEAEvolve.Exp003.unitary_pow_sub_pow_opNorm_le :
  S ∈ unitary (E n →L[ℂ] E n) →
  U ∈ unitary (E n →L[ℂ] E n) →
  ‖S^N-U^N‖ ≤ (N : ℝ) * ‖S-U‖

@NDEAEvolve.Exp003.cayley_split_unsplit_global_opNorm_le :
  Matrix.IsHermitian A → Matrix.IsHermitian B →
  ‖splitStepHat A B alpha ^ N - unsplitStepHat A B alpha ^ N‖ ≤
    (N : ℝ) * 4 * alpha^2 * ‖operatorOf A‖ * ‖operatorOf B‖
```

Every displayed norm is the induced norm on
`E n →L[ℂ] E n`, where `E n = EuclideanSpace ℂ (Fin n)`.

For the algebra, the proof defines `f k = S^(N-k)U^k`, rewrites every summand
as `f k - f(k+1)`, and applies `Finset.sum_range_sub'`. This is valid in a
noncommutative ring and reduces `N=0` to the empty sum.

For the norm, Exp002 Cayley unitarity is transported through
`Matrix.toEuclideanCLM`. Each term satisfies the exact equality

`‖S^p * (S-U) * U^q‖ = ‖S-U‖`

by `CStarRing.norm_mem_unitary_mul` and
`CStarRing.norm_mul_mem_unitary`. The triangle inequality sums `N` identical
bounds, and Step 3's `cayley_split_unsplit_defect_opNorm_le` supplies the local
coefficient.

Compiled controls:

- `nonunitary_blowup_counterexample`: on `E 1`, take `S=2I`, `U=I`, `N=2`.
  Both norms are at most two, `‖S-U‖=1`, but
  `‖S^2-U^2‖=3 > 2=N‖S-U‖`.
- `linear_bound_implies_n_squared_bound`: for `N>=1` and nonnegative local
  error, every `x<=N*local` entails `x<=N^2*local`.
- `n_squared_strict_slack_witness`: on `E 1`, take `S=(9/10)I`, `U=I`,
  `N=2`. The local error is `1/10`, the global error is `19/100`, and
  `19/100 < 2/5 = N^2‖S-U‖`.
