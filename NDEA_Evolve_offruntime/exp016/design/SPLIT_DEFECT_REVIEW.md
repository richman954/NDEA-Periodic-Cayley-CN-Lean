# SplitDefect source review

Independent read-only mathematical review of `lean/SplitDefect.lean` at
2026-09-09T04:19:01Z. The reviewer did not author or modify this module and
did not launch a compiler.

Reviewed source SHA256:
`affc2fcff250486f163d11cc3822014f7affadaaf7e0de5cd51baa52a3519b96`.

**Assessment: no source-level mathematical blocker found.** This is not a
Lean acceptance receipt. When inspected, the current rerun receipt
`evidence/20260909T041739.854114Z_SplitDefect.json` contained its start metadata
and the matching source hash but no final exit status.

## Identity and actual recurrence

- `stageResidual_eq_gridFactorResidual` preserves the saved denominator
  residual exactly: `(I+i*a*A)v - (I-i*a*A)u` expands to
  `v-u+i*a*A(v+u)`. There is no missing denominator, time-step factor or norm
  scaling. This bridge requires no Hermitian assumption.
- `ordered_stage_midpoint_defect` correctly states the **scaled** identity
  `i*(u3-u0)-k*(A+B)*m = i*(r1+r2+r3)+k*(A/2+B)*eta`, where
  `m=(u0+u3)/2` and `eta=(u1+u2-u0-u3)/2`. Coefficients and signs agree with
  direct expansion. Linearity suffices; neither commutativity nor
  selfadjointness is assumed. Since there is no division by `k`, the theorem
  validly permits every real `k`, including zero and negative values.
- `stageResidual_actual_cayley_zero` uses the saved Hermitian-matrix theorem
  for the actual `step`; Hermitian matrices ensure the denominator is
  invertible for every real stage parameter. There is no assumed solve-error
  premise replacing this concrete connection.
- `actual_symmetric_midpoint_defect` instantiates precisely the successive
  stages `A(k/4)`, `B(k/2)`, `A(k/4)` and eliminates their actual solve
  residuals. The surviving `k*(A/2+B)*eta` correctly retains the splitting
  defect. The nested applications have the same order as the saved
  rightmost-first `symmetric` definition. No `A*B=B*A` reduction occurs.

The file has three definitions and four theorem declarations. Its scope is
exact algebra plus an actual finite-matrix Cayley consumer. It does not yet
prove a defect bound, the stage-geometry identity, a named spinor-grid
specialization, reconstruction regularity or continuum convergence. Those
remaining steps are consistent with the recorded Exp016 plan. Dividing this
identity to define a velocity or unscaled defect will require `k != 0`;
positive slab duration is a later analytic hypothesis.

## Observed compiler evidence

The preserved first attempt has source SHA256
`aa962539dbf21f2973a9f7c80420044303d14c1d3561aa6d12f154a531f9d70e`.
Its receipt `evidence/20260909T040959.454479Z_SplitDefect.json` records exit 1,
336.024 seconds, and unchanged source. The full log reports one remaining
scalar equality containing `Complex.I ^ 2`, plus five deprecation warnings
for continuous-linear-map application names. The revised proof explicitly
normalizes `Complex.I_sq`; this addresses the displayed mathematical goal,
but successful elaboration must be established by the current rerun's receipt.

## Recommended next exact control

Use `Fin 1` matrices `A=1`, `B=0`, `k=4`, and the vector with coordinate 1.
The actual stages are

```text
u0 = 1,  u1 = -i,  u2 = -i,  u3 = -1.
r1 = r2 = r3 = 0,
m = 0,  eta = -i,
i*(u3-u0)-4*(A+B)*m = -2*i != 0.
```

The unscaled midpoint defect is `-i/2`. This is a nonzero, concretely
calculated defect with exact solves and commuting operators; it rules out
accidentally identifying the split step with unsplit CN. As an optional
stronger value check, the unsplit step with parameter `k/2=2` sends 1 to
`(-3-4*i)/5`, which differs from the split endpoint `-1`.

Prove the three explicit denominator equations and use the saved
`SpinorGrid.stage_unique` theorem to identify these vectors with actual
Cayley stages. That route avoids unnecessary nonsingular-inverse reduction.
This scalar control does not replace a later legacy noncommuting spinor-grid
consumer or the planned sampled variable-potential instance.
