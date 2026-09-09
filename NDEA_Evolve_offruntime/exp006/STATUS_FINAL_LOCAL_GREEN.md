# Experiment 006 — local final verification passed

Date: 2026-09-08. The bounded concrete-mode milestone is complete locally.

Experiment 005's formerly assumed residual budget has been derived for the
nonzero, nonconstant periodic solution `U(t,x)=exp(i*(x-2*t))` of
`i*U_t=-2*U_xx`, split as two copies of `-d_xx`. The discrete operators are
actual Hermitian cyclic centered Laplacian matrices. Both periodic endpoint
wraps and the actual Exp005 denominator/numerator residual identity are proved.

For a `d`-point grid with `d*h=2*pi`, `0<h<=1`, and `0<=k<=2`,

```
stageResidualBudget <= k*(Ct*k^2+Cs*h^2)
Ct=(5/16)*sqrt(2*pi), Cs=(1/4)*sqrt(2*pi).
```

The concrete fixed-time theorem gives
`weighted_error_N <= weighted_error_0 + T*(Ct*k^2+Cs*h^2)` for `N*k<=T`.
The varying-mesh theorem proves scalar weighted error tends to zero if
mesh, time step, and initial weighted error tend to zero under a common
horizon. None of these concrete endpoints assumes a residual-budget bound.
The restrictions on `h` and `k` do not involve the growing matrix norm.

Qualification:

- All four new source modules (three production modules and controls) passed
  their local modular Lean checks. Their hashes remain unchanged.
- A fresh combined source rechecked the frozen predecessor chain and all new
  proofs, with every project artifact excluded from its import path.
- Exactly **41 of 41** expected theorem audits passed: **35 production
  theorems and 6 exact controls**. Every audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`; no added axiom or placeholder is used.
- The combined invocation returned exit zero in **161.608 seconds**.
- The verifier reproduced the foundation from the frozen Exp005 source,
  checked the compiler/Mathlib pins and tracked Mathlib cleanliness, enforced
  its source policy, and checked source hashes before and after compilation.

Principal evidence:

- `evidence/FINAL_VERIFICATION.json`
- `evidence/20260908T051657.735387Z_CombinedVerification.json`
- `evidence/20260908T051657.735387Z_CombinedVerification.log`
- `evidence/MODULAR_GREEN_SNAPSHOT.json`
- `evidence/EXPECTED_FINAL_THEOREMS.json`

The stable combined source SHA-256 is
`af3d14716b492f6485dd1bcf88c3c99cd13440a219f89b27b5258531d7f96c52`.

Independent mathematical review checked the constants and caught the need
for exact periodic wrap. Independent floating-point diagnostics also passed
147 stage-budget cases and 49 global-trajectory cases and detected wrong-sign
and omitted-spatial-term controls. Numerical diagnostics are supporting
checks, not proof evidence.

The scope is a single first Fourier mode, fixed period `2*pi`, and a commuting
split with two active equal generators. General smooth data, noncommuting
operators, variable potentials, interpolation convergence, and sharp constants
are not claimed. The six exact controls include an admissible eight-point
grid, nonconstancy/nonzero state, two active continuous generators, and a
strictly present spatial error.

A separate independent Colab combined check of this exact source is owned by
the root task and was still running when this local status was written.
Its eventual result belongs to the separate remote report. Exp005 remained
frozen; this campaign's writes are confined to the new Exp006 directory.
