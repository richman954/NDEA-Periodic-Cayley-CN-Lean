# Experiment 006 — concrete periodic PDE residual closure

This campaign derives Experiment 005's actual three-stage residual estimate
for a nonconstant periodic Schrödinger mode, with constants independent of
mesh dimension and generator norm. It then supplies that derived estimate
to the existing fixed-time and varying-mesh convergence argument.

The concrete solution is `U(t,x)=exp(i*(x-2*t))`, on period `2*pi`, satisfying
`i*U_t=-2*U_xx`. Both split generators are `-d_xx`; both act nontrivially.
The discrete generator is the genuine centered periodic negative Laplacian,
including its corner entries and proved endpoint wrapping.

For `d*h=2*pi`, `0<h<=1`, `0<=k<=2`, the checked target is

```
stageResidualBudget <= k*(Ct*k^2 + Cs*h^2)
Ct = (5/16)*sqrt(2*pi)
Cs = (1/4)*sqrt(2*pi)
```

Consequently, for `N*k<=T`,

```
weighted_error_N <= weighted_error_0 + T*(Ct*k^2 + Cs*h^2).
```

The mesh-family endpoint proves that the scalar weighted error tends to zero
when `h`, `k`, and the initial weighted error tend to zero. It does not
identify varying discrete state spaces or assert interpolation convergence.

| Source | Checked responsibility |
| --- | --- |
| `lean/PeriodicGrid.lean` | Hermitian cyclic matrix and both endpoint wraps |
| `lean/PeriodicModeResidual.lean` | Nonzero/nonconstant periodic PDE, exact stencil symbol, spatial and temporal estimates |
| `lean/Exp005ModeBridge.lean` | Actual Exp005 factor residuals, budget, fixed-time error, varying-mesh limit |
| `lean/Controls.lean` | Six exact controls, including an admissible grid and a strictly present spatial error |
| `lean/Exp005Foundation.lean` | Reproduced frozen predecessor proof chain |
| `lean/CombinedVerification.lean` | Fresh combined check without project-module imports |

The mathematical scope is one nonzero Fourier mode and a commuting split.
This does not settle noncommuting generators, variable potentials, arbitrary
smooth data, or sharp constants. The spatial term is derived and is nonzero
on every nonzero mesh. No residual-budget hypothesis is assumed by the
concrete budget, fixed-time, or mesh-family endpoints.

See `MATHEMATICAL_DERIVATION.md` for the argument and explicit restrictions.
Consult `evidence/FINAL_VERIFICATION.json` and `STATUS_FINAL_LOCAL_GREEN.md` for the
qualification verdict; drafting source or passing numerical checks alone is
not proof verification. `numerical_checks.py` and its JSON are supporting
floating-point diagnostics only.

The local scripts pin Lean 4.31.0 (binary SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`) and Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. `verify_final.py` reproduces the
frozen foundation, checks the source policy, constructs the combined source,
checks it with only external dependency namespaces on its import path, and
requires an exact audit of all 41 new theorem/control names with only
`propext`, `Classical.choice`, and `Quot.sound` allowed. The source is portable;
the local runner paths identify this workstation's existing cache.
