# NDEA periodic Cayley–Crank–Nicolson formalization

This repository records a Lean 4.31 formalization milestone for a classical
convergence analysis of a periodic one-dimensional centered-space
Cayley–Crank–Nicolson discretization of the linear Schrödinger equation.

Three scope statements are essential:

- The numerical theorem is classical.
- The contribution is the audited Lean 4 formalization.
- Any “first” claim remains preliminary and unchecked.

## Verified chain

The development connects:

1. the periodic centered finite-difference Laplacian;
2. Cayley-factor invertibility and unitarity;
3. arbitrary finite-step weighted-norm stability;
4. explicit spatial and temporal Taylor remainder estimates;
5. a fixed-time `O(k² + h²)` weighted-error estimate; and
6. a grid-family convergence theorem.

The headline bound is

```text
error(N) ≤ initial_error
  + T * (sqrt(L) * (5*Mt/12) * k² + sqrt(L) * (Ms/12) * h²).
```

## Headline declarations

- `PeriodicCayleyCNAnalyticClosureV1.periodic_cayley_cn_convergence_of_smooth_solution`
- `PeriodicCayleyCNConstantModeExampleV1.constantMode_fixed_time_weighted_error_eq_zero`
- `PeriodicCayleyCNGridFamilyConvergenceV1.asymptoticErrorBound_tendsto_zero`
- `PeriodicCayleyCNGridFamilyConvergenceV1.error_tendsto_zero_of_explicit_bound`
- `PeriodicCayleyCNGridFamilyConvergenceV1.exact_initialization_error_tendsto_zero`

## Reproduce the build

Install `elan`, then run from the repository root:

```bash
elan toolchain install leanprover/lean4:v4.31.0
elan default leanprover/lean4:v4.31.0
lake update
lake build NDEAMathlibGate.PeriodicCayleyCNAnalyticClosureV1
lake build NDEAMathlibGate.PeriodicCayleyCNConstantModeExampleV1
lake build NDEAMathlibGate.PeriodicCayleyCNGridFamilyConvergenceV1
```

Direct source checks:

```bash
lake env lean NDEAMathlibGate/PeriodicCayleyCNAnalyticClosureV1.lean
lake env lean NDEAMathlibGate/PeriodicCayleyCNConstantModeExampleV1.lean
lake env lean NDEAMathlibGate/PeriodicCayleyCNGridFamilyConvergenceV1.lean
```

The toolchain and dependency revisions are pinned by `lean-toolchain` and
`lake-manifest.json`.

## Trust and audit status

The headline declarations compile without `sorry`, `admit`, custom `axiom`, or
`native_decide`. Their recorded axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Compilation establishes kernel acceptance; it does not by itself establish
that the formal statement perfectly captures the intended mathematics. The
paper therefore states the assumptions and constants explicitly. Independent
human mathematical and formalization review remains desirable.

Audit records are under [`audit/`](audit/). The technical note and its LaTeX
source are under [`paper/`](paper/).

## Repository contents

- `NDEAMathlibGate/`: exact transitive Lean source closure required by the
  three headline modules (53 source files).
- `paper/`: posting-ready milestone paper and LaTeX source.
- `audit/`: build, axiom, and PDF-validation records.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: pinned build setup.

## License

The project is released under the Apache License 2.0. See [`LICENSE`](LICENSE).

