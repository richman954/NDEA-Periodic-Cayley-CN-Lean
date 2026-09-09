# Experiment 005 — mesh-weighted symmetric-stage residual bridge

This campaign connects the verified symmetric Cayley method to the kind of
weighted residual estimates used in periodic-grid analysis. Its convergence
result is conditional: common mesh-uniform residual constants are explicit
hypotheses, not established smooth-PDE consistency results.

The frozen scope is in [PLAN.md](PLAN.md); the argument and exclusions are in
[MATHEMATICAL_DERIVATION.md](MATHEMATICAL_DERIVATION.md). The read-only relation
to the older single-CN framework is in
[LEGACY_FRAMEWORK_CONTEXT.md](LEGACY_FRAMEWORK_CONTEXT.md).

| New production module | Responsibility |
| --- | --- |
| `MeshWeightedStability.lean` | Weighted stability, measured trajectory defects, accumulation, conditional fixed-time certificate, pointwise-to-weighted conversion |
| `SymmetricStageResidual.lean` | Actual implicit-factor residuals, exact ordered transfer, constant-one weighted bound, three-stage accumulation |
| `MeshFamilyConvergence.lean` | Scalar error convergence across varying finite dimensions under common residual constants and vanishing mesh/time steps |

Principal endpoints are
`symmetric_stage_residual_identity`,
`symmetric_stage_residual_fixed_time_error`, and
`symmetric_stage_mesh_family_error_tendsto_zero` in namespace
`NDEAEvolve.Exp005`. Each physical mesh has positive spacing. Time horizons
satisfy N_q*k_q≤T; the general family endpoint does not silently assume that
all terminal times equal T or tend to it.

The fixed-time certificate is

`weighted_error_N ≤ weighted_error_0 + T*(Ct*k² + Cx*dx²)`,

provided k≥0, Ct,Cx≥0, N*k≤T, and the sum of the three measured weighted
factor residuals at every j<N is at most `k*(Ct*k² + Cx*dx²)`.
There is no small-step condition or bound on generator norms in this
certificate. Deriving that residual premise for sampled smooth split-PDE
solutions remains the next mathematical task.

The controls prove exact witnesses for missing assumptions or terms, rather
than using numerical sampling. Source and evidence live only in this new
campaign's directories. Assurance commands are documented under
[assurance/README.md](assurance/README.md); separate status snapshots record
progress without altering historical manifests. Consult the final evaluation
report and delivery receipt for the final qualification status; draft proof
source alone is not evidence of compilation.
