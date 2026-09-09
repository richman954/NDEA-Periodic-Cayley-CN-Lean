# Experiment 005 final evaluation

Proof verification: PASSED — conditional mesh-weighted residual bridge.
Preservation/source assurance: PASSED. Packaging metadata is recorded separately.

## Verified result

The new theorem chain concerns the actual symmetric update
`S = Chat A(k/4) * Chat B(k/2) * Chat A(k/4)` on finite complex Euclidean
spaces. Hermiticity gives unconditional preservation of the mesh-weighted
quantity sqrt(dx)‖x‖. An exact ordered identity transfers the three measured
implicit-factor residuals to the full-step discrepancy, with a weighted bound
of one times their norm sum. This requires neither a spectral step restriction
nor a generator-norm bound.

For nonnegative k,Ct,Cx, a common horizon N*k≤T, and the explicit measured
per-step residual premise `budget_j≤k*(Ct*k²+Cx*dx²)`, the fixed-time certificate
is `error_N≤error_0+T*(Ct*k²+Cx*dx²)`. A separate theorem proves scalar weighted
error convergence for varying finite dimensions when the constants are common,
positive spacings and nonnegative time steps tend to zero, and initial weighted
errors tend to zero. The family theorem permits any terminal times within the
common horizon; it does not silently identify them with T.

Principal declarations, in namespace `NDEAEvolve.Exp005`, are:

- `symmetric_stage_residual_identity`
- `symmetric_stage_residual_fixed_time_error`
- `symmetric_stage_mesh_family_error_tendsto_zero`

The supporting pointwise-to-weighted estimate has constant sqrt(L), under
n*dx=L, rather than an unexplained dimension-dependent constant.

## Assurance status

Final qualifying modular run: `20260908T015810.199511Z_2`, all 14 serial Lean
invocations passed, from an explicitly empty active project cache.
Combined-source run: `20260908T015403.848677Z_2`, 2,623 lines, exit 0 in
189.861789 seconds. This route ran before the final modular rebuild and
imported no project artifacts.

All 40 public theorem audits (29 production + 11 controls) show only
propext, Classical.choice, and Quot.sound. No prohibited proof mechanism
appears in the final new Lean source. Two failed development control
conversion attempts remain attributable in the evidence and are excluded
from qualification; the final repair passed both verification routes.

The staged source/evidence audit passed with no errors, confirming all 806
tracked predecessor files unchanged, import-only shadow correspondence, the
clean pinned environment, and the final receipt/source/log matches. The
candidate audit is retained separately; the final audit and selected manifest
are `evidence/FINAL_ASSURANCE_AUDIT.json` and
`evidence/SELECTED_EVIDENCE_SHA256SUMS`. The final full manifest is frozen
after the report and all intended deliverables are staged. The
off-tree `DELIVERY_RECEIPT.json` records the actual final commit/tag, archive
and bundle hashes, and completed fresh recovery results without circular
checksum dependencies.

Development uses a separate ordinary `/tmp/exp005_build` cache. Its initial
ten predecessor project artifacts were copied only after comparison with
Exp004's final serial source/output receipts. Compatible dependency artifacts
were independently hash-compared with the pinned package cache. This bootstrap
is development evidence, not a fresh proof-chain build. Final qualification
requires retiring the active project artifacts, rebuilding the entire serial
chain, and separately checking the combined source without project imports.

## Controls and limits

Compiled controls cover empty dimension and count, zero and negative
steps, zero weight hiding a nonzero state, stable evolution failing to track
an inconsistent drifting reference, missing per-step time scaling, omission
of the middle-stage residual, and the distinction between two half Cayley
steps and one full Cayley step. They are exact mathematical witnesses, not
numerical samples or failures to parse a statement.

This is a conditional consistency-transfer theorem, not a general smooth-PDE
consistency result or full spatial-continuum convergence proof. The required
uniform stage residual estimate remains a visible premise. The older single
CN theorem has not been attached to a different symmetric scheme. No PDE
well-posedness, interpolation convergence, unbounded-operator theorem, or
uniform bound on the Exp004 generator-norm constants is claimed.

All predecessor production sources and historical evidence remain immutable.
No remote publication or independent external artifact review is claimed.
