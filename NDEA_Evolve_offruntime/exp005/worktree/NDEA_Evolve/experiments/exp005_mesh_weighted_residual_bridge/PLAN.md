# Experiment 005 — mesh-weighted symmetric-stage residual bridge

## Authorization and immutable predecessor

After verified Experiment 004 closure, the user asked “now what, and the
proceed forward”. This campaign makes the next narrow PDE-facing connection:
stability and conditional consistency transfer for the actual symmetric
scheme. It does not reopen the completed releases or infer a new four-hour
budget from the earlier Step 4 authorization.

Predecessor: `956ce8acac594c45cf576b66972a082c89190bf8`, tag
`exp004-symmetric-cayley-second-order-verified-final-20260907`.
Development uses a separate clone of its release bundle at
`NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve`, branch
`exp005-mesh-weighted-residual-bridge`. Preserve all 806 tracked predecessor
files, historical manifests, release files, and original worktrees.

## Frozen specification

Use the existing complex Euclidean spaces `E n`, matrix-to-continuous-linear-
map representation, and

`S = Chat A (k/4) * Chat B (k/2) * Chat A (k/4)`.

For Hermitian matrices A and B, all finite dimensions (including zero), and
real k, define the mesh-weighted quantity
`weightedNorm dx x = Real.sqrt dx * ‖x‖`. Physical mesh-family statements
require positive dx. Algebraic stability statements may be more general;
zero dx is explicitly not a genuine norm on a nonzero state space.

1. Prove unconditional weighted norm and distance preservation by S, and
   all-N error accumulation for an actual numerical recurrence against an
   arbitrary reference trajectory. Define its local defect as
   `u(j+1) - S (u j)`; do not replace this by a free unconnected variable.
2. Let D, N, R be the Cayley denominator, numerator, and inverse denominator.
   For arbitrary states v, z1, z2, w, define the actual factor residuals
   `r1 = D_A z1 - N_A v`, `r2 = D_B z2 - N_B z1`,
   `r3 = D_A w - N_A z2`, using the same quarter/half parameters as S.
   Prove the exact ordered identity
   `w - S v = C_A (C_B (R_A r1)) + C_A (R_B r2) + R_A r3`.
   Unitarity and resolvent contraction must then give
   `weightedNorm dx (w-S v) ≤ weightedNorm dx r1 + weightedNorm dx r2
     + weightedNorm dx r3`, with no spectral or small-step restriction.
3. Accumulate these three-stage residuals. Under k≥0, Ct,Cx≥0, N*k≤T,
   and the explicit local hypothesis
   `sum_stage_residuals(j) ≤ k * (Ct*k² + Cx*dx²)` for j<N,
   prove `error(N) ≤ error(0) + T*(Ct*k² + Cx*dx²)`.
4. For families with possibly varying finite dimensions, positive spacings,
   k≥0, uniformly bounded physical horizons, common Ct and Cx, and the
   preceding residual assumption, prove the scalar weighted error tends to
   zero when k→0, dx→0, and the initial weighted error→0. State both a
   direct-defect and a stage-residual version if useful.
5. Prove a dimension-free pointwise-to-weighted bound: if dx≥0, L≥0,
   n*dx=L, R≥0, and each coordinate has norm≤R, its weighted norm≤sqrt(L)*R.

The new convergence statement is explicitly conditional on mesh-uniform
residual estimates. It is not the derivation of those estimates from a
general split PDE, not convergence of interpolants in a common function
space, and not a proof of PDE existence, uniqueness, or continuum convergence.

## Relation to the legacy periodic-grid work

The legacy `FiniteStateEuclideanNormBridgeV1` uses the identical formula
sqrt(dx) times the complex Euclidean norm. Its single unsplit Cayley/CN
consistency theorem is not a consistency theorem for this symmetric method.
In particular, A=0,B=H reduces S to the old single CN step; A=H,B=0 gives
two half-A Cayley steps and generally does not equal that single CN step.
This campaign uses the maintained Exp002–004 proof chain, not the broad
historical PDE import stack. Formula compatibility is not described as a
formal import bridge to that separate project.

## Controls and assurance

Retain compiled positive witnesses for zero dimension/count/weight,
stability without consistency, omitted time-step scaling in residual
accumulation, and omission of a stage residual. Include the single-CN versus
two-half-Cayley distinction if supported by a small exact witness. Controls
must refute actual false claims, not merely exhibit a loose upper bound.

Use pinned local Lean 4.31.0 and Mathlib, one serial worker, the shared
`/tmp/exp003_lean_one_job.lock`, and bounded 900-second command timeouts.
Use a separate ordinary temporary-filesystem cache `/tmp/exp005_build`.
Development may copy the ten verified predecessor project artifacts after
source/artifact receipt validation; this is not final fresh verification.
Final qualification requires rebuilding the entire project proof chain and
a combined-source run with no project artifact imports. Preserve import-only
shadow provenance for the first two predecessors. Do not modify pins or run
a root-project Lake build.

No `sorry`, `admit`, custom axioms, `unsafe`, or `native_decide`. Audit all
public production/control theorems against propext, Classical.choice, and
Quot.sound only. Preserve commands, source/output hashes, logs and receipts,
including failures. Use separate historical status snapshots and a final
frozen manifest. Package a source archive and Git bundle with fresh recovery
checks; no remote publication. Stop at verified closure of this bounded
conditional bridge, leaving smooth split-PDE residual derivation as later work.
