# Existing numerical APIs for the Exp016 design

Read-only audit, 2026-09-09. This report reads Exp008–012 and their retained numerical foundation, plus the proposed Exp016 `PLAN.md` and the accepted Exp015 residual interface. No Lean compilation, proof rerun, or sealed-source edit was performed. Statements below describe existing source; proposed bridges are explicitly identified as new work. Parent owns baseline receipts and recovery checkpoints.

The existing chain already has an end-to-end theorem for its particular constant-potential, two-component problem. Exp016 extends the numerical-to-continuum interface to variable potential. Its current plan does not establish spatial refinement or broader PDE convergence.

All paths below are relative to `/home/richman954/NDEA_Evolve_offruntime`. Namespace prefixes are given explicitly where otherwise ambiguous. Earlier generic results are also retained verbatim inside `exp008/lean/Exp007Foundation.lean`; their original module paths are included to make reuse reviewable.

## Exact scheme and conventions

`exp007/lean/SpinorGrid.lean:14–21`, namespace `NDEAEvolve.Exp007.SpinorGrid`, defines, for an arbitrary finite index type `ι`:

```text
Vec ι = EuclideanSpace ℂ ι
op G = Matrix.toEuclideanCLM G
D_G(a) = I + iaG             -- den
N_G(a) = I - iaG             -- num
R_G(a) = D_G(a)⁻¹            -- resolvent
C_G(a) = op (N_G(a) R_G(a))  -- step / cayleyMatrix
```

`Grid n = Fin (n+1) × Fin 2` (`SpinorGrid.lean:112`). There are **n+1 spatial nodes**, each with fiber `E 2 = EuclideanSpace ℂ (Fin 2)`. The full norm is the Euclidean norm over both indices; the mesh norm is `sqrt(h) * ‖y‖`. This differs from the unweighted norm and from a maximum over nodes.

`exp006/lean/PeriodicGrid.lean:16–42` defines cyclic `next` and `prev` with `finRotate`, samples at `x_j = j*h`, and uses the negative centered second difference

```text
L_h = h⁻² (2I - P - P*)
(L_h y)_j = (2y_j - y_next(j) - y_prev(j))/h².
```

`sample_next`, `sample_prev`, and `matrix_sample_stencil` (`PeriodicGrid.lean:52,68,97`) use a periodic scalar field of period `L` and the exact relation `(n+1)*h=L`. The matrix is Hermitian even at the totalized Lean expression `h=0`; physical mesh arguments must separately require `h>0`.

`SpinorGrid.potential n K = I ⊗ K` and `hamiltonian n h K = L_h ⊗ I + I ⊗ K` (`SpinorGrid.lean:170–181`). The saved actual scheme is

```text
A_h = L_h ⊗ I + I ⊗ Z
B_h = I ⊗ X
S_h(k) = C_A(k/4) C_B(k/2) C_A(k/4).
```

This is `SpinorGrid.symmetric n h k Z X` (`SpinorGrid.lean:270`); multiplication is composition and the **rightmost factor acts first**. A Cayley parameter `a` corresponds to physical time `2a`; the factors are half/full/half steps. The continuum generator is `-∂xx + Z + X`. The matrices `Z` and `X` do not commute. A full three-factor step is not an unsplit CN step for `A+B`, even when its factors commute: Cayley transformations do not have an exact semigroup law.

The proposed Exp016 split `A_h=L_h⊗I+I⊗Z`, `B_h=diag_j(V(x_j)-Z)` preserves this legacy definition when `V=Z+X`. Defining the sampled block diagonal operator, proving its Hermiticity, and proving that specialization identity are new bridges. Existing `potential n K` does not encode variable spatial coefficients.

## Reuse classification

| Existing API | Classification for the proposed variable-potential endpoint | Exact limitation or required bridge |
|---|---|---|
| `SpinorGrid.den_isUnit`, `den_mul_resolvent`, `resolvent_mul_den`, `den_step`, `stage_unique`, `step_mem_unitary` | Reusable as-is | Arbitrary finite `ι`, real stage parameter, Hermitian full-grid matrix. New sampled potential must supply Hermiticity. |
| `SpinorGrid.symmetric_mem_unitary`, `symmetric_pow_norm` | Needs a small bridge | Stated for the saved constant-block split. Compose the generic `step_mem_unitary` results for the new full-grid A/B; no new stability estimate is needed. |
| `Exp005` weighted norms, exact factor residuals and ordered accumulation | Needs an index/interface bridge | Generic in `Mat n`, hence `Fin n`. Existing full grid uses `Fin(n+1) × Fin 2`; reindex isometrically or generalize the proved argument to finite `ι`. Fixed A/B and k in the existing trajectory theorem; variable steps need an accumulation extension. |
| `PeriodicGrid` geometry and stencil identities | Reusable as-is on scalar components | Fiber assembly and the new sampled potential remain explicit. |
| `Exp010.sampleSolution`; `Exp011.nodeValue` and its sample identity | Reusable as-is for the selected C² grid | They accept arbitrary fields/grid data, despite later orbit-specific consumers. General Hilbert fibers would need a different grid representation. |
| `Exp008.FourierGrid` discrete orthogonality and Parseval | Reusable as-is for band coefficients on the selected grid | Full DFT inversion for arbitrary grid data and continuum integral Parseval are new statements. |
| `Exp008` invariant-mode evolution and its finite/infinite Fourier error closures | Unsuitable unchanged for variable V | Multiplication by a nonconstant V couples Fourier modes. The required mode-intertwining hypotheses are no longer available. |
| `Exp008.modeSymbol_consistency` | Reusable as a scalar symbol bound | Converting it into an estimate for the actual reconstructed variable-potential trajectory needs aliasing, regularity and multiplication/commutator estimates. |
| `Exp004.symmetric_cayley_exp_local_opNorm_le` | Reusable algebraically after reindexing; insufficient for spatial refinement | Constants depend cubically on full generator norms. Laplacian norms grow with refinement. |
| `Exp009` absolute/weighted Fourier tail estimates | Needs a type or data bridge where used | Existing statements concern C² coefficient sequences; the tail algebra is independent of evolution, but preservation and sampling estimates for variable V are new. |
| `Exp011.reconstruction` | Unsuitable unchanged as an Exp015 approximate field | Clamped piecewise constant in space and time; generally discontinuous and lacks the required actual derivatives. |
| `Exp012` uniqueness and reconstructed convergence | Accepted narrow endpoint and useful regression target | Its classical predicate and numerical solution concern constant `Z+X`, not Exp014's variable potential. |
| `Exp015.residual_error_uniform_budget` | Reusable as-is after proving the new reconstruction facts | Requires actual regular periodic field, actual derivative residual, continuity, selfadjoint V, positive period, and a derived interval budget. |

## Strongest reusable algebra and stability statements

`SpinorGrid.stage_unique` (`exp007/lean/SpinorGrid.lean:68`) states, for Hermitian `G`,

```text
op (den a G) target = op (num a G) source
  ↔ target = step a G source.
```

`step_mem_unitary` (`:150`) has no step-size or mesh restriction. `symmetric_pow_norm` (`:282`) proves norm preservation for every natural power of the saved split. Stability restrictions must not be inferred from consistency hypotheses elsewhere.

The exact stage residual is `D target - N source`: `Exp007.gridFactorResidual` (`exp007/lean/StageBridge.lean:10`) is generic in finite `ι`. It has **no implicit division by k**. The older `Exp005.factorResidual` uses exactly that convention on `Fin n`.

Original module: `exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/SymmetricStageResidual.lean`; retained at `exp008/lean/Exp007Foundation.lean:2107–2308`.

- `resolvent_factorResidual` (`SymmetricStageResidual.lean:64`): `R r = target - C source`.
- `factorResidual_recurrence` (`:79`): `target = C source + R r`.
- `symmetric_stage_residual_identity` (`:103`): for stage data `y0,y1,y2,y3` and residuals `r1,r2,r3` at `k/4,k/2,k/4`,

  ```text
  y3 - C_A C_B C_A y0
    = C_A (C_B (R_A r1)) + C_A (R_B r2) + R_A r3.
  ```

- `resolvent_weightedNorm_le` (`:141`) and `cayley_weightedNorm_preserved` (`:135`) give coefficient 1 for the residual norm propagation.
- `symmetric_stage_residual_weighted_le` (`:150`) bounds the full-step discrepancy by the sum of the three mesh-weighted residual norms, without commutation, norm, or step-size restrictions.
- `symmetric_stage_residual_accumulation` (`:183`) retains initial error and adds those actual stage budgets over `j<N`; N=0 is included.
- `symmetric_stage_residual_fixed_time_error` (`:204`) concludes initial error plus `T*(Ct*k²+Cs*dx²)` **if** every actual stage budget is bounded by `k*(Ct*k²+Cs*dx²)` and `N*k≤T`, with nonnegative k/Ct/Cs. This is a conditional convergence interface, not a derived PDE consistency result.

The simpler full-step interface is `Exp005.trajectoryDefect A B k u j = u(j+1)-S(k)(u j)` and `symmetric_weighted_error_accumulation`, in `MeshWeightedStability.lean:98,110` under the same original directory (retained foundation `:1971,1983`). Its bound is initial error plus the sum of measured full-step defects. `symmetric_weighted_fixed_time_error` (`:152`) again requires the defect rate as a premise.

These identities are useful for algebra and inexact solves. They do not identify a spatial reconstruction or its continuum residual.

## What the existing consistency and convergence claims actually assume

`Exp008.modeSymbol m h = (2-2*cos(m*h))/h²`. In `exp008/lean/FrequencyBounds.lean`:

- `modeSymbol_consistency` (`:36`) proves `|modeSymbol m h-m²| ≤ m⁴*h²/8`, assuming `h>0` and `|m|*h≤1`; zero and negative frequencies are included.
- `Ct M = 1000*(M²+2)^3`, `Cs M=M⁴/8` (`:11–12`).
- `frequency_local_error` (`:87`) proves an operator error at most `k*(Ct M*k²+Cs M*h²)` against the exact mode flow. Assumptions: `M≥1`, `|m|≤M`, `h>0`, `M*h≤1`, `k≥0`, and `2*k*(M²+2)≤1`.
- `frequency_power_error` (`:131`) gives `T*(Ct M*k²+Cs M*h²)` if `N*k≤T`.
- `frequency_stageResidualBudget_bound` (`:164`) bounds an actual three-stage budget by `sqrt(dx)*(9/8)*k*(Ct M*k²+Cs M*h²)*‖v‖`. The first two stages are actual solves and the final target is the exact mode flow. The `9/8` comes from an explicit denominator norm estimate, not an unconditional stability loss.

`Exp004.symmetric_cayley_exp_local_opNorm_le` (retained foundation `:1644`) is the generic source of temporal order:

```text
‖S(k) - exp(-ik(A+B))‖ ≤ 1000*|k|³*(‖A‖+‖B‖)³,
provided 2*|k|*(‖A‖+‖B‖) ≤ 1.
```

The norm here is the induced continuous-linear-map norm. A full-grid application to arbitrary Hermitian variable-potential matrices is valid after the index bridge, but the coarse Laplacian scaling produces an O(h⁻⁶) cubic factor. This is not a mesh-uniform PDE estimate.

`Exp008.finite_superposition_grid_error` in `SuperpositionClosure.lean` additionally assumes exact period relation `(n+1)*h=2π`, support in `[-M,M]`, and **`2*M<n+1`**. It gives

```text
grid error ≤ initial error
  + sqrt(2π)*T*(Ct M*k²+Cs M*h²)*sqrt(Σ ‖a_m‖²).
```

The actual initial grid state may contain arbitrary frequencies; its mismatch is retained. `StageBridge.actual_superposition_stage_budget` constructs the associated actual finite-band stage budget. These rely on the constant-potential invariant-mode structure.

`Exp009.infinite_grid_error_bound` (`exp009/lean/InfiniteClosure.lean:51`) has the same mesh/cutoff/time premises and absolute summability of `a`; the extra term is `sqrt(2π)*2*tail M a`, and the finite-band coefficient norm is bounded by `mass a`. The full grid trajectory is not replaced by a projected numerical trajectory. `WeightedTail.tail_le_moment_div` gives `tail M a ≤ moment r a/(M+1)^r` under the stated weighted summability.

`Exp010.Regular a` means `Summable (fun m => (1+|m|)^2 * ‖a m‖)`. The classical closure establishes the actual classical reference and its sampled grid error. The concrete Exp009 schedule is

```text
M=q+1, grid points=8*M³, h=2π/(8*M³),
k=1/(6*M⁴), number of steps=6*M⁴, final time=1.
```

All its cutoff, anti-aliasing and time-step premises are proved. The weighted cost tends to zero like O(M⁻²). This is a proved schedule for the old branch; it is not a universal CFL or a proved variable-potential refinement family.

## Sampling, full-grid Fourier inversion and reconstruction

`Exp010.sampleSolution` (`exp010/lean/ClassicalClosure.lean:11`) samples **any** `u : ℝ → ℝ → E 2`, returning `WithLp.toLp 2 (fun (j,b) => u t (j*h) b)`. `Exp011.nodeValue` (`exp011/lean/Reconstruction.lean:16`) reverses the component packaging at a node. `nodeValue_sampleSolution` (`:24`) is the direct sampling identity. `nodeValue_norm_le` (`:30`) only bounds a node by the **unweighted** full norm. Converting from mesh norm incurs `1/sqrt(h)`; it does not prove the faithful continuum L2 norm bridge required in the Exp016 plan.

Useful discrete Fourier APIs are in namespace `NDEAEvolve.Exp008.FourierGrid`, `exp008/lean/Orthogonality.lean`:

- `phase_mesh_eq_one_iff_dvd` (`:29`): `exp(i*r*h)=1` iff `n+1` divides the integer r, under the period relation.
- `phase_sum_zero` (`:48`): the sum over all grid nodes of that phase character is zero for a frequency not divisible by `n+1`.
- `band_difference_not_dvd` (`:68`) gives the required nondivisibility for distinct frequencies in an unaliased band.
- `modeLift_inner_eq_zero` (`:103`) gives column orthogonality.
- `AliasFree n S` (`:119`) means distinct m,l in S have `(n+1) ∤ (l-m)`; `aliasFree_of_band` (`:122`) discharges it from `2*M<n+1`.
- `superposition_norm_sq` (`:127`) is `‖Σ modeLift(a_m)‖²=(n+1)*Σ‖a_m‖²`.
- `superposition_weighted_norm` (`:157`) is `sqrt(h)*‖Σ modeLift(a_m)‖=sqrt(2π)*sqrt(Σ‖a_m‖²)`; `band_superposition_weighted_norm` (`:169`) packages the band hypothesis.

For the proposed odd full grid, set `n=2*M` and `S=Icc(-M) M`. Then the band contains exactly `n+1=2*M+1` frequencies and `2*M<n+1` still holds. Thus the existing column orthogonality is available at full dimension, including M=0 where the distinction condition is vacuous.

Two concrete routes to the **new** DFT inverse proof are available:

1. Define the normalized coefficient transform as the adjoint of synthesis; use existing column orthogonality to obtain a left inverse, then equal finite dimensions to obtain surjectivity and a right inverse.
2. Reindex the centered integer band by `Fin(2*M+1)` and prove the row character sum by the same geometric-series argument as `phase_sum_zero`. This directly shows the proposed coefficient formula samples back to every grid value.

No full inverse theorem, basis/surjectivity theorem, or continuum integral Parseval theorem is already present in the audited Exp008 modules. Discrete Parseval alone cannot be quoted as `‖S_h y‖L2=sqrt(h)*‖y‖`; one must prove continuum character orthogonality, relate its coefficient normalization, and prove inversion for arbitrary y. Existing `ContinuumModes.phaseMode_periodic` and its phase derivative lemmas provide kinematic ingredients, but the saved `modeSolution` includes an orbit-specific coefficient and is not itself a general time-dependent synthesis operator.

`Exp011.reconstruction` (`Reconstruction.lean:79`) uses `spaceIndex=min(floor(x/h),n)` and `timeIndex=min(floor(t/k),N)` to select a node of an actual numerical iterate. It is piecewise constant in both variables. At the spatial endpoint 2π it selects the last node rather than wrapping to node zero; the definition outside the rectangle clamps instead of extending periodically. Its existing error theorem adds `moment 2 a*h + 2*moment 2 a*k` to the grid error divided by `sqrt(h)`.

`Exp011.reconstruction_tendstoUniformlyOn` in `UniformConvergence.lean` proves convergence on `[0,1]×[0,2π]`. The scheduled nodal bound is O(M⁻¹/²), from the weighted estimate and the mesh-norm-to-node loss. This is a valid uniform-convergence result for a discontinuous approximation, not a claim that each approximation is classical.

`Exp012.classical_existsUnique`, `reconstruction_converges_to_classical`, and `reconstruction_error_to_classical` (`exp012/lean/ClassicalUniqueness.lean:45,52,61`) identify that actual numerical reconstruction's limit with **every** classical solution with the same initial data, using uniqueness. Therefore the narrow constant `Z+X` end-to-end endpoint is already achieved.

## Read-only assessment of the current Exp016 plan

The selected full odd-grid Fourier interpolation plus a globally polynomial extension on each time slab addresses the two principal interface gaps: fidelity to arbitrary actual grid data, and actual derivatives satisfying `Exp015.IsRegularPeriodicField`. Exp015 requires joint continuity of the field and its time/first-space/second-space derivatives, spatial periodicity, and actual differentiability at every real time and position. Applying it separately to global polynomial slab extensions is compatible with that requirement; merely stitching them does not establish a global regularity theorem.

The plan preserves the saved order and has consistent residual signs at the level of a read-only algebra check. With `m=(y0+y3)/2`, `v=(y3-y0)/k`, `eta=(y1+y2)/2-m`, its measured denominator residual convention gives

```text
d = i*v - (A+B)*m = (i/k)*(r1+r2+r3) + (A/2+B)*eta.
```

For exact stages only, eliminating their increments gives the proposed **ordered** expression

```text
eta = (k²/32)*A²*(y0+y1+y2+y3) + (k²/8)*A*B*(y1+y2).
```

This formula does not permit replacing AB by BA. For Hermitian exact stages, their equal norms yield the stated coarse fixed-grid `‖d‖ ≤ (k²/16)*‖A‖*(‖A‖+2‖B‖)²*‖y0‖`. These observations are design checks, not new accepted Lean theorems.

For `tau=t-(t0+k/2)` and the proposed `Q=m+tau*v-(i/2)*(tau²-k²/4)*H*v`, direct differentiation cancels the affine leading temporal term and leaves `i Q'-H Q=d+(i/2)*(tau²-k²/4)*H²v`. Thus the proposed residual decomposition has the correct sign when `C_h z=S_h(H z)-(-∂xx S_h z+V S_h z)`. An affine interpolation alone would retain a term proportional to tau and would not provide the same fixed-grid second-order certificate.

Still new and necessary before accepting the Exp016 endpoint: the sampled-potential matrix and legacy identity; full DFT inversion and continuum L2 normalization; polynomial synthesis regularity and endpoints; the actual discrete-to-continuum defect identity; an L2 triangle bound and derived slab budget; the actual-trajectory consumer and slab accumulation with arbitrary initial mismatch. `Exp015.residual_error_uniform_budget` (`exp015/lean/ResidualEstimate.lean:62`) is a direct final consumer after these obligations are proved.

Spatial refinement remains a separate substantive obligation. In particular, `C_h` cannot be declared small on arbitrary highest-frequency grid data, and Exp014 second Fourier moments cannot silently be treated as all higher graph-norm bounds. The proposed schedule in PLAN.md is not yet a proof of vanishing spatial defects. The audit supports the stated Exp016 boundary as an actual numerical residual certificate, with full variable-potential convergence left explicitly open.
