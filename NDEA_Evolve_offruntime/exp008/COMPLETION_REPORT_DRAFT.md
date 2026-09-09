# Experiment 008 — finite Fourier superpositions

**Draft dated September 8, 2026. Final acceptance is pending.** This report describes the implemented mathematical results and recorded numerical diagnostics. The verification fields below must be replaced with the final receipts before a completion claim is made.

Experiment 008 extends Experiment 007 from one spatial Fourier mode to arbitrary finite sets of signed integer frequencies, with arbitrary complex two-component coefficients. The full periodic grid scheme retains its noncommuting split. The resulting error bound uses the coefficient ℓ² norm and has constants independent of grid dimension for a fixed frequency cutoff.

Let `Z=diag(1,-1)`, `X=[[0,1],[1,0]]`, `S⊂ℤ` be finite, and `a_m∈ℂ²`. The continuum reference is

```text
U(t,x) = Σ_{m∈S} exp(imx) exp[-it(m²I+Z+X)] a_m,
i ∂t U = -∂xx U + (Z+X)U,
U(t,x+2π) = U(t,x),
U(0,x) = Σ_{m∈S} exp(imx) a_m.
```

`ContinuumModes.lean` constructs the actual real time derivative and second real space derivative, proves this PDE and periodicity, and proves exact orbit composition and norm preservation. Zero and negative frequencies are included.

Use `d=n+1` spatial sites with `h>0` and `dh=2π`. The actual wrapped centered negative second difference gives

```text
A_h = -D_xx,h ⊗ I + I ⊗ Z,       B_h = I ⊗ X,
C_α(H) = (I-iαH)(I+iαH)⁻¹,
S_h,k = C_{k/4}(A_h) C_{k/2}(B_h) C_{k/4}(A_h).
```

The full-grid stages are uniquely solvable, and the symmetric step is unitary. The frequency lift `J_m(v)(j,b)=exp(imjh)v_b` intertwines the wrapped grid operators and their Cayley factors with `A(λ_m,h)=λ_m,h I+Z` and `B=X`, where `λ_m,h=(2-2cos(mh))/h²`. Under `|m|h≤1`, the symbol satisfies `0≤λ_m,h≤m²` and `|λ_m,h-m²|≤m⁴h²/8`.

The error endpoint assumes

```text
M∈ℕ, M≥1, |m|≤M for every m∈S,
d>2M, h>0, dh=2π, Mh≤1,
k≥0, 2k(M²+2)≤1, N∈ℕ, Nk≤T.
```

The sampling condition excludes aliasing between distinct frequencies in `S`. `FourierGrid.lean` and `Orthogonality.lean` prove the exact weighted discrete Parseval identity

```text
√h ‖Σ_{m∈S} J_m(a_m)‖₂ = √(2π) ‖a‖ℓ²,
‖a‖ℓ² = (Σ_{m∈S} ‖a_m‖₂²)¹ᐟ².
```

Set `Ct(M)=1000(M²+2)³` and `Cs(M)=M⁴/8`. For an arbitrary initial grid vector `W₀`, define `W_N=S_h,k^N W₀`, let `R_hU(t)` denote the sampled continuum solution, and put `e_N=√h‖W_N-R_hU(Nk)‖₂`. The endpoint `finite_superposition_grid_error` in `SuperpositionClosure.lean` states

```text
e_N ≤ e₀ + √(2π) T [Ct(M)k² + Cs(M)h²] ‖a‖ℓ².
```

Every initial grid vector is allowed, including components outside the reference spectrum; its entire discrepancy is retained in `e₀`. Exact sampled initialization gives `e₀=0`. The proof combines frequency-dependent local consistency, telescoping of unitary powers, Parseval, and full-grid stability. `superposition_is_sampled_solution` identifies the reference in this bound coordinate by coordinate with the continuum PDE solution.

`finite_superposition_mesh_error_tendsto_zero` then proves convergence of these scalar weighted grid errors for mesh families with `h→0`, `k→0`, and `e₀→0`, satisfying the stated hypotheses on each mesh. The spectrum, cutoff, coefficients, and horizon stay fixed. The terminal times are the actual `Nk≤T`; the theorem requires neither `Nk=T` nor convergence of those times to `T`.

`StageBridge.lean` also derives the actual Experiment 007 three-stage budget using Experiment 005 factor residuals. At any start time `t`, take `v₀=R_hU(t)`, `v₁=C_{k/4}(A_h)v₀`, `v₂=C_{k/2}(B_h)v₁`, and `v₃=R_hU(t+k)`. With `(H₁,H₂,H₃)=(A_h,B_h,A_h)` and `(α₁,α₂,α₃)=(k/4,k/2,k/4)`, the measured budget satisfies

```text
√h Σ_{r=1}³ ‖(I+iα_r H_r)v_r - (I-iα_r H_r)v_{r-1}‖₂
  ≤ (9/8) √(2π) k [Ct(M)k² + Cs(M)h²] ‖a‖ℓ².
```

The first two residuals vanish because their states are actual numerical stages. The final residual follows from the independently bounded complete-step defect and a reduced denominator norm at most `9/8`. Exact residual decomposition and Parseval retain the coefficient ℓ² norm. This is `actual_superposition_stage_budget`; no residual-budget assumption is used. The global error endpoint is proved directly through unitary powers and Parseval, and does not invoke this stage-budget theorem as an intermediate premise.

The seven public controls in `Controls.lean` cover the following concrete statements:

| Control | Statement |
|---|---|
| `active_signed_superposition` | Modes `{-1,0,1}` have nonzero coefficients of norms `1,2,3`; coefficient norm is `√14`, and the physical initial value at `x=0` is nonzero. |
| `admissible_multimode_grid` | Cutoff `M=1`, eight sites, `h=π/4`, and positive step `k=1/12` satisfy the mesh and step restrictions. |
| `grid_size_alias` | Frequencies `0` and `d` have identical sampled lifts. |
| `aliasing_breaks_naive_parseval` | Opposite coefficients at those aliased frequencies cancel on the grid while their coefficient norm is nonzero. |
| `empty_trajectory_retains_initial_error` | With zero steps, the final error equals the entire initial error. |
| `full_grid_split_is_noncommuting` | The actual full-grid `A_h` and `B_h` do not commute. |
| `frequency_constants_increase` | Both constants strictly increase from cutoff `1` to cutoff `2`. |

The existing [numerical diagnostics](evidence/numerical_checks.json), produced by [numerical_checks.py](numerical_checks.py), record `passed: true` for cutoff `M=2`, active spectrum `{-2,0,1,2}`, and normalized complex spinor coefficients. They include 60 actual wrapped-stage cases, 20 global-error cases, seven joint-refinement levels, and six levels each for temporal refinement and a Lie-splitting sensitivity comparison. The finest observed orders are approximately `1.999975` jointly, `1.999994` temporally, and `0.999673` for Lie splitting. The temporal comparisons use the continuum spatial symbol to isolate time error. Maximum recorded discrepancies are approximately `4.44×10⁻¹⁶` for Parseval, `5.92×10⁻¹³` for wrapped-stencil intertwining, and `2.35×10⁻¹⁴` for the first two stage residuals. Aliasing and an added initial frequency outside the reference cutoff are also exercised. These are floating-point diagnostics; the constants in the theorem are conservative. See the [refinement plot](evidence/exp008_convergence.png).

The current declaration inventory is **90 new public theorems: 83 production theorems and 7 controls**. Counts are `FrequencyBounds:15`, `ContinuumModes:25`, `FourierGrid:13`, `Orthogonality:12`, `SuperpositionClosure:10`, `StageBridge:8`, and `Controls:7`. This is an inventory, not a completed combined-audit count. The final combined source must re-elaborate the frozen Experiment 007 foundation and all seven modules while importing only external libraries. Exploratory probes are excluded.

| Final verification field | Status to replace with final evidence |
|---|---|
| Combined source and exact audit catalog | **PENDING — [combined SHA-256; catalog path/hash]** |
| Local combined verification | **PENDING — [RESULT.json path; accepted status; elapsed time; source stability]** |
| Independent combined verification | **PENDING — [RESULT.json path; accepted status; elapsed time; source stability]** |
| Complete public axiom audits | **PENDING — [90/90 coverage and allowed-axiom validation in both runs]** |
| Independent evidence transfer and artifact comparison | **PENDING — [export/transfer receipt; comparison result]** |
| Predecessor preservation | **PENDING — [final preservation receipt]** |
| Review packet and release identifiers | **PENDING — [archive path/SHA-256; commit/tag if applicable]** |

The acceptance policy permits only `propext`, `Classical.choice`, and `Quot.sound` in the audited dependencies. The checker reconstructs exact combined bytes and the public audit catalog, checks dependency source revisions and compiler/helper pins, isolates copied external artifacts, validates the axiom log, and compares relevant hashes before and after compilation. A successful compiler process alone does not establish all these checks. See [REPRODUCE.md](REPRODUCE.md) for commands and [REVIEW.md](REVIEW.md) for the mathematical and verification-design review.

The trust boundary includes Lean 4.31.0, its core libraries, and compatible compiled external libraries. The checks pin source revisions and the compiler binary, and record/stability-check copied library artifacts; they do not rebuild Lean or Mathlib, prove source-to-artifact correspondence, or pre-pin every core-library file. Final independent agreement must be evidenced by the receipts above.

The result is uniform in grid dimension for a fixed finite frequency band. Growing cutoffs need further regularity and tail estimates. Infinite Fourier data and spatially varying potentials that mix frequencies remain outside this milestone. Arbitrary numerical initialization enlarges the permitted initial grid state while leaving the continuum reference class finite-spectrum. Further derivation and proof obligations are recorded in [MATHEMATICAL_DERIVATION.md](MATHEMATICAL_DERIVATION.md).
