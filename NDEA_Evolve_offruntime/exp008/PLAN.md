# Experiment 008 — finite Fourier superpositions

Status: completed, September 8, 2026. All acceptance criteria below passed. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md) and [FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). The original target and acceptance criteria are retained below.

Extend the completed Experiment 007 noncommuting periodic spinor PDE to finite sums of signed integer Fourier modes. Preserve the frozen predecessor sources and release packets. The PDE and actual centered-grid symmetric Cayley scheme remain those of Experiment 007:

`i U_t = -U_xx + (Z+X)U`, period `2π`, with `Z=diag(1,-1)` and `X` the component swap.

For a finite set `S ⊂ ℤ`, coefficients `a_m ∈ ℂ²`, and fixed cutoff `M≥1` with `|m|≤M` on `S`, the reference is

`U(t,x) = Σ_{m∈S} exp(imx) exp(-it(m²I+Z+X)) a_m`.

## Acceptance criteria

1. Prove actual real continuum derivatives, the displayed PDE, periodicity, initial value, and exact orbit composition for the finite superposition. Include zero and negative frequencies.
2. Prove the actual wrapped centered stencil eigenrelation and full-grid Cayley intertwining for each integer frequency. Prove discrete orthogonality and weighted Parseval when `d*h=2π` and `d>2M`.
3. Derive uniform-in-grid local bounds from the existing finite-matrix theorem with frequency dependence explicit. For `0<h`, `M*h≤1`, `0≤k`, and `2*k*(M²+2)≤1`, use
   `Ct(M)=1000*(M²+2)³`, `Cs(M)=M⁴/8`.
4. Prove the full-grid endpoint, for `N*k≤T` and arbitrary numerical initial grid state,
   `e_N ≤ e_0 + sqrt(2π)*T*(Ct(M)*k²+Cs(M)*h²)*sqrt(Σ ‖a_m‖²)`.
   Prove convergence for a fixed finite spectrum as `h,k,e_0→0` under a common time horizon.
5. Derive the actual Experiment 005 three-stage residual budget. The first two reference stages are actual numerical stages. Bound the last denominator by `9/8`, yielding a conservative budget of
   `(9/8)*sqrt(2π)*k*(Ct(M)*k²+Cs(M)*h²)*sqrt(Σ ‖a_m‖²)`.
6. Include exact controls for multiple active signed frequencies, zero mode, sampling aliasing, noncommuting coupling, and retention of initial error. Add numerical refinement and aliasing diagnostics as supporting evidence.
7. Pass all production/control modules, combined source reconstruction, complete new public theorem axiom audits, local verification, independent Colab verification, evidence-transfer checks, and predecessor-manifest checks. Save a final report, reproduction instructions, and a checksum-verified review packet.

## Scope and dependencies

The cutoff is fixed in the convergence endpoint. Constants may depend on `M` and the coefficient norm, and must not depend on the number of grid points. A cutoff growing with refinement requires additional regularity/tail estimates and is outside this milestone. Constant internal matrices preserve individual frequencies; a spatially varying potential and spatial mode mixing remain later work.

The copied foundation is `lean/Exp007Foundation.lean`, SHA-256
`cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c`.
It is byte-identical to the verified Experiment 007 combined source. Modular development may use project artifacts; final combined verification must exclude all project artifacts. The pinned Lean/compiler and compatible external library cache remain the documented trust boundary.

Implementation split: `FrequencyBounds.lean`, `FourierGrid.lean` / orthogonality, `ContinuumModes.lean`, full superposition closure, stage bridge, and controls. Intermediate failures and repairs will be retained as dated evidence, with a final receipt determining accepted status.
