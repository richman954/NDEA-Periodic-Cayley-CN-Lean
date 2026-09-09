# Finite Fourier superpositions: verified derivation

This derivation accompanies the completed Experiment 008 proof. Both combined checks passed all 90 audits; the accepted evidence is [FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). This explanatory document records the mathematics, while the receipt establishes the verification status.

Let `S` be a finite set of integers, `a_m ∈ ℂ²`, and `M≥1` a fixed cutoff such that `|m|≤M` on `S`. Set

`U(t,x)=Σ_m exp(imx) exp[-it(m²I+Z+X)]a_m`.

The matrices `Z=diag(1,-1)` and `X=[[0,1],[1,0]]` are Hermitian and do not commute. Every summand solves `iU_t=-U_xx+(Z+X)U`, and finite sums commute with the required real derivatives. This gives an actual continuum solution with arbitrary finite signed frequency content, including zero frequency.

## The grid and frequency representation

Use `d=n+1` spatial sites, `h>0`, `d*h=2π`, and the actual cyclic centered negative second difference. The full split generators are

`A_h=-D_xx,h ⊗ I + I ⊗ Z`, `B_h=I ⊗ X`.

The lift `J_m(v)(j,b)=exp(imjh)v_b` intertwines these matrices with `A(λ_m,h)=λ_m,h I+Z` and `B=X`, where

`λ_m,h=(2-2cos(mh))/h²`.

The integer-frequency exponential is periodic over `2π`; the two wrapped grid endpoints therefore satisfy the same eigenrelation as interior sites. Generic denominator, numerator, and invertibility identities transfer the intertwining to the actual Cayley factors. Each full-grid CN stage is unique, and the full-grid symmetric product is unitary.

For distinct frequency residues modulo `d`, the finite geometric sum vanishes. If `d>2M`, distinct frequencies in the band cannot differ by a nonzero multiple of `d`. Consequently,

`sqrt(h) ‖Σ_m J_m(a_m)‖ = sqrt(2π) (Σ_m ‖a_m‖²)^(1/2)`.

This is the discrete Parseval identity used for the error and residual estimates. An aliasing witness with opposite coefficients at frequencies `0` and `d` cancels on the grid while its coefficient norm is nonzero, demonstrating why the sampling condition matters.

## Frequency-dependent local and global error

For `|m|h≤1`, the cosine remainder estimate gives

`0≤λ_m,h≤m²`, `|λ_m,h-m²|≤m⁴h²/8`.

The reduced matrix norm is bounded by `m²+1`; adding `‖X‖≤1` yields `M²+2`. Experiment 004's cubic local estimate therefore applies when

`0≤k`, `2k(M²+2)≤1`.

The Cayley perturbation bound transfers the scalar spatial-symbol error with factor `k`. For each frequency, the combined one-step defect is at most

`k[Ct(M)k²+Cs(M)h²]`,

where `Ct(M)=1000(M²+2)³` and `Cs(M)=M⁴/8`, assuming `Mh≤1`. Telescoping unitary powers gives the frequency-wise global bound `T[Ct(M)k²+Cs(M)h²]` when `Nk≤T`.

Apply this common bound to each coefficient and use Parseval to aggregate squared errors. Full-grid unitarity carries any numerical initial discrepancy without growth. The proved endpoint is

`e_N ≤ e_0 + sqrt(2π)T[Ct(M)k²+Cs(M)h²](Σ_m ‖a_m‖²)^(1/2)`.

The scalar weighted errors converge when `h,k,e_0→0` under the same horizon and fixed `S,M,a`. The actual terminal times are `Nk≤T`; no equality or convergence of these terminal times to `T` is required.

## Actual three-stage residuals

For each macrostep, choose the first and second reference auxiliary states as the actual first and second numerical stages from the sampled exact solution. Their unscaled denominator residuals vanish. The third residual is the final Cayley denominator applied to the independently bounded complete-step defect.

On each frequency, `‖I+i(k/4)A(λ_m,h)‖≤1+(k/4)(M²+1)≤9/8`. Linear Fourier lifting identifies each full-grid residual with the lifted array of Experiment 005 factor residuals. Parseval aggregates their norms. The proved actual physical budget is bounded by

`(9/8)sqrt(2π)k[Ct(M)k²+Cs(M)h²](Σ_m ‖a_m‖²)^(1/2)`.

The coefficient norm is preserved by the exact per-frequency evolution, so this bound is uniform over the macrostep start time. Its constants are conservative.

## Scope

The estimate is independent of the number of grid points for a fixed cutoff. Its frequency dependence is explicit. Allowing `M` to grow with refinement requires additional regularity and tail estimates. A spatially varying potential mixes Fourier modes and is outside this finite invariant-subspace result. Arbitrary numerical initialization is accounted for by `e_0`; it does not enlarge the continuum reference class.

The numerical script checks an active spectrum `{-2,0,1,2}` with complex spinor coefficients. Its stage, trajectory, Parseval, wrapped-stencil, aliasing, and refinement checks are supporting floating-point diagnostics. Lean verification is separate.
