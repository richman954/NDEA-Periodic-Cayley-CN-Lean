# Experiment 007 — verified noncommuting periodic spinor closure

Completed September 8, 2026. **Local and independent combined verification passed all 88 audits: 81 production theorems and seven controls.**

The model is the two-component periodic Schrödinger equation

\[
i\,\partial_t U=-\partial_{xx}U+(Z+X)U,
\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

The spatial domain has period \(2\pi\). The reference solution is
\(U(t,x)=e^{ix}v(t)\), where
\(v(t)=\exp[-it(I+Z+X)]v_0\) for arbitrary \(v_0\in\mathbb C^2\).
[ContinuumSpinor.lean](lean/ContinuumSpinor.lean) proves its actual real time
derivative, second spatial derivative, displayed PDE, periodicity, initial
value, norm preservation, and exact-step composition law. In particular,
\(\|v(t)\|=\|U(t,x)\|=\|v_0\|\); the initial amplitude is not silently
normalized.

The two split operators retain noncommuting internal matrices. On the first
Fourier mode they reduce to \(A(\lambda)=\lambda I+Z\) and \(B=X\), with
\([A(\lambda),B]=[Z,X]\ne0\). The centered periodic stencil has symbol
\(\lambda_h=(2-2\cos h)/h^2\). Its reduced norm bounds and spatial consistency
estimate are uniform in the number of grid points. The full grid uses the
wrapped negative second difference with two components at each site:
\(A_h=-D_{xx,h}\otimes I+I\otimes Z\) and \(B_h=I\otimes X\).
[SpinorGrid.lean](lean/SpinorGrid.lean) proves the finite-grid intertwining and
Cayley-stage identities, Hermitian stability, and the exact weighted lift norm.
For \(d=n+1\) spatial sites and \(dh=2\pi\), the Fourier lift satisfies
\(\sqrt h\,\|J_hw\|=\sqrt{2\pi}\,\|w\|\).

The symmetric step is
\(S_{h,k}=C_{A_h}(k/4)C_{B_h}(k/2)C_{A_h}(k/4)\), with
\(C_H(a)=(I-iaH)(I+iaH)^{-1}\). Its proved error theorem in
[FullClosure.lean](lean/FullClosure.lean) is

\[
e_N\le e_0+\sqrt{2\pi}\,T
\left(27000\,k^2+\frac{h^2}{8}\right)\|v_0\|,
\]

under \(0<h\le1\), \(0\le k\le1/6\), \(dh=2\pi\), and \(Nk\le T\).
Here \(e_N=\sqrt h\,\|S_{h,k}^Nz_0-J_hv(Nk)\|\) and
\(e_0=\sqrt h\,\|z_0-J_hv_0\|\). The numerical initial vector \(z_0\) may be
any full-grid state, including other grid modes. Its entire initial error is
retained. Exact sampling gives \(e_0=0\). The temporal bound \(k\le1/6\) is
independent of the mesh spacing; no condition coupling \(k\) to \(h^2\) is used.
The mesh-family endpoint takes \(h,k,e_0\to0\) while \(Nk\le T\); it concerns
errors at the actual terminal times \(Nk\), without asserting that those times
equal or approach \(T\).

The second route uses the existing Experiment 005 three-stage residual budget.
The first two reference auxiliary states are the actual first and second
numerical stages, so those two factor residuals vanish. The final factor
residual is a denominator applied to the separately bounded complete-step
defect. [ReducedClosure.lean](lean/ReducedClosure.lean) proves

\[
\mathcal B_j\le\sqrt{2\pi}\,k
\left(29250\,k^2+\frac{13h^2}{96}\right)\|v_0\|.
\]

The conservative constants are the direct constants multiplied by the
denominator bound \(13/12\). [StageBridge.lean](lean/StageBridge.lean) proves
the exact equality between this budget and the physically weighted residuals
of the actual wrapped grid stages. It also identifies the lifted reference as
the sampled continuum PDE solution and states actual full-grid noncommutation.
The direct global bound and this residual-budget route retain the factor
\(\|v_0\|\); they do not assume unit amplitude.

The present proof scope is one nonconstant spatial Fourier mode with
noncommuting constant internal coupling. It establishes a concrete
noncommuting extension of Experiment 006. General smooth initial functions,
spatial mode mixing, and spatially varying potentials remain outside this
scope. Arbitrary numerical initialization is handled through \(e_0\), which
does not enlarge the continuum reference class.

The seven new modules passed separately both locally and in the fresh Colab
runtime. The final combined checks re-elaborated the complete frozen foundation
and every new proof, using only isolated external library artifacts. All 88
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

Local combined check: **289.022 seconds**. Independent combined check: **162.250 seconds**, completed `2026-09-08T06:16:52.729167+00:00`. Each run checked 9,868 external artifact hashes before and after. Exact reconstruction of the combined source and complete audit catalog passed.

All 9,868 external artifact hashes also agree between the two environments.
The independent runtime downloaded the pinned compiler and compatible library
cache itself. No locally built project artifacts were uploaded. Lean and
Mathlib themselves were not rebuilt from scratch. External compiled libraries
remain the stated trust boundary.

| Module | Successful local receipt |
| --- | --- |
| ReducedNoncommuting | [receipt](evidence/20260908T055715.664506Z_ReducedNoncommuting.json) |
| SpinorGrid | [receipt](evidence/20260908T060015.249331Z_SpinorGrid.json) |
| ContinuumSpinor | [receipt](evidence/20260908T060447.855291Z_ContinuumSpinor.json) |
| ReducedClosure | [receipt](evidence/20260908T060431.947498Z_ReducedClosure.json) |
| FullClosure | [receipt](evidence/20260908T061024.803754Z_FullClosure.json) |
| StageBridge | [receipt](evidence/20260908T061302.441510Z_StageBridge.json) |
| Controls | [receipt](evidence/20260908T061546.776441Z_Controls.json) |

The final qualification is recorded in [FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json), with the [local complete result](evidence/local_combined/RESULT.json) and [independent complete result](remote_check/downloaded_evidence/exp007_independent_evidence/final_verification/RESULT.json).

[Numerical diagnostics](evidence/numerical_checks.json) passed 90 stage-budget
cases and 30 global-error cases. These are supporting floating-point checks.
They do not replace Lean proof verification.

| Diagnostic | Observed result |
| --- | --- |
| Joint spatial/time refinement, 8 through 512 sites/steps | Order increased from 1.97634 to 1.999977; final weighted error \(3.4214\times10^{-5}\) |
| Temporal refinement with continuum symbol \(\lambda=1\), 12 through 384 steps | Order increased from 1.999410 to 1.999998 |
| Unsymmetric Lie-step sensitivity control | Order approached 0.998757, detecting the loss of second order |
| Wrapped-grid intertwining | Maximum discrepancy \(4.151\times10^{-13}\) |
| First two actual factor residuals | Maximum weighted residual \(3.754\times10^{-14}\) |
| Noncommutation witness | Commutator applied to the normalized test spinor had norm 2 |
| Omitted spatial term control | Actual error 0.163811 exceeded the temporal-only bound \(6.768\times10^{-6}\) |

The formal [Controls.lean](lean/Controls.lean) source supplies a normalized
spinor, an admissible eight-point grid, active internal coupling, a spatially
nonconstant initial solution, the consequence of removing coupling, failure
at zero mesh spacing, and retention of initial error for zero steps. All seven controls passed the final combined audit.

[Predecessor preservation](evidence/PREDECESSOR_PRESERVATION.json) passed:
Experiment 005 matched all 889 frozen entries; Experiment 006 matched all 21
local verified entries and all 99 final packet entries. The Experiment 006
SHA256SUMS file agrees with its JSON local manifest. The receipt records the
manifest paths and hashes, entry counts, and unchanged manifest hashes during
the checks. No predecessor file was modified.

The [convergence figure](evidence/exp007_convergence.png) visualizes the supporting diagnostics. [REPRODUCE.md](REPRODUCE.md) describes the pinned environment and standalone verification command.

Combined source SHA-256: `cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c`.
