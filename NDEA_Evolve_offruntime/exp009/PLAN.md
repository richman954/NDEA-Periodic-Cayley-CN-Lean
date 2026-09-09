# Experiment 009 — infinite Fourier reference and growing cutoff

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md). The previous experiments and their sealed
evidence remain unchanged. No new theorem is accepted until the verification
receipts pass.

Extend Experiment 008's noncommuting periodic spinor evolution to coefficients
`a : ℤ → ℂ²` satisfying `Σ ‖a_m‖ < ∞`. Construct the actual infinite Fourier
reference by summing the existing exact mode orbits. The PDE model remains
`i U_t = -U_xx + (Z+X)U`; absolute summability alone supplies a Fourier evolution
reference, and does not imply the classical second derivatives needed to
assert this PDE pointwise. Classical infinite-series differentiation is a
separate regularity milestone.

For `band(M)={-M,…,M}`, define `A=Σ ‖a_m‖` and
`tail(M)=Σ_{|m|>M} ‖a_m‖`. Prove the sampled truncation bound
`√h ‖R_h U(t)-R_h U_M(t)‖ ≤ √(2π) tail(M)` without assuming
orthogonality of infinitely many sampled frequencies. Derive from the actual
finite-grid evolution, for arbitrary numerical initialization,

```text
e_N ≤ e_0 + √(2π) [T(Ct(M)k²+Cs(M)h²) A + 2 tail(M)].
```

Here `e_0` is measured against the full infinite reference. The two tails
account for truncation at the initial and terminal times. Retain all mesh,
nonaliasing, step, and horizon hypotheses of Experiment 008 on the finite band.

Prove convergence when `M→∞`, the explicit consistency cost tends to zero,
and the full-reference initial error tends to zero. Prove a concrete admissible
schedule `M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`, which reaches
`T=1` exactly and has vanishing consistency cost. This proves convergence for
the full absolute-summable class; it does not promise a universal second-order
rate for that class. The Fourier tail may decay slowly.

Acceptance includes modular checks, complete new public axiom audits, combined
source verification with project artifacts excluded, a second-environment
Colab combined check, evidence transfer/hash comparison, negative or exact
controls, supporting infinite-reference numerical diagnostics, preserved
predecessor hashes, reproduction instructions, and a sealed review packet.

The frozen foundation is the exact Experiment 008 combined source, SHA-256
`5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0`.
Development uses earlier modular artifacts; final combined checks re-elaborate
all project source. Lean 4.31.0 and compatible compiled external libraries
remain the documented trusted inputs. The independent Colab check uses a
newly allocated replacement CPU VM, session `exp009-independent-check`, with
its pinned compiler and external libraries independently downloaded under
`/content/exp009_check` and no uploaded project artifacts. The earlier
`exp008-fresh-recheck-r2` runtime became unavailable before this independent
proof check. Its prepared request and environment records remain preserved in
`remote_check/lost_runtime/`; accepted local proofs and earlier sealed evidence
were unaffected.
