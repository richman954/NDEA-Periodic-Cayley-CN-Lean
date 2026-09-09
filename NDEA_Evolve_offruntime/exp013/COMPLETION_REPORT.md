# Experiment 013 — generic periodic Schrödinger energy and uniqueness

Completed 2026-09-08. All **64 new public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM,
with only `propext`, `Classical.choice`, and `Quot.sound`. All 5 new
modules passed separately.

The reusable framework applies to functions with values in any complex Hilbert
space H, any positive spatial period L, time/space dependent Hermitian
operators V(t,x), and forcing f(t,x). Each V(t,x) is bounded; no uniform
operator-norm bound is assumed:

```text
i ∂t u = −∂xx u + V(t,x)u + f(t,x).
```

The classical predicate requires the actual first time and first/second space
derivatives, their specified joint continuity, periodicity, and the pointwise
PDE. No Fourier representation, energy law, global time bound, finite fiber
dimension, or continuity/periodicity assumption on V or f is added. These are
conditional results about solutions satisfying the classical predicate.

The proof derives the local and integral identities

```text
ρ = ‖u‖²,  J = 2 Re⟨u, i ∂x u⟩,  W = 2 Re⟨u, −i f⟩,
∂t ρ = ∂x J + W,
d/dt ∫[b,b+L] ‖u(t,x)‖² dx = ∫[b,b+L] W(t,x) dx.
```

Continuity of W follows from the difference of the actual density and flux
derivatives. A compact local time-space rectangle justifies differentiation
of the scalar integral. Periodicity cancels the boundary flux. Here energy
means squared L² norm (mass) for L>0, not Hamiltonian expectation. The balance
and conservation identities also hold for arbitrary real L when their
integrals are understood as oriented interval integrals.

For zero forcing this mass is conserved for all real times and interval bases.
For two solutions with the same V and forcing, their difference solves the
homogeneous equation, so their squared L² distance is conserved. When L>0,
matching data at any one real time imply equality at every real time and
position. Positivity and continuity convert zero integral energy into pointwise
equality, including interval endpoints.

The exact legacy predicate bridge recovers the previous two-component model
and identifies the earlier uniformly convergent numerical reconstruction with
its unique classical solution under the unchanged data and mesh assumptions.
Generic files import Mathlib directly; their reuse does not require importing
the concrete predecessor experiments.

The exact controls include the nonzero nonconstant stationary scalar solution
u(x)=2+sin(x) with V(x)=−sin(x)/(2+sin(x)), and the forced solution u(t,x)=t,
V=0, f=i. They check genuine spatial dependence and active potential, the
forcing-work sign, and failure of integral separation when the period is zero.

| Accepted check | Result |
|---|---|
| New modular sources | 5 passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | 64 audits; exit 0; 602.710 seconds |
| Independent combined source | 64 audits; exit 0; 384.128 seconds |
| Source/catalog | Reconstructed exactly and unchanged during both checks |
| External artifact hashes | 10,688 agree across environments |
| Evidence transfer | 89 payload hashes and compiler audits verified |
| Predecessors | Sealed manifests and Exp012 packet preserved |

The distinct CPU session is `exp013-independent-check-r2`, initially empty at
`/content/exp013_check`. Compiler and compatible external libraries were
independently downloaded. Project artifacts were excluded from both combined
import paths; retained predecessor proof bodies were re-elaborated. Lean
4.31.0 and compatible library artifacts remain trusted inputs and were not
rebuilt from source.

The first combined attempt failed because an inherited `Matrix` namespace
opening made a control's unqualified `smul_apply` reference ambiguous. The
corrected proof qualifies that reference as `_root_.smul_apply`; no mathematical
formula or public theorem statement changed. The original sources, checks,
deliveries and pending review are retained under `attempts/r1/`. This report
qualifies the corrected source after its repeated local and fresh-VM checks.

This opens a reusable analytic interface for later variable-potential existence,
residual/forcing estimates, and approximation theory. Those general existence,
rough-data spatial L² evolution, forcing norm estimates, sharper rates, and
variable-potential numerical convergence results are not claimed here. Current
numerical convergence remains specialized to the earlier concrete model.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `b14e205da846e45c0ac506e9319a0f351e5148232ee4fc608193709734cd4788`.
