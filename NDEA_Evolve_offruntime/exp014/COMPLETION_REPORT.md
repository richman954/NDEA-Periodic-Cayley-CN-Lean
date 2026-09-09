# Experiment 014 — global regular variable-potential PDE existence

Completed 2026-09-09. All **143 public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM.
All 9 new modules passed separately. Only `propext`,
`Classical.choice`, and `Quot.sound` appear in the audited axiom dependencies.

For any complete complex Hilbert space H, let w(m)=(1+|m|)^2. Assume initial
coefficients a(m) and bounded operator coefficients v(j) satisfy

```text
Σ_m w(m) ‖a(m)‖ < ∞,       Σ_j w(j) ‖v(j)‖ < ∞,
v(-j) = v(j)*,              V(x) = Σ_j exp(i j x) v(j).
```

There exists exactly one global classical 2π-periodic solution of

```text
i u_t = -u_xx + V(x)u,       u(0,x) = Σ_m exp(i m x) a(m),
```

for every real time. The construction uses all integer Fourier modes without
a finite cutoff.
Its actual first time and first/second spatial derivatives satisfy the PDE,
with the joint continuity and periodicity required by Experiment 013's
classical predicate. Uniqueness ranges over that entire classical solution
class, without a Fourier-representation assumption on a competing solution.

The proof builds bounded weighted convolution, a strongly continuous free
isometric group and an all-real-time Dyson evolution in the interaction
picture. Bounded synthesis and a strong-operator product rule identify the
actual PDE derivatives. No commutation of V with the Laplacian, finite fiber
dimension, operator-norm continuity of the free group, or finite cutoff is
assumed. The exact controls exercise an active variable potential, initial
conditions and infinite-support regular data; their accepted statements are
in [Controls.lean](lean/Controls.lean).

| Accepted check | Result |
|---|---|
| New modular sources | 9 passed |
| Local combined source | 143 audits; exit 0; 178.418 seconds |
| Independent combined source | 143 audits; exit 0; 87.154 seconds |
| Source/catalog | Exactly reconstructed; unchanged during both checks |
| External artifact hashes | 10,768 agree across environments |
| Evidence transfer | 96 payload hashes and all compiler audits verified |
| Predecessors | Sealed manifests and Exp013 packet preserved |

The distinct CPU session is `exp014-independent-check`, initially empty at
`/content/exp014_check`. The pinned compiler and compatible external libraries
were independently downloaded. Both combined checks exclude project artifacts
from their import paths. They re-elaborate the exact retained Exp013 generic
classical, energy and uniqueness bodies alongside the new source; the older
numerical chain is preserved and is not part of this combined check. Lean
4.31.0 and compatible compiled library artifacts are trusted inputs and were
not rebuilt from source.

This closes classical existence and uniqueness for the stated regular linear
periodic class. Rough L² data, nonlinear equations, time-dependent potentials,
other boundaries and numerical convergence for this enlarged class remain
separate extensions. It does not claim existence for arbitrary PDEs.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee`.
