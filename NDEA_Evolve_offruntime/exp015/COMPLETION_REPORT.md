# Experiment 015 — quantitative forcing and residual stability

Completed 2026-09-09. All **50 new public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM.
All 7 new modules passed separately. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in the audited axiom dependencies.

For positive spatial period L and any origin b, define the spatial L2 norm as
the square root of the integral of the squared Hilbert norm over [b,b+L]. Classical periodic
Schrödinger fields u and v with a common pointwise selfadjoint potential and
jointly continuous forcing difference satisfy, for s <= t,

```text
||u(t)-v(t)||L2 <= ||u(s)-v(s)||L2 + integral_s^t ||f(r)-g(r)||L2 dr.
```

The estimate keeps the full initial error and has coefficient one in front
of the forcing integral. The proof derives the squared-error derivative from
Exp013's exact energy identity and uses positive square-root regularization
to include vanishing error. Spatial integral and continuity prerequisites
are proved under the stated hypotheses.

A regular approximate field is assigned its actual PDE residual
`i*u_t + u_xx - V*u`. Applying the same estimate turns residual size and
initialization error into an L2 error bound, with joint continuity of the
residual-minus-forcing difference required explicitly. A jointly continuous
operator potential supplies residual continuity from field regularity.
The variable-potential bridge
specializes this result to the unique global regular solution constructed in
Exp014. The exact theorem statements specify all field, period, potential
and forcing regularity assumptions; see the [derivation](MATHEMATICAL_DERIVATION.md)
and [controls](lean/Controls.lean).

| Accepted check | Result |
|---|---|
| New modular sources | 7 passed |
| Local combined source | 50 audits; exit 0; 297.277 seconds |
| Independent combined source | 50 audits; exit 0; 109.771 seconds |
| Source/catalog | Exactly reconstructed; unchanged during both checks |
| External artifact hashes | 10,768 agree across environments |
| Evidence transfer | 92 payload hashes and all compiler audits verified |
| Predecessors | Sealed predecessor manifests and Exp014 packet preserved |

The separate CPU session is `exp015-independent-check`, initially empty at
`/content/exp015_check`. The pinned compiler and compatible external libraries
were independently downloaded. Both combined checks exclude project artifacts
from their import paths. They re-elaborate the exact sealed Exp014 combined
proof bodies, including its generic Exp013 foundation, alongside the new source.
Only the 143 prior axiom-print commands are removed from that foundation; the
new audit catalog covers Exp015 declarations only. Earlier numerical proof
chains remain preserved in their accepted packets. Lean 4.31.0 and compatible
compiled library artifacts are trusted inputs and were not rebuilt from source.

This is a continuous PDE stability and residual-to-error milestone. Convergence
of actual discrete iterates or reconstructed numerical fields, discrete
consistency bounds, refinement schedules and numerical convergence rates for
the enlarged variable-potential class require additional work.

Read [review](REVIEW.md), [reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).
Combined SHA-256: `ef99d7098209d790f32abf89e2ec866e1b3c0cb2ce5b4262022df3cfdbf18846`.
