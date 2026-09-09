# Experiment 011 — verified reconstructed space-time convergence

Completed 2026-09-08. All **44 new public theorem/control
audits** passed locally and independently on a fresh Colab CPU VM, with only
`propext`, `Classical.choice`, and `Quot.sound`. All 5 new modules passed
separately.

The actual numerical grid iterates now define a reconstructed spinor field
throughout the closed rectangle `[0,1] × [0,2π]`. Under
`A₂=Σ_m (1+|m|)² ‖a_m‖<∞` and exact sampled initialization, these fields
converge uniformly to Experiment 010's classical solution of
`iUt=-Uxx+(Z+X)U`.

The reconstruction uses the explicitly clamped indices `floor(t/k)` and
`floor(x/h)` and extracts both spin components from the actual split Cayley
iterate. At the right spatial endpoint it takes the last grid node. The
finite fields may be discontinuous and need not agree at the two spatial
endpoints; the periodic classical target and the uniform error estimate cover
that endpoint discrepancy.

The schedule is `M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`.
It reaches time one exactly and satisfies the predecessor's mesh, band and
step restrictions. Writing `r=1/M`, the derived bound is

```text
‖R_q(t,x)−U(t,x)‖ ≤
  A₂ * [(1000/36)(1+2r²)³ + π²/128 + 2] * sqrt(8r)
  + A₂*h + 2*A₂*k.
```

The bound holds for every point of the rectangle and tends to zero. Its grid
term comes from a bound valid for every scheduled time step, divided by
`sqrt(h)` using the proved node-extraction contraction. The other two terms
come from proved global spatial and time norm difference bounds for the
actual classical solution. No reconstruction error or derivative-exchange
premise is assumed.

| Accepted check | Result |
|---|---|
| New modular sources | 5 passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | 44 audits; exit 0; 420.470 seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | 44 audits; exit 0; 304.076 seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly and unchanged during both checks |
| External library hashes | 9,880 agree across environments |
| Evidence transfer | 89 payload hashes verified; uploaded inputs and compiler audits matched |
| Earlier experiments | Sealed predecessor manifests and the Exp010 ZIP preserved |

The independent CPU session is `exp011-independent-check`, with an initially
empty project workspace at `/content/exp011_check`. Its compiler and libraries
were downloaded independently. No project build artifacts were uploaded or
available on either final combined import path. The predecessor proof bodies
retained in the frozen Experiment 010 combined source were re-elaborated.

Lean 4.31.0 and compatible compiled external libraries remain trusted inputs.
The checks do not rebuild Lean or Mathlib or prove source-to-artifact
correspondence.

Supporting [numerical diagnostics](NUMERICAL_DIAGNOSTICS.md) exercise off-grid
space/time reconstruction and the stated endpoint convention, with explicit
Fourier truncation qualifications. Floating-point tests do not replace the
formal uniform convergence theorem or certify roundoff.

Exact sampled initialization is part of this result. Merely vanishing initial
weighted error is insufficient for the inverse-norm argument without further
control. The displayed bound is conservative; no sharp uniform rate,
uniqueness theorem, spatially varying potential, weaker-data theorem, or
universal PDE guarantee is claimed. The unverified energy-uniqueness probe is
retained only as a future-work note and is excluded from production sources.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `6e516d1a5cbd1eae23feddcb9b26a29c12a15a6a0d45928c891acd9be453e3e5`.
