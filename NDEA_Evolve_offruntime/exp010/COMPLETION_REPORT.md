# Experiment 010 — verified classical infinite Fourier solution

Completed 2026-09-08. All **65 new public theorem/control
audits** passed locally and independently on a fresh Colab CPU VM, with only
`propext`, `Classical.choice`, and `Quot.sound`. All 5 new modules passed
separately.

For coefficient sequences satisfying `A₂=Σ_m (1+|m|)² ‖a_m‖<∞`, the actual
infinite Fourier reference from Experiment 009 now has its time derivative,
first spatial derivative, and second spatial derivative proved. All four
quantities `U`, `Ut`, `Ux`, and `Uxx` are jointly continuous. The solution is
periodic with period `2π` and satisfies `iUt=-Uxx+(Z+X)U` pointwise.
The actual derivative exchanges are derived from summable uniform bounds.

The theorem `infiniteSolution_classical` constructs an explicit predicate with
derivative-existence fields. An exact control supplies coefficients nonzero at
every signed frequency, satisfying the regularity condition and producing a
classical solution. This applies beyond finite Fourier sums.

The new grid endpoints compare the numerical iterate with pointwise samples of
this classical solution. With the predecessor's cutoff, grid and step restrictions,

```text
e_N ≤ e_0 + √(2π) [ T(Ct(M)k²+Cs(M)h²)A + 2A₂/(M+1)² ],
A=Σ_m ‖a_m‖, Ct(M)=1000(M²+2)³, Cs(M)=M⁴/8.
```

The required restrictions are `M≥1`, `d>2M`, `dh=2π`, `h>0`, `Mh≤1`,
`k≥0`, `2k(M²+2)≤1`, and `Nk≤T`. The proved schedule
`M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`
gives convergence of sampled error at exactly `T=1` when initial sampled error
tends to zero. Exact sampled initialization is included. The cutoff-dependent
constants remain explicit; no universal second-order mesh rate is claimed.

| Accepted check | Result |
|---|---|
| New modular sources | 5 passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | 65 audits; exit 0; 376.693 seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | 65 audits; exit 0; 282.011 seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly and unchanged during both checks |
| External library hashes | 9,880 agree across environments |
| Evidence transfer | 89 payload hashes verified; uploaded inputs and compiler audits matched |
| Earlier experiments | Sealed predecessor manifests and the latest Exp009 ZIP preserved |

The fresh CPU session is `exp010-independent-check`, with an initially empty
project workspace at `/content/exp010_check`. Its compiler and libraries were
downloaded independently. No project build artifacts were uploaded or available
on either final combined import path. The predecessor proof bodies retained in
the frozen Experiment 009 combined source were re-elaborated.

Lean 4.31.0 and compatible compiled external libraries remain trusted inputs.
The checks pin compiler/source revisions and compare artifact hashes; they do
not rebuild Lean or Mathlib or prove source-to-artifact correspondence.

Supporting [floating-point diagnostics](NUMERICAL_DIAGNOSTICS.md) compare
analytic derivatives with centered finite differences, bound omitted Fourier
derivative tails, check the PDE, and reject wrong signs and omitted potentials.
Their analytic truncation estimates do not certify floating-point roundoff.

The second weighted absolute moment is a sufficient regularity hypothesis.
Variable spatial potentials, uniqueness, interpolation convergence, rougher
coefficient classes, and universal second-order rates for arbitrary infinite
data remain outside the result.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `fb7b27b42d0baaca9ab8b30f9ba80bb0a5b8999986342fe8538e880bb3947ef0`.
