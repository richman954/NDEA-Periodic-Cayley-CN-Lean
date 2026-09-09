# Experiment 009 — verified infinite Fourier reference and growing cutoff

Completed 2026-09-08. Local and independent Colab combined checks
passed all **70 new public theorem/control audits** with only
`propext`, `Classical.choice`, and `Quot.sound`. All 7 new modules passed
separately. This extends the finite-spectrum reference of Experiment 008 to
coefficients with `A=Σ_m ‖a_m‖<∞`.

The actual infinite reference is
`U(t,x)=Σ_m exp(imx) exp[-it(m²I+Z+X)]a_m`. Its series converges absolutely;
periodicity, initial value, and equality between its samples and the infinite
grid series are proved. The split grid matrices remain the actual noncommuting
centered-difference spinor scheme from the earlier experiments.

For `τ_M=Σ_{|m|>M}‖a_m‖`, the new theorem derives

```text
e_N ≤ e_0 + √(2π) [ T(Ct(M)k²+Cs(M)h²)A + 2τ_M ],
Ct(M)=1000(M²+2)³, Cs(M)=M⁴/8.
```

Both errors compare against the full infinite reference. The two tails arise
at the initial and final times; arbitrary numerical initialization retains its
full discrepancy. The sampled tail estimate uses absolute summability, allowing
aliasing of omitted frequencies. The retained band must still satisfy `d>2M`.
Other hypotheses are `M≥1`, `dh=2π`, `h>0`, `Mh≤1`, `k≥0`,
`2k(M²+2)≤1`, and `Nk≤T`.

The generic endpoint proves convergence with `M→∞`, vanishing displayed
consistency cost, and vanishing full-reference initial error. A fully proved
schedule is `M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`.
It satisfies every restriction and reaches time `T=1` exactly. Its consistency
cost is `[(1000/36)(1+2/M²)³+π²/128]/M²`, which tends to zero.
Exact sampled initialization therefore gives convergence to the full reference
at that common final time.

For a summable weighted moment `A_r=Σ_m(1+|m|)^r‖a_m‖`, the proof gives
`τ_M≤A_r/(M+1)^r` and inserts this bound into the actual grid-error theorem.
An exact control exhibits summable coefficients nonzero at every integer
frequency, with positive tails beyond every finite cutoff. Coherent sampled
aliases expose the failure of a naive infinite-grid Parseval estimate.

| Accepted check | Result |
|---|---|
| New modular sources | 7 passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | 70 audits; exit 0; 414.878 seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | 70 audits; exit 0; 202.968 seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly, unchanged during both checks |
| External library hashes | 9,868 agree across environments |
| Evidence transfer | 91 payload hashes verified; exact uploaded inputs and compiler audits matched |
| Previous sealed files | All predecessor manifests and both latest original ZIPs preserved |

The Colab check ran on a newly allocated replacement CPU VM, session
`exp009-independent-check`. Its pinned compiler and external libraries were
downloaded independently under `/content/exp009_check`. The earlier
`exp008-fresh-recheck-r2` runtime became unavailable before the Experiment 009
independent proof check; its prepared request and environment records are
preserved in `remote_check/lost_runtime/`. The accepted local proof and earlier
sealed evidence remained intact. No local project build artifacts were
uploaded or available on the final combined import paths. The predecessor
proof bodies retained in the frozen Experiment 008 combined source are
re-elaborated.

Lean 4.31.0 and compatible compiled external libraries remain trusted inputs.
The checks pin compiler/source revisions and compare artifact hashes; they do
not rebuild Lean or Mathlib or prove source-to-artifact correspondence.

Supporting floating-point diagnostics exercise genuine signed infinite
geometric data, exact closed-form sampled initialization, a terminal reference
with an explicit analytic omitted-tail bound, both endpoint tails, perturbed
initialization, the growing schedule, wrapped-grid identities, and coherent
aliasing controls. See [numerical details](NUMERICAL_DIAGNOSTICS.md) and
[data](evidence/numerical_checks.json). The truncation estimate does not certify
floating-point roundoff.
The [convergence figure](evidence/exp009_convergence.pdf) plots these accepted
diagnostics, with its input, script, and output hashes checked.

Absolute summability alone gives this Fourier evolution reference and sampled
grid convergence. Classical time and second-space derivatives of the infinite
series have not been proved here. Spatially varying potentials, numerical
interpolation, and a universal second-order rate for arbitrary infinite data
remain outside the result. The Fourier tail may decay slowly.

See [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `8cbf781d91f3cd0cc5f6669586c55a4c4613d6f3e9f322e10fbafff39991e8c8`.
