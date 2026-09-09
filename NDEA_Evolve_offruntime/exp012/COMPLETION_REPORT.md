# Experiment 012 — classical periodic uniqueness

Completed 2026-09-08. All **46 new public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM,
with only `propext`, `Classical.choice`, and `Quot.sound`. All 5 new
modules passed separately.

Any two functions satisfying the unchanged
`Exp010.IsClassicalPeriodicSolution` predicate for
`iUt=-Uxx+(Z+X)U`, period `2π`, and agreeing at a single real time are equal
for every real time and position. This compares arbitrary classical solutions;
a Fourier representation of the competing solution is not assumed.

The proof derives the local identity

```text
∂t ‖u(t,x)‖² = ∂x J(t,x),
J(t,x) = 2 Re ⟨u(t,x), i ∂x u(t,x)⟩.
```

Hermitian symmetry cancels the potential term. Actual differentiability and
periodicity imply periodicity of the spatial derivative and hence of the
flux. A compact time-space rectangle supplies the local majorant needed to
differentiate the energy integral, without any added global time bound.
Thus, for every real base `b` and all real times `s,t`,

```text
∫[b,b+2π] ‖u(s,x)−v(s,x)‖² dx = ∫[b,b+2π] ‖u(t,x)−v(t,x)‖² dx.
```

Equal data at one time make this energy zero. Continuity and positivity of
the integral then force equality at each spatial point. Allowing arbitrary
interval bases covers all real positions directly, including interval endpoints.

For initial data from Fourier coefficients with
`Σ_m (1+|m|)² ‖a_m‖ < ∞`, there exists exactly one solution in this classical
class. Experiment 011's actual reconstructed numerical fields converge
uniformly to that unique solution on `[0,1] × [0,2π]`, with the same explicit
error bound, exact sampled initialization and refinement schedule.

| Accepted check | Result |
|---|---|
| New modular sources | 5 passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | 46 audits; exit 0; 454.824 seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | 46 audits; exit 0; 287.927 seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly and unchanged during both checks |
| External library hashes | 10,688 agree across environments |
| Evidence transfer | 89 payload hashes verified; uploaded inputs and compiler audits matched |
| Earlier experiments | Sealed predecessor manifests and the Exp011 ZIP preserved |

The independent CPU session is `exp012-independent-check`, initially empty at
`/content/exp012_check`. Its compiler and libraries were downloaded
independently. Project build artifacts were excluded from both final combined
import paths. The retained predecessor proof bodies were re-elaborated.
Lean 4.31.0 and compatible compiled external libraries remain trusted inputs;
Lean and Mathlib themselves were not rebuilt from source.

The [exact controls](lean/Controls.lean) exercise nonzero data, necessity of
matching data, zero-data uniqueness, matching at a shifted time, and the flux
sign. This analytic milestone uses formal controls; no additional
floating-point simulation is treated as evidence of uniqueness.

Uniqueness holds within the specified global classical periodic class.
Existence for rougher data, spatially varying potentials, nonperiodic boundary
conditions and sharp numerical rates remain outside this result. The sign
convention above is `∂tρ=∂xJ`; `J` is the negative of the current in
`∂tρ+∂xj=0`.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `ff98d87926fe6729202d77119d84e3ff3b3a3664ab607c0069a52db2c9f8547d`.
