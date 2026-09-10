# Recovered pinned reference and useful transfer

Post-reboot readback, September 9, 2026 UTC. The requested acquisition and
concrete transfer had already completed before this restart. Their accepted
bytes were recovered and checked; no completed Lean check was repeated.

The [source manifest](SOURCE_MANIFEST.json) identifies the exact commit
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`, originally retrieved at
2026-09-09T12:10:10.915750+00:00. Its SHA-256 is
`b760993391a46afafc2aabe5922720745f9bedab99592b7551a282eabb1496c4`.
The complete checkout remains at
`/home/richman954/NDEA_External/navier-stokes-euler/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.
Fresh readback checked all 2,496 tracked files, 32,461,273 bytes, their SHA-256,
sizes and Git blob IDs, the exact tree, clean checkout and strict Git fsck.
Upstream HEAD/main still names that same revision; no newer source was substituted.
See the [compact readback receipt](../../evidence/reboot_20260909T233900Z/REFERENCE_RECOVERY_SUMMARY.json),
which binds the complete local readback record.

The tracked README, formalization.yaml, license, toolchain, Lake configuration,
all dependency revisions, NavierStokes/, Euler/ and ComparatorChallenges/ are
preserved. Upstream uses Lean 4.34.0-rc2, Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, and Comparator
`19e111e2141cf333c7daff0f64c5f24acc91dd2e`. NDEA retains Lean 4.31.0 and Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The Apache-2.0 license and original
per-file notices remain intact; no upstream executable or compiled artifact was
introduced into NDEA.

The [manuscript manifest](MANUSCRIPT_MANIFEST.json) records the successful prior
download, strict PDF parsing and searchable text for all 166 pages. Both files
still match their hashes. PDF SHA-256:
`0e779481c4da40bd28d1e642e1d8ca57447d129610df28dfa5a11e9af8ae228f`.
Page references in the saved review use one-based PDF page numbers; text has
explicit page separators. No new mathematical claim here depends on the PDF.
Redistribution permission is not established; PDF/text stay outside public Git
and routine NDEA snapshots.

## Ranked reuse decisions

The [full three-candidate map](REUSE_MAP.md) records statements, assumptions,
dependency closures, existing APIs and adaptation costs. The current decisions
remain:

| Rank | Upstream declaration and assumptions | NDEA consumer and decision |
|---|---|---|
| 1 | `NavierStokes.SmoothFourierData.unitCoeff_eq_integral`: for any `f : ℝ → ℂ`, `n : ℤ`, the unit-period coefficient equals `∫₀¹ fourier(-n,x)*f(x) dx`; no regularity premise. | Adapted via pinned Mathlib's existing `fourierCoeffOn_eq_integral`, using period 2π and vector scalar action. Exact continuum extraction for the actual DFT reconstruction is accepted. Small closure: Mathlib AddCircle plus accepted NDEA FourierNorm; no fluid-specific imports. |
| 2 | `NavierStokes.SmoothParameterIntegral.hasFDerivAt_integral_jet`: real normed parameter/codomain spaces, a.e. C∞ parameter slices, measurable jets at all orders/points and locally uniform integrable majorants at every order. The derivative is the curry-left map of the integrated next jet. | Defer. A later smooth-core parameter-integral proof might use its induction pattern; it supplies neither majorants nor mesh-uniform regularity. Existing Mathlib dominated differentiation is sufficient for finite-order needs. Porting the full wrapper would impose unjustified C∞ assumptions and require adapting the newer derivative-order API. |
| 3 | `NavierStokes.PeriodicIntegration.cubeIntegral_partial_eq_zero`: real-valued C¹ function on real Euclidean 3-space, unit periods in all coordinates; each actual coordinate partial integrates to zero on the unit cube. | Reuse existing NDEA/Mathlib cancellation. Exp013 already proves the relevant one-dimensional Hilbert-valued energy boundary cancellation. Porting box geometry, real coordinates and unit periods removes no current obstacle. |

`unitCoeff_norm_le` and `unitCoeff_of_hasDerivAt` were also inspected. Their
integral-bound and integration-by-parts primitives already exist in pinned
Mathlib. Unit-period derivative coefficients use `(2π i n)⁻¹`; physical period
2π uses `(i n)⁻¹`. These facts are separate from Parseval/isometry, which NDEA
had already proved. Neither scalar derivative decay nor a C∞ wrapper proves
the unresolved evolved spatial-tail bound.

No secondary FourierAlias or gluing module was ported. Upstream alias names do
not identify grid sampling aliases, and finite regular polynomial slabs already
meet the needs of the slabwise Exp015 argument.

## Concrete accepted transfer and present consumer

[FourierCoefficientBridge.lean](../../lean/FourierCoefficientBridge.lean) retains
the upstream declaration, commit, license attribution and a description of all
changes. Its general coefficient formula proves the explicit factor `(2π)⁻¹`
and equality of Mathlib's character with NDEA's `phase(-n*x)`. It specializes
the period directly; it does not assume an unproved unit-period rescaling.
The integral formula allows complex normed-space values; mode integration uses
completeness, and the actual finite-grid consumer is the spinor space `E 2`.

The accepted theorem
`NDEAEvolve.Exp016.physicalFourierCoefficient_reconstruction` says that the
normalized continuum coefficient of `fourierReconstruction M h y` at
`oddFrequency M m` is exactly `fourierCoefficient M h y m`. Its off-band
corollary is zero. Node fidelity requires the separately proved mesh relation;
the coefficient extraction identity itself holds for the actual finite sum.

The [original transfer receipt and reproduction guide](../FourierCoefficientBridge_TRANSFER.md)
record exit 0 in 7.100 seconds, four transitive axiom reports using only
`propext`, `Classical.choice`, `Quot.sound`, zero warnings/errors, unchanged
source/import artifacts and validated evidence transfer. Source SHA-256:
`0b550fad136360d5bbb2f9c68f595cf5a2f274a33c0f1bd393cb3b9c50d44918`.
Receipt SHA-256:
`0bab210adf0b5ce26130de4c9e62bdc9b85e652511627c1572277cbc44ea7647`.
Fresh recovery readback confirmed the exact source, compiler log, receipt and
installed artifact. This is recovered modular acceptance, not a new proof run
or independent combined qualification.

The obstacle removed was the missing identification of continuum Fourier
coefficients with coefficients of the actual numerical reconstruction.
`WeightedCoefficientBridge.physicalFourierCoefficient_weightedSynthesis` and
`physicalFourierCoefficient_potentialProduct` (both in namespace
`NDEAEvolve.Exp016`) already consume this API for Exp014 synthesis and its
actual potential convolution. This makes the continuum side available for
comparison with discrete sampling aliases. It does not itself prove evolved
tail control or refinement. No additional port is justified merely to produce
another transfer result.

## Independent target checking

The pinned Comparator documentation and challenge/solution adapters were
reviewed. The reference intentionally has two `sorry` challenge theorems;
solution adapters import separate ComparatorDefinitions. The exact adapters
retain force, viscosity, initial-data, time/space-order and solution-class
quantifiers. No upstream headline theorem was compiled here.

[IndependentTarget.lean](../../lean/IndependentTarget.lean) specifies raw DFT,
quadratic slabs and ordered A-half/B-full/A-half action using sealed numerical
APIs without importing the Exp016 implementation. TargetBinding and the actual
sampled trajectory certificates prove implementation agreement. The
[independent target document](../INDEPENDENT_TARGET_SPEC.md) fixes physical
norm, potential/initialization, all defects and eventual refinement quantifiers.
The raw Lean definition layer does not yet constitute a separate Comparator
challenge for the entire convergence theorem. That theorem remains unproved.

| Check | Actual status |
|---|---|
| Reference specification and pinned adapter source | Reviewed |
| NDEA adapter ordinary Lean check | Passed at its saved exact source |
| NDEA adapter transitive axiom audit | Passed; four reports, standard three only |
| Full upstream Lean build | Not run |
| Comparator | Not run |
| Additional independent kernel | Not run |
| Isolated combined/fresh independent Exp016 qualification | Pending |

The current local environment lacks landrun, lean4export and nanoda_bin. No
isolated credential-free checking environment has been prepared. The pinned
README also specifies unprivileged execution, a trusted challenge boundary
and Unix-socket isolation; no weaker substitute was used.

## NDEA continuation

The verified restart recovered 50 accepted development modules, including full-grid
Parseval, actual reconstruction/residual certificates, sampling/alias bounds,
initialization and paired continuum/discrete potential-cutoff stability.
KineticSymbolBound already supplies `‖op(gridKinetic)‖ ≤ 4/h²`. The next
dependency-ordered proof, KineticAssembly, passed locally at its exact source:
`‖op(sampledSplitA (2*M) h)‖ ≤ 4/h²+1`, with `(2*M+1)*h=2π` and `h>0`.
The accepted catalog now has 51 modules. Two new transitive axiom reports
contain only the standard three axioms, with no warnings/errors; no prior
accepted source or import artifact changed. See
[milestone and check receipts](../KINETIC_ASSEMBLY_MILESTONE.md).
Next substitute these actual A/B bounds into the temporal certificate and
prove temporal-budget vanishing under the recorded refinement schedule.
The spatial barrier remains justified smooth-core evolved consistency/tails;
initial L² stability and finite input/potential support do not settle it.

Exp013–015, main and dependency pins remain unchanged. The recovery audit
matched all 1,298 pre-reboot snapshot payloads and 789 sealed predecessor
payloads. Watcher session 27367 produced verified startup and interval saves;
the post-reboot manual checkpoint was published at 23:43:23 UTC. The large
external checkout and PDF remain outside that snapshot scope.
