# Pinned external reuse assessment

Reference: `openai/NavierStokesAndEuler` at
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` (the observed upstream main is unchanged).
The complete 2,496-file, 32,461,273-byte tracked snapshot is outside routine NDEA
snapshots at `/home/richman954/NDEA_External/navier-stokes-euler/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.
Every tracked blob was read and compared with its Git object ID; a complete
SHA-256 catalog accompanies the clean checkout and strict Git fsck receipt.
See `SOURCE_MANIFEST.json` for hashes, location, retrieval time and all dependencies.

Upstream requires Lean 4.34.0-rc2, Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, and Comparator
`19e111e2141cf333c7daff0f64c5f24acc91dd2e`. NDEA remains on Lean 4.31.0,
Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. No upstream build or
downloaded artifact was used in NDEA. `UPSTREAM_LICENSE.txt` preserves the
Apache-2.0 license; individual source notices remain in the untouched checkout.

## Ranked candidates (three, based on inspected proofs)

| Rank / declaration | Exact statement and assumptions | Current consumer and decision |
|---|---|---|
| 1. `NavierStokes.SmoothFourierData.unitCoeff_eq_integral` | For any `f : ℝ → ℂ`, `n : ℤ`, the unit-period coefficient is `∫₀¹ fourier (-n) x * f x`. No regularity or periodicity premise. | **Adapt the proof pattern through pinned Mathlib**, without importing upstream code. Test a physical-period, spinor-valued continuum coefficient interface and prove its value on our actual finite DFT reconstruction. This is the concrete coefficient representation bridge needed by later spatial alias/tail analysis. It is distinct from the already accepted finite-grid Parseval/isometry theorem. |
| 2. `NavierStokes.SmoothParameterIntegral.hasFDerivAt_integral_jet` | Let `jet F k x t = iteratedFDeriv ℝ k (fun y => F y t) x`. Assume a.e. C∞ parameter slices, a.e.-strong measurability of every jet at every point, and for every order and center an integrable majorant on a parameter ball uniform in the integration variable. Then the derivative of the integrated kth jet is the curry-left map of the integrated (k+1)st jet. | **Defer.** Potential later smooth-core/Duhamel consumer, but no current missing finite-regularity obligation. `contDiff_integral` and `iteratedFDeriv_integral` prove smoothness and all-order interchange from the same premises. They do not supply mesh-uniform derivative bounds. |
| 3. `NavierStokes.PeriodicIntegration.cubeIntegral_partial_eq_zero` | For a real-valued C¹ function on real Euclidean 3-space, unit-periodic in each coordinate, the unit-cube integral of any actual coordinate partial derivative is zero. Its IBP companion requires both factors C¹ and unit-periodic. | **Use existing pinned Mathlib / sealed NDEA instead.** The current one-dimensional complex/Hilbert energy cancellation is already proved in Exp013 `GenericEnergy`; importing cube geometry removes no current obligation. |

Candidate 1 details: the upstream proof uses
`fourierCoeffOn_eq_integral`, already present in pinned Mathlib
`Analysis/Fourier/AddCircle.lean:356`, and supports complex normed-space values.
The smallest useful dependency closure is that Mathlib API and our accepted
`FourierNorm` / `FourierReconstruction`; importing the upstream file would also
pull in `TorusInverse → DiophantineGraph` and unrelated two-dimensional theory.
Our adaptation uses period 2π directly, normalized coefficient `(2π)⁻¹ ∫`,
kernel `exp(-inx)`, and `E 2` values; the exact phase/normalization identity must
be proved. It does not silently identify sampled coefficients of an arbitrary
smooth function with its continuum coefficients. The equality is first proved
for the actual finite reconstruction. Expected cost: a small bridge module,
with no smoothness assumptions beyond those proved for that finite sum.

Also inspected in `SmoothFourierData`:

- `unitCoeff_norm_le`: only `∀ x ∈ Icc 0 1, ‖f x‖ ≤ C`, giving
  `‖unitCoeff f n‖ ≤ C`. This is the integral formula plus pinned
  `intervalIntegral.norm_integral_le_of_norm_le_const`; there is no new primitive
  to import.
- `unitCoeff_of_hasDerivAt`: `n ≠ 0`, `∀ x, HasDerivAt f (f' x) x`,
  `Continuous f'`, and `f 1 = f 0`, giving
  `unitCoeff f n = (2π i n)⁻¹ * unitCoeff f' n`. It wraps pinned
  `fourierCoeffOn_of_hasDerivAt` (`AddCircle.lean:595`), whose hypotheses can
  actually be restricted to the interval and interval-integrable derivative.
  For period 2π the multiplier is `(in)⁻¹`. Scalar derivative decay is a later
  consumer; spinors/operators need the appropriate extension. One derivative
  does not establish Exp014's second-weighted absolute summability. A stronger
  four-derivative sufficient theorem must be labeled separately from our
  existing baseline and still needs reconstruction/alias estimates.

Candidate 2 dependency closure is one 315-line project file and four Mathlib
imports (`ParametricIntegral`, `IteratedDeriv.Defs`, `ContDiff.Comp`,
`IntervalIntegral.Basic`). Parameter/codomain are generic real normed spaces;
complex Hilbert codomains may use their real structure. Compact-interval
convenience results require `ProperSpace` of the parameter space. Pinned Mathlib
already supplies the dominated first derivative and jet currying primitives;
there was no equivalent all-orders wrapper in the searched sources. Adapting
the induction could help later, but proving its majorants remains the main
obligation. Upstream's explicit `WithTop ℕ∞` order arguments are not our pinned
`ℕ∞` API and need changes. Do not raise our regularity target to C∞ to fit it.

Candidate 3 dependency closure is `PeriodicIntegration` plus `ProblemStatement`
(496 lines), with seven Mathlib boundary imports. It uses the box divergence
theorem on a one-component vector field and cancellation of opposite faces,
then the product rule. Our interval FTC/IBP APIs work directly in one dimension;
no 3D real cube → 1D complex rescaling port is justified.

## Exact theorem scope and independent target checking

The release's Navier–Stokes adapters quantify over a **smooth force** as well
as initial data, for each positive viscosity. They exclude global solutions
in the precise challenge classes; they are not a result about unforced
Navier–Stokes. Euler's solution adapter uses zero force and zero viscosity.
`ComparatorR3Theorem` imports `R3FiniteEnergyComparison` and `R3ActualCandidate`;
`ComparatorTheorem` imports `ComparatorBridge`, `ActualCandidateAssembly` and
`CandidateConsequences`. Their conversions retain the challenge's force,
initialization, space/time order, periodicity and global-solution quantifiers.
The inspected manuscript's Theorem 1.1 (PDF page 1) explicitly uses a smooth
compactly supported force; page 3 explains the residual construction. Residual
smoothness alone says nothing about NDEA's vanishing numerical residual.

The challenge files intentionally contain `sorry`. Their solution adapters
import separate `ComparatorDefinitions`, not the challenge declarations. Both
JSON challenges permit only `propext`, `Classical.choice`, `Quot.sound` and
request nanoda. Configuration is not evidence that any check ran here.

Pinned Comparator README was inspected at its dependency revision, including
the trusted-challenge boundary, dependency comparison, export/replay, Landrun
isolation and its documented Unix-socket mitigation. No appropriately checked
isolated unprivileged credential-free Comparator environment has been prepared
here. **Comparator: not run. Additional independent kernel: not run.** No fake
sandbox or root development runtime is substituted. Upstream Lean build: not
run. The compact earlier readback records the exact Comparator README hash.

The useful practice is already applied: `IndependentTarget.lean` defines raw
ordered Cayley/Fourier/quadratic objects without importing their Exp016
implementation; `TargetBinding.lean` proves exact agreement and the actual
partial-slab error bound. `ActualCayleyCertificate.lean` proves the finite
trajectory and partial final slab against that target. The independent review
document fixes grid, potential, initialization, normalization, all defects and
eventual refinement quantifiers. The full convergence target remains unproved.
Here “independent target” means statement/proof separation, not separate
institutional authorship or an independent kernel run.

Ordinary source-bound development Lean checks and transitive `#print axioms`
checks for these target/certificate declarations passed with the three standard
axioms. Full isolated combined and fresh independent Exp016 qualification have
not run. The reference challenge placeholders stay outside production imports.

## Manuscript and status

`MANUSCRIPT_MANIFEST.json` records one successful download, SHA-256, strict PDF
parse and searchable text for all 166 pages. References use one-based PDF page
numbers. PDF/text are external supporting references, not public Git content;
redistribution permission has not been established.

Acquired: complete pinned source and manuscript. Inspected: the requested
declarations/proofs, challenge definitions and adapter imports, dependency pins
and relevant trust documentation. No upstream build, Comparator or nanoda run.
Candidate 1's transfer is development-accepted in `lean/FourierCoefficientBridge.lean`.
The theorem `physicalFourierCoefficient_reconstruction` identifies the normalized
continuum coefficient of the actual reconstructed field with its computed DFT
coefficient. The off-band theorem proves zero for frequencies outside the retained
range. These are exact representation results, not coefficient-decay or alias-error
estimates. Candidates 2 and 3 are not ported.

Accepted source SHA-256:
`0b550fad136360d5bbb2f9c68f595cf5a2f274a33c0f1bd393cb3b9c50d44918`.
Receipt: `evidence/remote_development/2026-09-09T130009.044711_0000_FourierCoefficientBridge/RESULT.json`,
SHA-256 `0bab210adf0b5ce26130de4c9e62bdc9b85e652511627c1572277cbc44ea7647`.
Exit 0 in 7.100 seconds, no warnings, four transitive axiom reports containing
only propext/Classical.choice/Quot.sound; sources/import artifacts unchanged.
The result archive and matching artifact passed SHA-256/CRC/readback validation.
The helper proofs are included in the public declarations' transitive axiom checks.
This is ordinary Lean development acceptance, not fresh isolated qualification.

The direct imports are accepted NDEA `FourierNorm` and pinned Mathlib
`Analysis.Fourier.AddCircle`; no external fluid module or upstream compiled
artifact enters the proof closure. The 228 restored Mathlib cache artifacts were
individually compared with the local pinned artifacts. Earlier connection,
cache-import, lock-handoff and period-elaboration failures are retained separately;
none is counted as mathematical acceptance. See the companion transfer note for
provenance, assumptions and reproducible checking instructions.

The next dependency-ordered Exp016 result also passed:
`NDEAEvolve.Exp016.sampledCayley_gridTime_error` and
`NDEAEvolve.Exp016.sampledCayley_partialSlab_error` in SampledCayleyCertificate instantiate
actual matrix samples, centered stencil and ordered trajectory, preserving
arbitrary initial mismatch and positive variable steps. No free matrix
compatibility premise or assumed residual bound is added. Remaining obligations
include the separate stencil/potential alias decomposition and bounds uniform
under refinement; the total convergence target is not claimed.
