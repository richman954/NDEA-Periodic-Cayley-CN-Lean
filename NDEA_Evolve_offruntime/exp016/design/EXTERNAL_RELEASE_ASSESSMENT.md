# Bounded read-only assessment — 2026-09-09

Conclusion: **useful now for independent target specification; no outside mathematical code adopted.** Exp016 continues its existing quadratic/Fourier certificate. This was source inspection, not an external build or an independent validation of the release.

Inspected `openai/NavierStokesAndEuler` commit `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` (2026-09-08). Eighteen selected repository files were read back against their exact Git blob hashes in the separate directory `/home/richman954/NDEA_External_Inspection/NavierStokesAndEuler_8937a8f4`; `READBACK_RECEIPT.json` records SHA-256 values. No external Lean code was executed, added to NDEA imports, or built. The pinned Comparator README was also inspected separately.

## Exact scope and trust boundary

- `NavierStokes.Comparator.navier_stokes_breakdown_R3`: for every positive viscosity, there exist admissible initial velocity **and a smooth external force**, with rapid derivative decay, for which no global smooth solution exists in the stated whole-space finite, uniformly bounded energy class.
- `NavierStokes.Comparator.navier_stokes_breakdown_periodic`: for every positive viscosity, there exist admissible periodic data and smooth periodic, time-decaying force with no global smooth periodic velocity/pressure solution. These statements do **not** set the force to zero and do not resolve the unforced Navier–Stokes question.
- `Euler.euler_breakdown_R3` explicitly uses zero viscosity and zero external force, with no global smooth solution in the stated whole-space energy class.
- `Euler.exists_compact_smooth_euler_singularity` additionally specifies nonzero compact smooth data, a positive maximal lifespan at most one, local bounds below it, and infinite endpoint C1 limsup/vorticity integral. Its finite-lifespan maximality is in the separately defined all-order Sobolev class; the broader global nonexistence clause is retained separately.

The challenge files import only Mathlib and contain intentional theorem placeholders. The solution roots instead import their own definition/bridge modules, expose the challenge theorem statements, and print their axiom dependencies. Both Comparator JSON files list only `propext`, `Quot.sound`, and `Classical.choice`, enable nanoda, and have no definition-hole configuration. The release metadata reports those dependencies and labels review self-assessed. These are inspected declarations/configuration and reported status, **not a new executed Comparator receipt from this assessment**.

Comparator commit `19e111e2141cf333c7daff0f64c5f24acc91dd2e` describes comparing the transitive statement definitions, restricting proof axioms, and replaying the solution into Lean and optional external kernels. It still requires a trustworthy target/import closure and appropriate build/export isolation; its README identifies system-specific sandbox requirements. We do not equate another fresh run of the same compiler with a distinct kernel implementation.

Release pins: Lean `v4.34.0-rc2`; Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`; Comparator as above; lean4export `cacf989bd75f608700820f6afc595f32e7a99a4d`. NDEA remains on Lean `v4.31.0`, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Installing/porting Comparator is deferred until it has a bounded, compatible verification use; the specification discipline can be adopted immediately.

## Mathematical code screening

No screened outside lemma removes a current missing obligation more cheaply than the pinned NDEA/Mathlib route. At most two concrete examples were evaluated:

| Screened declaration at the release commit | Actual assumptions and scope | NDEA consumer / decision |
|---|---|---|
| `NavierStokes.FourierAlias.periodic_integral_translate` | Real normed target, a period-one function; translates its actual interval integral | Could support changing the base point of a periodic norm, but directly wraps Mathlib's `Periodic.intervalIntegral_add_eq`. It does not remove our discrete Parseval or consistency obligation. Reuse pinned Mathlib if needed; do not import this module. |
| `EulerLpTranslation.cutoffDerivativeLp_tendsto` | Smooth whole-space field and both field/actual derivative in L2; spatial compact-support cutoffs | A possible later whole-space extension reference. It is not periodic Fourier truncation, grid sampling, or propagation of high-frequency bounds, so it does not discharge NDEA's current initialization/aliasing obligations. No port now. |

The release's `FourierAlias` handles a radial transport compactification defect; the name alone does not make it a DFT potential-aliasing estimate. Its frequency lemmas use the release's special chart scales. No claimed NDEA refinement bound follows from them.

## Adopted change with a current consumer

A separate reviewer specifies the intended actual recurrence, reconstruction, certificate and refinement quantifiers in `INDEPENDENT_TARGET_SPEC.md`, without treating the implementation's convenient hypotheses as the target. A small independent Lean reconstruction contract will be connected by an explicit theorem to the current Fourier/quadratic implementation. The complete certificate-to-target and convergence-to-target theorems remain completion obligations until their actual numerical premises are discharged.

The target cannot be weakened through definition holes, assumed residual smallness, changed factor order, or an implicit smooth-data upgrade. Target changes require an explicit scope revision. The certificate retains the actual PDE residual, all defect terms and arbitrary initial mismatch. Smoothness alone supplies no quantitative bound or convergence.

Primary sources: [release statements](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/NavierStokes/ComparatorSolution.lean), [Euler statements](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/Euler/Solution.lean), [Comparator challenges](https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/ComparatorChallenges), [Comparator trust model](https://github.com/leanprover/comparator/blob/19e111e2141cf333c7daff0f64c5f24acc91dd2e/README.md).
