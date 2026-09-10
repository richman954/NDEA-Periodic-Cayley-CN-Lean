# Physical-grid kinetic assembly — development milestone

Accepted September 10, 2026 at 00:04 UTC (September 9 local time).
The authoritative catalog now contains 51 accepted Exp016 development modules.
Exp016 remains unsealed; combined and fresh independent qualification are pending.

## Barrier removed

`NDEAEvolve.Exp016.sampledSplitA_opNorm_le` in
[KineticAssembly.lean](../lean/KineticAssembly.lean) proves
`‖op (sampledSplitA (2*M) h)‖ ≤ 4/h^2 + 1` for the actual physical grid,
with explicit hypotheses `((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi` and `0 < h`.
It combines the accepted Fourier/Parseval kinetic bound with the fixed Z block
estimate and the triangle inequality for the induced operator norm.
`sampledPotentialZ_opNorm_le_one` proves the fixed-block estimate for any `n,h`.

This closes the remaining actual A-operator assembly obligation. It does not
prove temporal refinement, evolved spatial regularity, or solver convergence.

## Doors opened and best next move

The actual temporal certificate can now replace its induced operator norms by
`a ≤ 4/h²+1` and the accepted `b ≤ sum_ell ‖v_ell‖+1`.
The immediate consumers are the temporal terms in
`sampledCayley_gridTime_quantitative_error` and
`sampledCayley_partialSlab_quantitative_error`, followed by the initialization
and alias-tail certificate interfaces. Prove that explicit temporal budget
vanishes for the recorded `N=2(q+1)+1`, `h=2π/N`, `J=N^4`, `k=N^-4` schedule,
using the already proved uniform physical norm of actual samples.

## Next barrier

The spatial defect still needs evolved smooth-core consistency/tail control
or sufficient propagated numerical moments. Finite Fourier input and potential
support do not imply an invariant finite solution band. Uniform L² stability
does not control the fourth moments or coefficient tails in the existing
spatial certificate. The paired numerical/continuum potential-cutoff transfer
is already accepted and must be reused.

## Accepted checks and recovery

[Source-bound receipt](../evidence/20260909T235728.222817Z_KineticAssembly.json):
Lean 4.31.0, pinned Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`,
single-thread local compilation, exit 0 in 294.582 seconds, no warnings/errors.
Both transitive axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` occurs in either accepted theorem's dependencies.
No additional independent-kernel or Comparator check ran.

Source SHA-256: `e2452dc2b18153b7595984b43f7ca56748cbdb1d870325d342cfa8450e97a9ae`.
Receipt SHA-256: `964decbc28054f3414a4da0bfa3f03d319b4a0e149f18eb3b6f238400e61d2f8`.
[Acceptance/readback record](../evidence/KINETIC_ASSEMBLY_MILESTONE_LOCAL.json)
also binds the compiler log and artifact. All 50 previous accepted modules'
sources, receipts, logs and installed artifacts remain unchanged; all 110
previous project import artifacts match the pre-check inventory.

The two failed local drafts are retained in `attempts/kinetic_assembly_reboot_r1`
and `attempts/kinetic_assembly_reboot_r2`. They are rejected evidence. The final
proof explicitly maps the operator sum and supplies the physical mesh relation
required by `gridKinetic_opNorm_le`; the broader draft was never accepted.

Reproduction uses the unchanged source-bound runner:

```sh
python3 -B /home/richman954/NDEA_Evolve_offruntime/exp016/run_lean.py lean/KineticAssembly.lean
```

The runner checks the existing project compiler/dependency pins and records
source, log and output hashes. Imported project artifacts must first match
their accepted source-bound receipts. This is modular development checking;
the full isolated/fresh qualification gates remain mandatory before sealing.

Post-reboot recovery verified all 1,298 saved payloads and all 789 sealed
Exp013–015 payloads. No sealed proof was rerun. Watcher session 27367 is producing
minute snapshots; dated manual and Git readback receipts identify later coverage.
The external checkout and manuscript stay outside routine snapshots/public Git.
