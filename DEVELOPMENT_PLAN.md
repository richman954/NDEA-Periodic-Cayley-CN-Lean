# Development continuation plan

Exp016 is authorized and in progress. This startup-foundations checkpoint contains 5 locally accepted modules and 39 theorem declarations, with exact source/receipt/log bindings in [MODULAR_ACCEPTANCE.json](NDEA_Evolve_offruntime/exp016/MODULAR_ACCEPTANCE.json). The full experiment remains incomplete and unsealed; combined and independent qualification are still pending. See [NEXT_STEPS](NDEA_Evolve_offruntime/exp016/NEXT_STEPS.md) for remaining work. Exp013–015 accepted bytes are unchanged, and staging performs no proof rerun.

The chosen endpoint connects the actual symmetric Cayley scheme, including its A-B-A factor order, to a faithful odd-grid Fourier interpolant and a quadratic time reconstruction on each slab. It will derive the actual continuous residual, apply Exp015 and retain arbitrary initial error. Spatial consistency under refinement and resulting broader convergence are a separate next obligation. The accepted startup foundations alone do not establish this endpoint.

The following baseline guidance remains applicable; its earlier requirement to choose a new experiment has now been met by Exp016 PLAN.md.

The barrier removed by Exp015 is converting controlled continuous forcing/residual into continuous L2 error with a sharp coefficient 1. This opens the same stability endpoint to several approximations once their actual residuals are controlled. The next barrier is proving those consistency estimates for a concrete discrete method, including a faithful norm/sampling bridge. A residual theorem by itself does not establish that a numerical scheme has a small residual.

Before implementation, compare plausible reconstructions by proof reuse, regularity required, whether their residual is well-defined in the proved class, and their direct connection to the actual scheme. Record the chosen scope in a new working experiment. Reuse frozen results by exact pinned copies or imports; do not edit accepted Exp013–015 files to retrofit later claims.

Development validation should progress from actual imports and small meaningful controls through module elaboration, combined reconstruction and catalog audit, full local qualification, independent qualification, transfer checks and packet sealing where appropriate. Tests cover their actual stated properties, not blanket mathematical correctness. Preserve failures and accepted logs in their appropriate development/recovery locations. Heavy original archive evidence remains on the dedicated recovery branch.

Git cadence is meaningful progress, before risky changes and at milestones. Local snapshots remain more frequent. Bind commits externally to source/combined hashes and immutable acceptance receipts after readback; do not rewrite old receipts to add a commit. Review scope before tags/releases and never move a published verified tag.
