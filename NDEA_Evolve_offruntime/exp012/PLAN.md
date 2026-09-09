# Experiment 012 — classical periodic uniqueness

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).

Prove uniqueness in the unchanged `Exp010.IsClassicalPeriodicSolution` class
for the concrete spinor equation `iUt=-Uxx+(Z+X)U` on period `2π`.
Competing solutions are arbitrary classical functions. Their Fourier-series
representation, an energy identity, and any global time bound are not assumed.

The proof derives the local norm-squared conservation identity, differentiates
the integral on an arbitrary interval of length `2π` using a compact local
majorant, and cancels the periodic flux. Applied to the difference of two
solutions with equal initial data, conserved zero energy and continuity imply
pointwise equality for all real times and positions.

The final endpoints will identify any classical solution with the previously
constructed Fourier solution when their initial data agree, and transfer
Experiment 011's uniform numerical convergence to that unique solution under
the existing regularity, exact initialization and refinement assumptions.

Acceptance requires all production modules and exact controls to pass Lean,
a complete new public axiom catalog, combined source checks locally and on a
distinct fresh Colab CPU VM, accepted downloaded evidence, independent source
review, and a sealed checksum-verified review packet. Frozen Experiment 011
source, manifests and archives are preserved. Compatible compiler and external
library artifacts remain trusted inputs.

Spatially varying potentials, weaker solution classes, nonperiodic boundary
conditions and sharp numerical rates remain outside this milestone.
