# Experiment 014 — global existence for regular periodic variable-potential PDEs

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).

User authorization: proceed as needed toward broader PDE work and a general
existence result. The concrete target in this branch is global classical
existence and uniqueness for i u_t = -u_xx + V(x)u on period 2*pi, for any
complex Hilbert fiber, regular Fourier initial data, and selfadjoint operator
potentials with a finite second weighted absolute Fourier moment. Exact
regularity assumptions and intermediate interfaces will be fixed after API
review. This targets an infinite-mode PDE, with no finite cutoff in the solution.

Proposed construction: complete ℓ¹ state stores weighted coefficients; the
free diagonal Schrödinger phase is a strongly continuous isometry. Weighted
convolution by the potential is bounded. In the interaction picture its
conjugation yields a jointly continuous uniformly Lipschitz linear vector
field. Construct global evolution, synthesize the actual spatial field and
derivatives, establish the pointwise PDE, then invoke Exp013 uniqueness.
Operator-norm continuity of the conjugated vector field is not assumed.

General existence requires data/potential regularity. This goal does not assert
existence for every PDE, arbitrary irregular potential, or nonlinear equation.
Broader time-dependent potentials and forcing may be included when the proved
interfaces support them; their scope must follow accepted Lean statements.

Preserve all sealed experiments through013. Use local milestone checkpoints
and a tracked minute watcher. Final claims require exact-source modular and
combined checks, independent source review, separate fresh-VM qualification,
verified evidence transfer and a sealed packet. Keep local Chromebook copies;
Google Drive backup remains canceled.
