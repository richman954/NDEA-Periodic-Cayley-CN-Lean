# Exp016 startup milestone — local modular acceptance

Five modules passed pinned local Lean checks, with exact source/log/runner/compiler hashes and unchanged-source receipts. There are 39 public theorem declarations across these modules. FourierReconstruction additionally prints seven public axiom audits, all using only the standard allowed axioms. This is not a combined or independently qualified Exp016 release.

| Module | Public theorems | Result | Remaining compiler warnings |
|---|---:|---|---|
| SplitDefect |4|exit 0|5 deprecation warnings|
| AffineReconstruction |14|exit 0|7 unused section-variable warnings|
| SpatialL2Bridge |4|exit 0|2 unused section-variable warnings|
| FourierReconstruction |7|exit 0; seven clean axiom audits|1 unused simp warning|
| QuadraticTime |10|exit 0|2 sequencing style warnings|

The actual A-half/B-full/A-half Cayley step is an immediate consumer of the ordered defect identity. Full odd-grid Fourier interpolation recovers every arbitrary grid state through the saved sampling map. The quadratic time polynomial has exact endpoints, actual derivative and an exact grid residual retaining its endpoint defect. The affine field regularity and integral spatialL2 rules are reusable foundations for the forthcoming synthesis/certificate proof.

The chosen construction is full centered Fourier interpolation in space and quadratic polynomial extensions on individual positive time slabs. PLAN.md specifies the endpoint, assumptions, defect terms, explicit budget and natural refinement boundary; design/RECONSTRUCTION_COMPARISON.md compares seven serious alternatives. No O(h²+k²) PDE rate is claimed.

Next: prove Fourier spatial derivatives and continuum L2 isometry; instantiate regular synthesis; derive actual stencil/potential discrepancy and ordered splitting bounds; apply Exp015 slabwise to Exp014’s unique solution with arbitrary initial mismatch. Full refinement convergence requires a separate derived spatial/high-frequency argument. The potential-perturbation/density note records a later route, not a completed proof.

Exp013–015 remain sealed and immutable. The startup baseline readback checked 789 sealed payloads unchanged. The recovery watcher produces verified 60-second snapshots and is not an automatic boot service. Git checkpoints are separately read back and recorded under NDEA_Recovery/github_evidence; consult its latest binding for the exact development commit. Main and heavyweight archival history are preserved.
