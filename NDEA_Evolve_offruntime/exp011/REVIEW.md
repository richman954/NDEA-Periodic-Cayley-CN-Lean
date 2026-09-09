# Experiment 011 source and verification review

No blocking issue was found within the stated reconstruction scope. The
review covers all five new modules, their complete public theorem catalog,
the numerical diagnostic, and the verification and preservation workflow.
The exact reviewed versions are recorded in
[REVIEW_CHECK.json](evidence/REVIEW_CHECK.json). Compiler acceptance is
recorded separately; this source review does not itself rerun Lean.

## Actual reconstruction and target

The target is Experiment 010's actual classical infinite Fourier solution
under `Regular a`, the summability of `(1+|m|)² ‖a_m‖`. The new derivative
norm bounds follow from its established derivative series and summable
majorants. The mean value inequality then supplies global spatial and time
norm difference bounds with constants `A₂` and `2A₂`. Neither derivative
exchange nor these difference bounds is assumed in the new endpoints.

`gridState` is an integer power of the actual full-grid symmetric Cayley
operator applied to the full infinite reference sampled at time zero.
`nodeValue` extracts both spin components. The reconstruction selects actual
states and nodes by explicit clamped natural floors. It is not an arbitrary
approximation supplied with an assumed error bound.

Positive mesh and time steps, along with the rectangle bounds, justify the
floor estimates. The proof includes `t=0`, `t=Nk`, `x=0`, and `x=dh`.
The terminal time selects the final numerical step. At the right spatial
endpoint, the last node is used and lies exactly one mesh width away.
Finite reconstructions can therefore be discontinuous and have different
values at the two spatial endpoints. The theorem concerns the entire closed
rectangle and includes this discrepancy in its estimate; the target itself
is periodic and classical.

## Error norm and uniformity

Extracting a two-component block does not increase the full Euclidean grid
norm. Converting the mesh-weighted grid error to a block error requires
division by `sqrt(h)`. This factor appears explicitly in the reconstruction
bound, and an exact node-spike control refutes its omission when `0<h<1`.

The triangle inequality through the exact reference at the selected node and
time gives `e_j/sqrt(h)+A₂*h+2*A₂*k`. All three terms refer to the actual
reference and numerical iterate. Exact sampled initialization makes the
initial grid discrepancy zero. A merely vanishing initial weighted error
would not suffice after division by `sqrt(h)`; the final theorem does not
silently allow that broader initialization class.

For every `j≤N` in the retained schedule, `jk≤1`. The existing error theorem
therefore applies uniformly over every step, not only the terminal step.
Using `A≤A₂`, the second-moment tail bound, and the exact schedule formulas
gives `e_j≤sqrt(2π) A₂ G(1/M)/M²`, where
`G(r)=(1000/36)(1+2r²)³+π²/128+2`.

Since `h=(π/4)/M³`, the proved nonnegative square-root identity turns the
divided error into the bound `A₂ G(1/M) sqrt(8/M)`, which tends to zero.
The additional spatial and time terms tend to zero as well. This resolves
the potentially dangerous inverse-mesh loss rather than ignoring it.

`reconstruction_tendstoUniformlyOn` uses this one bound for every point in
`[0,1] × [0,2π]`. Its conclusion is actual Mathlib `TendstoUniformlyOn` of
the reconstructed `E 2`-valued functions. The classical endpoint pairs it with
the inherited predicate containing derivative existence, joint continuity,
periodicity, and the PDE. A pointwise corollary and a regular infinite-support
coefficient witness are also supplied.

The complete catalog contains 44 new declarations: 7 derivative/difference
bounds, 8 reconstruction theorems, 8 schedule bounds, 6 uniform-convergence
theorems, and 15 controls. Probes, including the unfinished uniqueness route,
are outside the generator's production input list.

## Numerical evidence

The diagnostic uses a separate infinite signed geometric datum. Its second
weighted moment is 23; its radius-80 omitted reference tail is exactly
`1/604462909807314587353088`. These values were checked independently with
rational arithmetic. The saved numerical result matches the current script
hash. All 476 saved space-time index selections and distance restrictions were
independently checked with exact rational coordinates. Their error
decompositions, reported level maxima, and refinement orders are consistent
with the detailed saved rows.

The geometric alias formulas sum positive and negative frequencies into the
correct finite residue classes, including arbitrarily high-frequency initial
aliases. Dense small-grid checks compare the modal calculation with direct
three-stage Cayley solves, using both periodic wraps. The stage parameters,
potential matrices, reference orbit signs, and endpoint conventions agree
with the formal definitions.

These are ordinary floating-point computations. Their truncation bounds do
not certify rounding or underflow, and the sampled maxima do not certify a
continuum supremum. The report distinguishes the observed refinement order
from the much more conservative proved envelope. The incorrect next-node and
next-step controls exercise the floor choices.

## Verification and preservation

The infrastructure is adapted from the sealed Experiment 010 workflow; see
[INFRASTRUCTURE_REVIEW.md](INFRASTRUCTURE_REVIEW.md). The foundation is pinned
exactly, the complete combined source and catalog are reconstructed, and
final checks exclude project artifacts from their import paths. The fresh-VM
receiver binds the new boot and allocation, exact bootstrap deliveries,
completed command logs, final proof inputs, compiler audit logs, and matching
external artifact manifests.

The finalizer requires accepted local, independent, transfer, and numerical
receipts; current module and tool hashes; this review; and predecessor
preservation. It refuses existing sealed outputs, verifies every ZIP member
by readback, and checks the exact manifest bytes. The final archive receipt
is external to the ZIP, avoiding a self-hash cycle. A stale reproduction-doc
description of the numerical suite was corrected during review.

Accepted compiler runs and final qualification are recorded in
[FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). The pinned
compiler and compatible external libraries remain trusted inputs. The proof
does not claim uniqueness, variable spatial potentials, weaker coefficient
regularity, arbitrary perturbed initialization, or a sharp uniform rate.
