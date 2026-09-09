# Actual sampled-potential stability — development acceptance

Four additive modules close the mesh-independent discrete potential-perturbation
obligation. They reuse the sealed Exp007 resolvent argument, the accepted actual
ordered recurrence, Exp016 Fourier L2 isometry and actual initialization bound.
The source-bound receipts are cataloged in
`evidence/POTENTIAL_STABILITY_MILESTONE_LOCAL.json`.

Let N=2M+1, Nh=2*pi, and let V,W be the actual matrix fields obtained from the
operator-valued Fourier potentials. Both coefficient families have the existing
Hermitian symmetry. Let delta bound ||V(x_i)-W(x_i)||op at the actual nodes.
Let L=sum_{j<J}|k_j|. The proved bound is

`||S_h yV_J-S_h yW_J||L2 <= sqrt(h)||y0-z0|| + L*delta*sqrt(h)||z0||`.

Each trajectory uses the same A_h=L_h+Z and its own B_h=sample(V-Z), with
unchanged k/4,k/2,k/4 Cayley stages. No commutation is assumed. Signed variable
steps are allowed; for positive steps, L is elapsed grid time. No N,h or
Laplacian norm occurs in the perturbation coefficient.

For the symmetric inclusive coefficient cutoff v_R and actual common initial
samples of a, the concrete consumer gives

`||S_h yv_J-S_h yv_R,J||L2 <= L*sqrt(2*pi)||a||*T_v(R)`

`T_v(R) <= (sum_ell (1+|ell|)^2 ||v_ell||)/(1+R)^2`.

The norm is the physical unnormalized L2 over any length-2*pi interval. These
are the original coefficients and actual omitted tail. RegularPotential is
used where series convergence is needed; no stronger potential hypothesis is
introduced. Cutoffs preserve Hermitian symmetry and are regular by finite
support, even before assuming regularity of the original family. R need not
be below M: nodal potential approximation is separate from alias exactness.

The shared bottleneck removed by SampledPotentialBounds is the sum-of-node-norm-
squares identity. It gives ||op(sampledBlock V)||<=C when every nodal induced
operator norm is <=C, with constant1. The actual split therefore satisfies
`||op B_h|| <= sum_ell ||v_ell||+1`. The kinetic bound for A_h remains separate.

Acceptance: four modules,28 explicit standard-axiom reports (one audits a
definition),0 errors,4 retained style warnings: two unnecessary typeclass
assumptions and two no-op change tactics. No warning-only rebuild was performed.
Corrected development failures remain preserved separately. Pinned Lean4.31.0
and Mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f were unchanged. Exact source,
runner, import artifacts, compiler log, output and transfer bindings passed.
These checks use restored artifacts; they are not fresh independent qualification.

Achievement: ACTUAL SCHEME INSTANTIATED for grid-time potential stability and
cutoff error. The same uniform constant has not been proved for quadratic paths
between grid times. The accepted final partial-slab residual certificate still
applies, but does not discharge that new comparison obligation. No solver
convergence, residual vanishing, floating-point validation or computable tail
certificate is claimed.

Next leverage point: derive the matching continuum two-potential L2 comparison
from Exp015. Together the discrete and continuum stability bounds will support
transfer from smooth Fourier cutoffs. Actual smooth-core scheme convergence,
evolved moment/tail estimates and remaining qualification gates still must be
proved or completed; finite input support is not an invariant evolved band.
