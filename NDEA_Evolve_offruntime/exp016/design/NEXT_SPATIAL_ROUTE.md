# Next spatial obligation: weighted numerical Fourier control

This is a proposed proof route, not accepted Lean mathematics. It follows the
actual temporal-certificate work and preserves the existing reconstruction,
recurrence, data class and qualification gates.

## Comparison and recommendation

| Candidate | Existing support | Missing proof and decision |
|---|---|---|
| Propagate a weighted absolute Fourier norm of the actual numerical states | GridAlias gives the unique centered representative and exact mode alias; PotentialAlias gives the actual product alias sum; StencilFourier gives the fourth-moment stencil defect; Exp014.weight_add_le supplies submultiplicative weights | Prove that folding cannot increase absolute frequency, then a mesh-independent weighted multiplication bound and actual Cayley stage growth. Recommended next route for each fixed finite cutoff. |
| Compare the scheme directly with a sampled higher-regularity continuum solution | Exp014 solution and Exp015 error estimates, plus paired cutoff stability | Requires additional continuum regularity and local truncation proofs before reconnecting to the existing certificate. Retain as an alternative if numerical weighted propagation proves too costly. |
| Use only L2 stability or assume an invariant finite band | L2 stability is already proved | Insufficient: the existing top-frequency counterexamples prevent this inference. Finite potential support does not preserve finite solution support. Reject this shortcut. |

The strongest immediate small lemma is the centered representative weight
inequality. If `N=2M+1`, `r` is the actual odd-grid representative and
`N` divides `ell-oddFrequency M r`, prove
`|oddFrequency M r| <= |ell|`. Existing GridAlias proves existence, uniqueness,
band membership and exact reconstruction, but does not expose this minimum
absolute-frequency estimate. Combine it with sealed `Exp014.weight_add_le`;
do not edit that predecessor or confuse grid aliases with upstream aliases.

## Intended consumer and proof sequence

Write the proposed numerical fourth weighted norm as

`W4(y) = sum_r (1+|oddFrequency M r|)^4 * ||fourierCoefficient M h y r||`.

For the folded representative of `m+ell`, the desired weight bound is
`w4(fold(m+ell)) <= w4(m)*w4(ell)`. Prove it from minimum absolute frequency,
the triangle inequality and the existing squared weight inequality. This is
the missing arithmetic input to the actual sampled-potential product estimate

`W4(P_V y) <= (sum_ell w4(ell)*||v_ell||) * W4(y)`.

The first target uses a fixed symmetric finite potential cutoff, so the fourth
weighted coefficient sum is finite. The full Exp014 hypothesis only provides
second weighted moments; do not assert a finite fourth potential moment for
that whole class. The original class should later follow through the already
accepted mesh-independent numerical/continuum cutoff transfer and a justified
initial-data approximation transfer.

Next prove that each actual A Cayley stage preserves W4 mode by mode. The
kinetic symbol is scalar on each spinor mode and the fixed Z block is Hermitian.
This must follow from the actual coefficient identities and actual stage solve,
not from an assumed diagonal surrogate. For B, the proposed weighted operator
bound K4 and the actual denominator equation should give resolvent control
when `alpha*K4<1`. The Cayley factor is then bounded by
`(1+alpha*K4)/(1-alpha*K4)`, where `alpha=k/2` for the B-full stage.
Prove a uniform finite-time product bound under an explicit eventually valid
step restriction. Preserve A-half/B-full/A-half order throughout.

For fixed finite initial data cutoff, prove a uniform initial W4 bound once
the expanding grid resolves it. No invariant solution band is needed if the
weighted norm is propagated. All constants may depend on the fixed data and
potential cutoffs, but must be independent of the numerical grid.

## How this could close the existing spatial certificate

W4 controls the fourth-frequency l2 moment in the stencil bound and the low/high
coefficient l1 terms in the potential alias bound. For actual endpoint states,
use the definitions of the mean and velocity to control W4(mean) and k*W4(velocity).
The k²*generator-velocity term also requires the proved kinetic symbol bound
and weighted potential multiplication; its possible factor k*h^-2 tends to
zero on the current k=N^-4 schedule. These are obligations to prove explicitly.

After those estimates, prove that `scheduledSpatialSum` tends to zero for each
fixed smooth cutoff, then discharge the approximation quantifiers using the
existing stability results. Until then, the actual time-1 error certificate
retains its entire spatial sum. Temporal refinement is not solver convergence.
