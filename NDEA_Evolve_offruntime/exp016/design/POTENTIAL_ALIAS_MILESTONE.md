# Actual potential sampling and frequency tails

Development acceptance, September 9, 2026. This removes the missing exact
potential-sampling alias formula and bounds its actual spatial discrepancy.
Read `../evidence/ALIAS_MILESTONE_LOCAL.json` and the original compiler receipts.
Exp016 is not yet independently qualified or sealed.

On the physical period 2*pi, N=2M+1 and Nh=2*pi, use the existing inverse DFT
S_h and normalized coefficients a_m(y), m=-M,...,M. Let v_ell be the complex
spinor operator Fourier coefficients of V, with the existing Exp014 assumption
W_v=sum_ell (1+abs(ell))^2*norm(v_ell)<infinity. P_V is the actual nodal block
operator, with (P_V y)_j=V(jh)y_j. There is no extra scaling or surrogate grid.

## Exact formula

`PotentialAlias.sampledPotential_fourierCoefficient_alias` proves

    a_r(P_V y) = sum_{m=-M}^M sum_{q in Z} v_{r-m+qN}(a_m(y)).

The alias progressions are summable. The proof expands the actual grid state
using existing Fourier inversion, applies the convergent potential series to
each lifted mode, uses integer-grid orthogonality, and reindexes precisely the
congruence class ell+m=r mod N. No Hermitian assumption is needed here.

## Bound on the full discrepancy

For a chosen integer 0<=R<=M, define

    T_v(s) = sum_{abs(ell)>s} norm(v_ell),
    A_v    = sum_all_ell norm(v_ell),
    L_y(R) = sum_{abs(m)<=R} norm(a_m(y)),
    H_y(R) = sum_{abs(m)>R} norm(a_m(y)).

`PotentialAliasBounds.sampledPotentialDefect_spatialL2_le_tailBudget` proves,
on any spatial interval [b,b+2*pi],

    norm(S_h(P_V y) - V*S_h(y))_L2
      <= 2*sqrt(2*pi) * (T_v(M-R)*L_y(R) + A_v*H_y(R)).

This bounds the full continuum discrepancy, including the continuum product
outside the retained band. It is stronger in scope than merely bounding the
q!=0 contributions to retained coefficients. For abs(m)<=R, products with
abs(ell)<=M-R reconstruct exactly. Each remaining mode discrepancy has norm
at most twice its amplitude. Absolute summability justifies each infinite
sum, and the physical L2 conversion gives exactly sqrt(2*pi).

`potentialAliasTailBudget_le_weighted` additionally substitutes the proved

    T_v(s) <= W_v/(1+s)^2.

This uses the original Exp014 regularity, not a newly strengthened smoothness
assumption. The remaining numerical coefficient sums are fully explicit.

## Actual certificate consumer and controls

`AliasTailCertificate.sampledCayley_gridTime_tail_error` and
`sampledCayley_partialSlab_tail_error` combine this result with the accepted
full-band stencil fourth-moment bound. They apply the resulting spatial budget
to the actual quadratic mean, velocity, and generator velocity, alongside the
existing ordered temporal bound. The actual A-half/B-full/A-half recurrence,
arbitrary initial mismatch, positive variable time steps and final partial
slab are preserved. No assumed residual-smallness field replaces the bound.

`AliasTailControls.sampledPotential_product_exact_of_resolved_support` proves
that this actual product discrepancy is zero if the state and potential have
supports within R and K, with R+K<=M. Finite support supplies RegularPotential.
The nonzero five-node cosine control has state mode +1, potential modes +/-1,
and R=K=1, M=2; the +2 product reaches the inclusive cutoff boundary exactly.
This control does not assert that evolving numerical states keep that support.

## Scope and next obligation

The formula, summability, bounds and actual error-certificate substitution have
source-bound Lean 4.31.0 development acceptance and transitive standard-axiom
checks under unchanged Mathlib pins. An independent read-only mathematical
review found no assumption or normalization error. This review is not an
independent compiler or independent-kernel check. Failed development attempts
are retained separately; they are not accepted evidence.

Mesh convergence still requires control of the actual evolved coefficient
tails/low sums, stencil fourth moments and h-dependent temporal operator norms.
L2 isometry alone cannot provide this. The selected baseline route remains
smooth Fourier approximation plus uniform stability; initial interpolation and
potential-perturbation estimates are the next small reusable obligations.
Finite support at initialization does not imply an invariant solution band.

The certificate is analytical. Infinite potential moments/tails need separately
validated bounds before producing fully computable numerical certificates.
No floating-point implementation or roundoff certification is claimed.
