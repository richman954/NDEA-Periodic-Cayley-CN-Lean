# Mesh-independent sampled-potential perturbation

Continuation from the accepted initialization milestone, 2026-09-09. All42
accepted sources stay frozen. This is the next supporting obligation for the
selected smooth Fourier approximation plus uniform stability route.

The immediate endpoint is a bound for actual ordered trajectories with two
sampled Hermitian potentials and possibly different numerical initial vectors:

`sqrt(h)||y_V,N-y_W,N|| <= sqrt(h)||y0-z0||
 + (sum_{j<N}|k_j|)*delta*sqrt(h)||z0||`.

Here each trajectory uses the same actual A=L_h+Z and the exact k/4,k/2,k/4
Cayley stages; B_V samples V-Z. The hypothesis on delta is only the induced
operator norm difference at actual nodes. The norm bound is proved from those
node values, not added as an assumed grid-operator bound. No grid-size or
Laplacian norm factor belongs in this estimate. Hermitian values of both
potentials supply unitarity. No commutativity or real-entry hypothesis is used.

New dependency order:

1. Sum of node norm squares equals the full grid norm square; sampled block
   operator bound has constant one. The shared Z cancels in B_V-B_W. Also prove
   the concrete b<=sum||v_ell||+1 bound needed by the temporal certificate.
2. Adapt the exact pinned Exp007 resolvent/Cayley perturbation proof from Fin n
   to the existing generic finite grid index. Derive the actual ordered-step
   and finite-trajectory comparison, retaining arbitrary initialization mismatch.
3. Symmetric Fourier cutoff: preserve RegularPotential and Hermitian symmetry,
   and prove ||V-V_R||op <=T_v(R)<=W_v/(1+R)^2. No smoothness assumption is added.
4. Apply these results to sampledCayleyTrajectory and the exact Fourier L2
   isometry. Actual initial samples use the accepted sqrt(2*pi)||a|| bound.
   The cutoff consumer therefore has error <=T*sqrt(2*pi)||a||*T_v(R), uniformly
   in the spatial grid, whenever total absolute step length is at most T.

This is grid-time potential stability. Comparing the assembled quadratic paths
between grid times remains separate because their generators and velocities
also change. The accepted final-partial-slab PDE certificate remains available;
its existence does not establish a uniform potential perturbation constant there.

Remaining convergence obligations: prove smooth-core actual-scheme convergence,
including evolved spatial consistency/tail control and potential comparison on
the continuum side; then justify the full approximation argument. Initial L2
norms and the present uniform potential estimate alone do not control derivatives.
These are analytical bounds; certified evaluation of infinite tails is separate.

Qualification stays source-bound incremental development followed by the existing
combined, fresh independent, transfer, review and sealing gates at the milestone.
