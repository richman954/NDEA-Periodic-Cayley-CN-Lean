# Next spatial obligation: actual quadratic slab estimates

Current accepted state: 59 development modules. InitialWeightedCutoff and
WeightedSpatialMoments close the finite initial weighted bound and the fourth
moment/tail-to-spatial-budget bridge. Read INITIAL_WEIGHTED_MILESTONE.md and
its source-bound receipt. All previous numerical and continuum definitions,
sealed predecessors, pins and qualification gates are preserved.

## Accepted inputs and immediate consumer

For each fixed initial-data and Hermitian potential cutoff, actual samples
initialize an actual ordered Cayley trajectory whose W_2 is uniformly bounded
at every prefix to time 1, eventually on the saved schedule. The complete
sampledSpatialDefectBudget at an arbitrary grid state y is at most C_sp*W_2(y),
where the explicit spatialFourthWeightCoefficient is

`sqrt(2*pi)*h^2 + 2*sqrt(2*pi)*(T_v(M-L)+A_v/(1+L)^4)`.

The physical mesh, full normalized complex-spinor DFT, strict tail and inclusive
low cutoff L<=M are unchanged. The initial cutoff need not be resolved by M.
Higher initial moments are finite only after the explicit cutoff.

## Recommended next proof

The remaining actual sampledSpatialStageBudget in TemporalBudget.lean is
`B_sp(mean)+(k/2)*B_sp(velocity)+(k^2/8)*B_sp(G*velocity)`.
Here mean=(y+y3)/2, velocity=(y3-y)/k, and G=op A+op B for the actual ordered
endpoint y3. Keep k>0 explicit and use the accepted weighted triangle/scalar
identities to bound W_2(mean) and k*W_2(velocity) by the endpoint weights.

For G, KineticSymbolBound.fourierCoefficient_gridKinetic_norm_le already gives
the actual kinetic coefficient bound 4/h^2. Sum it against the nonnegative
weights and combine with WeightedSampledPotential's finite-cutoff bound.
SampledPotential.sampledSplit_sum proves cancellation of the actual Z terms:
the sum is gridKinetic plus sampledBlock of V_R. This should yield the explicit
weighted G bound 4/h^2+K_V, without proving a new surrogate operator estimate.

Substituting these bounds should give
`B_stage <= C_sp*(1+k*K_G/8)*(W_2(y)+W_2(y3))`.
This is a proposed next theorem, not an accepted estimate. Then consume the
accepted uniform endpoint bound and the actual sum of step sizes, exactly 1.
This route reuses the existing certificate and requires no extra smooth gluing
or stronger continuum regularity theorem.

## Refinement and next barrier

Choose, for example, L=floor(M/2), and prove L and M-L tend to infinity.
The accepted potential tail estimate uses exactly the original second moment;
it controls T_v(M-L). Prove C_sp tends to zero and k*K_G remains controlled
on M=q+1, h=2*pi/(2M+1), J=(2M+1)^4, k=1/J. Then prove the actual
scheduledSpatialSum tends to zero for fixed cutoffs and feed scheduledCayley_error_le.

Only after this smooth-cutoff convergence proof can the baseline theorem's
potential and initial-data approximation quantifiers be discharged. Finite
potential support does not imply an invariant solution band. Temporal or
endpoint spatial estimates alone are not full solver convergence. Quadratic
between-grid-time transfer and full independent qualification remain separate.
