# Exp016 continuation after weighted sampled-potential control

This is a work plan, not verification evidence. Preserve Exp013–015 and all
accepted module source/receipt bindings. Exp016 is unsealed. PLAN.md retains
the normative reconstruction, actual recurrence and qualification gates.

There are 55 accepted development modules. The actual reconstruction/residual
certificates, Fourier/physical L2 normalization, initialization, alias/stencil
bounds and paired numerical/continuum potential-cutoff transfer are already
proved. TemporalBudget now substitutes the actual concrete A/B bounds and
uses unitarity. TemporalRefinement proves the actual accumulated temporal sum
tends to zero for M=q+1, N=2M+1, h=2*pi/N, J=N^4, k=1/J, at exact time 1.
The initial-plus-temporal budget tends to zero. The actual spatial sum remains
in scheduledCayley_error_le and is not proved to vanish.

AliasWeights proves centered alias minimization and weighted DFT mode bounds.
WeightedSampledPotential proves the actual finite-cutoff multiplication bound
W_p(P_(V_R)y) <= K_(p,R,v)*W_p(y), with no grid factor or R<=M restriction.
p=2 is the fourth weight. It does not strengthen the full Exp014 data class.
Read design/WEIGHTED_SPATIAL_MILESTONE.md and its exact local receipt.
The two new checks passed with 18 standard-axiom reports, zero errors and one
reviewed deprecated-name warning. The first alias attempt is rejected evidence.
No compiler job remains running. Do not rerun completed work from older notes.

1. Prove weighted triangle/scalar properties, actual kinetic/Z stage preservation
   using sealed Exp008.hamiltonian_step_modeLift, and the Z contribution needed
   for sampledSplitB. Use its actual denominator equation for B-stage growth
   with K_B=K_V+1 and |alpha|*K_B<1. Keep stage parameters k/4,k/2,k/4.
2. Propagate the actual ordered trajectory in
   the weighted numerical Fourier norm, first for fixed finite potential/data
   cutoffs. Derive uniform fourth-moment and low/high-tail bounds, then prove
   scheduledSpatialSum tends to zero. Discharge the baseline approximation
   quantifiers through the existing stability/initialization machinery.
   Follow design/NEXT_SPATIAL_ROUTE.md; the first two weighted multiplication
   steps are accepted, while propagation/refinement remains proposed.
   General Exp014 data are not assumed to have fourth moments.
3. Complete statement/dependency review and required controls, isolated
   combined and fresh independent qualification, transfer validation and
   finalizer/sealing gates. Modular acceptance is not full qualification.

Quadratic partial-slab potential transfer and any uniform between-grid-time
refinement theorem remain separate obligations. No assumed residual vanishing,
L2-to-derivative inference, invariant finite solution band or false full-band
M*h<=1 premise may replace the missing spatial argument.

Recovery: inspect WATCHER_STATUS.json and the advancing dated checkpoint
receipts, not a PID alone. Keep verified manual local milestones even with
the watcher active. Use dev/variable-potential for curated Git checkpoints
and verify uploaded bytes; leave main and sealed archival heads unchanged.
