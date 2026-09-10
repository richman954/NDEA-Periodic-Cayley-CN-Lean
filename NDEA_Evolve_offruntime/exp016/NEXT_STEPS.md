# Exp016 continuation after actual weighted Cayley propagation

This is a work plan, not verification evidence. Preserve Exp013–015 and all
accepted module source/receipt bindings. Exp016 is unsealed. PLAN.md retains
the normative reconstruction, actual recurrence and qualification gates.

There are 57 accepted development modules. The actual reconstruction/residual
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
WeightedGridStages now proves actual A-stage preservation and the B bound
including -Z. WeightedCayleyPropagation proves the actual ordered trajectory
bound and eventual small-step restrictions on the saved schedule. Every
prefix to time 1 has a grid-independent factor times the explicit initial W_p.
Read design/WEIGHTED_CAYLEY_MILESTONE.md and its exact local receipt.
These two new checks passed with 23 standard-axiom reports, zero errors and
two reviewed style/deprecation warnings. No failed attempt occurred here.
No compiler job remains running. Do not rerun completed work from older notes.

1. Prove a uniform initial W_2 bound for actual samples of fixed finite initial
   data cutoffs. Use Exp014.ofCoefficients, its coefficient identity,
   SamplingExpansion.sampledInitialState_eq_tsum and the accepted finite-sum
   and folded-mode weighted bounds. No grid-resolution condition is needed
   for that bound. Feed scheduledCayley_cutoff_fourierWeightedNorm_eventually_le
   to obtain an eventual uniform bound for every actual prefix up to time 1.
2. Derive uniform fourth-moment and low/high-tail bounds for actual endpoints,
   means, velocities and generator-velocities, then prove
   scheduledSpatialSum tends to zero. Discharge the baseline approximation
   quantifiers through the existing stability/initialization machinery.
   Follow design/NEXT_SPATIAL_ROUTE.md; actual weighted propagation is
   accepted, while the initial weighted bound and spatial refinement are open.
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
