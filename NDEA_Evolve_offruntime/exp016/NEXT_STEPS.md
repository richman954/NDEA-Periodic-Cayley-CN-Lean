# Exp016 continuation after actual temporal refinement

This is a work plan, not verification evidence. Preserve Exp013–015 and all
accepted module source/receipt bindings. Exp016 is unsealed. PLAN.md retains
the normative reconstruction, actual recurrence and qualification gates.

There are 53 accepted development modules. The actual reconstruction/residual
certificates, Fourier/physical L2 normalization, initialization, alias/stencil
bounds and paired numerical/continuum potential-cutoff transfer are already
proved. TemporalBudget now substitutes the actual concrete A/B bounds and
uses unitarity. TemporalRefinement proves the actual accumulated temporal sum
tends to zero for M=q+1, N=2M+1, h=2*pi/N, J=N^4, k=1/J, at exact time 1.
The initial-plus-temporal budget tends to zero. The actual spatial sum remains
in scheduledCayley_error_le and is not proved to vanish.

Read design/TEMPORAL_MILESTONE.md and evidence/TEMPORAL_MILESTONE_LOCAL.json.
Both new checks passed with 24 transitive standard-axiom reports, no warnings
and no errors. The failed first refinement attempt remains rejected evidence.
No compiler job remains running. Do not rerun completed work from older notes.

1. Prove that the unique centered odd-grid representative cannot increase
   absolute frequency. Combine this with the existing Exp014.weight_add_le
   to obtain the fourth-weight alias inequality and a mesh-independent
   weighted bound for actual sampled potential multiplication.
2. Prove actual kinetic/Z stage preservation and potential-stage growth in
   the weighted numerical Fourier norm, first for fixed finite potential/data
   cutoffs. Derive uniform fourth-moment and low/high-tail bounds, then prove
   scheduledSpatialSum tends to zero. Discharge the baseline approximation
   quantifiers through the existing stability/initialization machinery.
   Follow design/NEXT_SPATIAL_ROUTE.md; its proposed bounds are not accepted
   theorems. General Exp014 data are not assumed to have fourth moments.
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
