# Actual spatial residual refinement — September 10, 2026 KST

62 Exp016 modules are development-accepted. WeightedSlabSpatialBudget,
SpatialScalarRefinement and SmoothCutoffConvergence passed 17 transitive
standard-axiom reports, with zero warnings/errors. The exact receipt is
../evidence/SPATIAL_REFINEMENT_MILESTONE_LOCAL.json. Two small normalization
probes passed separately. No combined or fresh independent qualification,
Comparator acceptance, additional kernel check or sealing is claimed.

The actual quadratic mean, velocity and generator-velocity now feed the
complete spatial budget:
`B_slab <= C_sp*(1+k*K_G/8)*(W_2(y_j)+W_2(y_{j+1}))`,
where `K_G=4/h^2+K_V`; the accepted actual generator decomposition cancels Z.
The sum uses every actual ordered step to time 1. With L=floor(M/2), both
cutoffs expand, the potential tails vanish under the original second-moment
condition, and k*K_G tends to zero on J=N^4. These estimates prove the actual
scheduledSpatialSum vanishes for each fixed initial/potential cutoff. The
existing Exp015/Exp014 certificate then proves actual solver convergence at
exact time 1 for those fixed approximants.

The missing spatial-residual limit for the smooth approximants is removed.
The next consumer is the initial-data stability transfer: actual samples of
a-a_S have a physical norm controlled by the omitted Fourier tail, and the
existing numerical/continuum stability estimates transfer the error. Then
remove the potential cutoff. Those approximation quantifiers remain drafts.
The finite-horizon k=T/J schedule and maximum error over all grid times are
also drafted in dependency order, with T fixed before the refinement limit.
Continuous-time quadratic reconstruction refinement remains separate.

No invariant finite solution band, stronger original-data regularity, free
residual-smallness field, easier recurrence, or changed norm is used. The
original 59 accepted bindings, 132 imported artifacts and 789 sealed Exp013–015
payloads/packet hashes remain unchanged. Rejected drafts and full logs remain
under attempts/; they are not production acceptance. Main and pins are intact.

Watcher 9546 now produces verified advancing minute snapshots. A review diff
briefly stopped watcher 27367 because .diff was not an allowed Git-evidence
suffix; the bytes are preserved as .diff.txt without changing checkpoint policy.
Read WATCHER_STOP_0251.json, WATCHER_RESTART_0254.json and
WATCHER_ADVANCING_0258.json in evidence/spatial_refinement_20260910.
All new accepted work and further drafts are local until curated Git readback.
