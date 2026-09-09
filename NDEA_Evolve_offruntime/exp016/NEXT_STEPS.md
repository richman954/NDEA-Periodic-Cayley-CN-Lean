# Exp016 continuation after actual potential stability

This is a work plan, not verification evidence. Preserve Exp013–015 and reuse the exact BASELINE/NUMERICAL_PINS sources. Exp016 is not sealed. The normative endpoint and assumptions are in PLAN.md.

Development-accepted work now includes the quadratic slab identities/regularity,
physical L2 isometry, exact ordered stage bounds, sampled potential and stencil,
actual finite/partial-slab Exp014 error certificates, full-band stencil multiplier
bounds, and the exact potential alias series plus low/high frequency-tail bounds.
AliasTailCertificate uses these bounds on the actual mean, velocity and generator
velocity of the ordered Cayley stages. InitialSamplingBounds now proves the actual
sampling/interpolation tail, its weighted rate, the uniform sampled physical norm
and an arbitrary extra initialization mismatch term. InitializationCertificate
substitutes this bound into the actual grid-time and partial-slab certificate.
SampledPotentialBounds, CayleyPerturbation, PotentialCutoff and PotentialStability
now prove mesh-independent actual grid-time potential perturbation, including
the symmetric cutoff tail/rate and actual sampled initial norm. Read current TASK_STATE source receipts;
do not repeat these proofs because an older startup note lists them as pending.

1. Complete the finite-grid milestone's final statement/dependency review and
   required controls, then isolated combined and fresh independent qualification,
   transfer validation, finalizer and immutable packet gates. Development module
   acceptance is not this full qualification. Preserve failed attempt evidence.
2. Prove the matching continuum two-potential L2 comparison using Exp015. The
   sampled block norm, actual ordered grid-time perturbation and Hermitian
   cutoff-tail bounds are accepted. The kinetic A_h norm estimate remains.
   These support the smooth-cutoff transfer; they do not establish smooth-core
   scheme convergence or uniform comparison of quadratic partial-slab paths.
3. Close the main refinement obstacle: numerical evolution of the actual
   fourth moments and low/high coefficient sums, or a justified smooth-core
   comparison with uniform stability. Finite Fourier input/potential support
   does not imply an invariant finite band for the evolved numerical solution.
   No norm-isometry or fixed-grid estimate is a substitute for this obligation.

The next experiment must derive accumulated spatial-defect vanishing along actual refinements, using the proved exact-sampling initialization bound. Full-band M*h<=1 is false on the chosen grid family; old small-band estimates cannot be applied wholesale. The sampled potential bound is now proved; the kinetic bound and any needed stronger graph regularity remain obligations. The sampled initial physical norm is now bounded by the existing weighted data norm; this does not control evolved derivatives. Exp016 does not assume residual-to-zero as a shortcut to the convergence theorem.

Recovery: inspect WATCHER_STATUS.json and the timestamped LATEST_CHECKPOINT.json, not a PID alone. The current watcher is manual startup, not a boot service. Meaningful development commits go to dev/variable-potential; source backups and theorem qualification remain distinct.
