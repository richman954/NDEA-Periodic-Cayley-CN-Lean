# Continuum potential stability and actual cutoff error transfer

This additive Exp016 development step preserves Exp013–015 and the previous
46 accepted Exp016 source files. Source-bound modular Lean acceptance is
separate from the remaining combined, fresh independent, transfer, review and
sealing gates. Read `evidence/CONTINUUM_MILESTONE_LOCAL.json` for exact receipts.

## Barrier removed and concrete consumer

`SpatialL2Operator.spatialL2_operator_le` is stated in the existing Exp015
physical integral norm: a continuous operator field bounded pointwise by
delta multiplies continuous fields with L2 norm at most delta times their L2
norm. The interval length and delta are nonnegative; no normalization changes.

`ContinuumPotentialStability.solution_pdeResidual_other_potential` derives
the actual residual of Exp014.solution w c in the equation with potential v:
`R_v[u_w] = (W-V)u_w`. Exp013 energy conservation and unchanged Exp015 then give
`solution_potential_spatialL2_le`:

```
||u_v,a(t) - u_w,c(t)||L2
  <= ||synth a - synth c||L2 + t * delta * ||synth c||L2.
```

Both potentials satisfy the original Exp014 regularity and Hermitian symmetry;
the operator difference is bounded by delta >= 0 and t >= 0. The fiber can be
any complete complex Hilbert space. Arbitrary initial mismatch is retained.
No derivative bound on V-W, evolving weighted-norm bound, nonzero mass premise
or exponential growth factor is introduced.

The immediate consumer is `PotentialErrorTransfer` for the actual two-component
ordered A-half/B-full/A-half trajectory, with parameters k/4,k/2,k/4, odd grid
2M+1 and (2M+1)h=2*pi. Both runs use the actual point samples of the same
original Fourier state a. Define E_v to be physical L2 error of the actual
Fourier-interpolated numerical grid state against Exp014.solution v a. The
symmetric coefficient cutoff v_R satisfies the required regularity and
Hermitian symmetry by the already accepted PotentialCutoff module.

`sampledCayley_gridTime_cutoff_error_transfer` proves, for nonnegative steps
totaling the actual grid time T:

```
E_v <= E_v_R + 2*T*sqrt(2*pi)*||a||*tail_v(R),
tail_v(R) = sum_{|ell|>R} ||v_ell||.
```

The weighted corollary replaces tail_v(R) by
`W_v/(1+R)^2`, where `W_v = sum_ell (1+|ell|)^2*||v_ell||`.
There is no h, M, Laplacian norm or R<=M restriction in this transfer cost.
The intermediate theorem also retains arbitrary signed step lengths through
`sum |k_j| + t`, with explicit comparison time t>=0. The final corollary proves
the grid-time and step-sum agreement rather than assuming it.

## Doors opened and remaining obligation

This is ACTUAL SCHEME INSTANTIATED for the potential-approximation transfer.
E_v_R is the actual remaining cutoff solver error, not a smallness assumption
hidden in an interface. It still must be bounded and shown to vanish. These
theorems do not prove full numerical convergence or between-grid-time stability
of the quadratic reconstruction. Analytical infinite-coefficient tails are not
automatically computable validated numerical certificates.

The baseline route remains smooth Fourier approximation plus uniform stability.
Fix the approximation cutoff before refining the numerical mesh. Finite Fourier
input or potential support does not imply an invariant finite solution band.
The smooth-core comparison requires justified evolving regularity or tail bounds,
and any further initial-data approximation requires its own stability bridge.
The already proved sampling estimate handles actual initialization, not evolving
derivatives. Stronger-data quantitative rates remain distinct from qualitative
convergence under the original data/potential assumptions.

The next inexpensive concrete obligation is the induced kinetic bound
`||A_h|| <= 4/h^2+1`, using the accepted Fourier diagonalization and Parseval
identities, then substitution into the existing temporal budget along the
recorded schedule. The main remaining spatial barrier is smooth-core consistency
with bounds that are uniform under mesh refinement. The existing single defect
table in PLAN.md tracks those obligations and their explicit resolution dependence.

## Evidence and recovery scope

The three new source-bound module checks request eleven axiom reports, including
the actual error definition; they are not eleven separate convergence results.
All reported dependencies are within propext, Classical.choice and Quot.sound.
There are two unused-section-variable style warnings and no accepted-run errors.
Rejected continuum elaboration evidence remains preserved separately.

The Colab proxy binding expired after the accepted continuum compiler run.
Only the local connection was restored; the same boot and exact accepted archive
hash were read back before evidence installation. No VM or proof was restarted.
The continuum workflow manifest was prepared after the run for strict received-
evidence validation; PREPARATION_TIMING.json records that distinction without
changing the original compiler timestamps or claiming a pre-run manifest.

Frequent checksum-verified local snapshots continue, with a manual milestone
checkpoint and a curated dev/variable-potential Git checkpoint. Git readback
receipts identify the exact remotely preserved source/receipt/log mapping.
The watcher requires manual restart after a reboot; Google Drive remains canceled.
Main, sealed predecessor packets and existing heavyweight archival branches are
unchanged. No Exp016 verified tag or release is authorized by this development check.
