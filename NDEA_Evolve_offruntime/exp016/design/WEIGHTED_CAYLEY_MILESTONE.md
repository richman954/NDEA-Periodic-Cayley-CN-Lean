# Actual weighted Cayley propagation

Accepted September 10, 2026 UTC: WeightedGridStages and
WeightedCayleyPropagation. Exp016 now has 57 accepted development modules.
The two new checks have 23 transitive standard-axiom reports, zero errors,
and two reviewed warnings. Exp016 remains unsealed; full combined and fresh
independent qualification are pending.

## Barrier removed

Use the existing normalized complex-spinor DFT on N=2M+1, N*h=2*pi:

`W_p(y) = sum_r (1+|oddFrequency M r|)^(2p) * ||fourierCoefficient M h y r||`.

For a fixed symmetric potential cutoff V_R with Hermitian Fourier coefficients,
write `K_B = 1 + sum_{ell=-R}^R (1+|ell|)^(2p) * ||v_ell||`.
The extra one accounts for the actual -Z contribution in sampledSplitB.
The original coefficients outside the cutoff need no higher moment assumption.

WeightedGridStages proves weighted triangle and scalar properties and the
actual coefficient action of constant blocks and Cayley factors. It reuses
sealed Exp008.FourierGrid.hamiltonian_step_modeLift and the accepted full-grid
mode decomposition. The actual kinetic-plus-Z A factors preserve W_p exactly;
the actual B operator satisfies W_p(B*y) <= K_B*W_p(y). The constant is independent
of M and h; there is no R<=M condition or invariant finite solution band.

WeightedCayleyPropagation uses the actual denominator equation to prove the
weighted Cayley factor (1+|alpha|*K)/(1-|alpha|*K) when |alpha|*K<1.
For |alpha|*K<=1/2 this is at most exp(4*|alpha|*K).
With the actual ordered parameters k/4, k/2, k/4, the resulting consumer is

`W_p(y_j) <= exp(2*K_B*sum_{i<j}|k_i|) * W_p(y_0)`

for the actual sampledCayleyTrajectory, provided |k_i|*K_B<=1 on that prefix.
Signed variable steps are allowed. Hermitian symmetry is used for the actual
Cayley solves and mode unitarity; no weighted resolvent premise replaces them.

The scheduled consumer proves that this restriction eventually holds on the
existing M=q+1, N=2M+1, h=2*pi/N, J=N^4, k=1/J family. Eventually, every actual
prefix j<=J satisfies `W_p(y_j) <= exp(2*K_B)*W_p(y_0)`. The initial grid states
may form an arbitrary family: their initial weighted amplitude remains explicit.
This proves propagation, not a uniform initial bound or spatial convergence.

## Doors opened and best next move

For p=2, this is the fourth weighted numerical Fourier sum needed by the
accepted stencil and potential-tail bounds. The next small proof should turn
actual samples of fixed finite initial-data cutoffs into a uniform initial
W_2 bound. SamplingExpansion.sampledInitialState_eq_tsum supplies the exact
sampled series; AliasWeights supplies the finite-sum and folded-mode bounds.
Construct the cutoff as an actual Exp014.FourierState via ofCoefficients and
prove its coefficient identity. Folding already decreases weights, so the
initial estimate need not wait for the grid to resolve the cutoff.

That estimate can feed
scheduledCayley_cutoff_fourierWeightedNorm_eventually_le directly. Then derive
fourth-frequency l2 moments and low/high l1 coefficient bounds for the actual
endpoint states, slab mean, velocity and generator-velocity. The actual
scheduledSpatialSum must still be proved to vanish. General Exp014 data require
the explicit approximation/stability quantifiers; second moments are not
silently promoted to fourth moments. Full solver convergence and quadratic
between-grid-time refinement remain open.

## Checks and reproduction

From exp016, after validating imported artifacts against original receipts:

```
python3 -u -B run_lean.py lean/WeightedGridStages.lean
python3 -u -B run_lean.py lean/WeightedCayleyPropagation.lean
```

Use Lean 4.31.0 and Mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The unchanged runner uses one Lean job and records source hashes before/after,
compiler/runner pins, artifact hashes, full output and elapsed time.

| Module | Source SHA-256 | Original accepted receipt |
|---|---|---|
| WeightedGridStages | `8ff03d880d61fd7ec268eb0f1a4cb882fb1ed78e065277f3a7f0102a2b631922` | [receipt](../evidence/20260910T011949.617500Z_WeightedGridStages.json), 243.643 seconds, 13 reports |
| WeightedCayleyPropagation | `4ce349b8ad10e982675ab2d85af5e1faf4343c390f0d1acc000dea750f68a4fe` | [receipt](../evidence/20260910T012618.779160Z_WeightedCayleyPropagation.json), 165.679 seconds, 10 reports |

Every public theorem's transitive axiom report contains only propext,
Classical.choice and Quot.sound. No sorryAx occurs. WeightedGridStages has one
deprecated ContinuousLinearMap.sub_apply name; pinned Mathlib identifies it as
an alias of the same sub_apply theorem. WeightedCayleyPropagation has one
unnecessarySeqFocus style warning for `congr 2 <;> ring`. Both original sources
remain exactly as accepted; no failed attempt occurred in these two checks.

The [local milestone receipt](../evidence/WEIGHTED_CAYLEY_MILESTONE_LOCAL.json)
binds the original sources, receipts, artifacts and logs, plus warning reviews.
The validator checks all 55 prior accepted bindings, 128 preexisting project
import artifacts and all 789 sealed Exp013–015 payloads/packet hashes.
No dependency pin or upstream reference changed. Comparator and an additional
independent kernel were not run. This is modular development acceptance.

## Recovery state

Verified manual checkpoints precede both long checks. The tracked automatic
watcher is session 27367, with 60-second intervals and no reboot autostart.
Dated checkpoint and Git readback receipts determine precise backup coverage.
Use dev/variable-potential; preserve main and the sealed archive branches.
