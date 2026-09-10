# Weighted sampled-potential control

Accepted September 10, 2026 UTC: AliasWeights and WeightedSampledPotential.
Exp016 now has 55 accepted development modules. The two checks have 18 transitive
standard-axiom reports, zero errors and one reviewed deprecation warning.
Exp016 remains unsealed; combined/fresh independent qualification is pending.

## Barrier removed

For the actual odd periodic grid, N = 2M+1 and N*h = 2*pi, write

`w_p(m) = Exp014.weight(m)^p = (1+|m|)^(2p)`

and

`W_p(y) = sum_r w_p(oddFrequency M r) * ||fourierCoefficient M h y r||`.

These are the existing normalized DFT coefficients in C², not a different
sampling convention. p = 2 gives the fourth weight needed for the stencil
moment. AliasWeights proves that the centered representative of any integer
frequency has no larger absolute frequency or weight. It also proves the
exact weighted sum for a sampled single mode and its bound by that input
mode's weight. This includes out-of-band aliases and the one-node grid.
The proof reuses GridAlias's unique representative and sealed Exp014.weight_add_le.

WeightedSampledPotential derives the finite shifted-mode expansion of the
actual sampled multiplication operator, starting from PotentialAlias's
accepted infinite-series identity and the stated finite support. It then
applies the new weighted bound to each mode and sums. The accepted consumer is

`W_p(P_(V_R) y) <= K_(p,R,v) * W_p(y)`

where `P_(V_R) = op(sampledBlock(2M,h,operatorPotentialMatrix(potentialCutoff R v)))`
and

`K_(p,R,v) = sum_{ell=-R}^R w_p(ell) * ||v_ell||`.

The constant depends on p, the fixed potential cutoff and its original
coefficients. It has no M, h or N factor. The grid state y is arbitrary;
there is no R <= M restriction and no invariant finite solution band.
The estimate does not require Hermitian symmetry; later actual unitary stage
propagation does. The original v is arbitrary in this finite-cutoff theorem.
It does not assert fourth weighted summability for the full Exp014 class.

## Doors opened, best next move, and remaining barrier

The immediate consumer is the weighted bound for the actual B factor:
`sampledSplitB = P_(V_R) - potential(Z)`. Add the coefficient-one Z bound,
weighted triangle/scalar properties, and the actual Cayley denominator equation.
For the A factors use sealed Exp008.FourierGrid.hamiltonian_step_modeLift and
the existing full-grid decomposition to prove weighted preservation.
The exact parameters remain k/4, k/2, k/4 in A-half/B-full/A-half order.

These bounds should next yield uniform finite-time weighted propagation for
each fixed smooth cutoff. That propagation, the spatial mean/velocity/generator
bounds, scheduledSpatialSum vanishing and approximation quantifiers remain
unproved. The accepted time-1 error certificate still retains its entire
spatial sum. No solver convergence or between-grid-time refinement is claimed.
See [the dependency-ordered route and inspected interfaces](NEXT_SPATIAL_ROUTE.md).

## Checks and reproduction

Use the unchanged runner, in this order, from exp016:

```
python3 -u -B run_lean.py lean/AliasWeights.lean
python3 -u -B run_lean.py lean/WeightedSampledPotential.lean
```

The environment is Lean 4.31.0 with Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Validate imported artifacts against
their original source-bound receipts first. The new module validator is
`evidence/weighted_spatial_20260910/record_module.py`; it checks every public
theorem's transitive `#print axioms` report, source immutability, compiler/runner
pins, receipt/log/artifact hashes and the entire prior accepted inventory.
This is modular development acceptance, distinct from final qualification.

| Module | Source SHA-256 | Accepted check |
|---|---|---|
| AliasWeights | `d08415815901fd965fc874e7251d829e84502ef92c06804c334f74d10e8894cd` | [receipt](../evidence/20260910T005923.091644Z_AliasWeights.json), 277.093 seconds, no warnings |
| WeightedSampledPotential | `7724ee352eacf9d6af7bc30f237c14252522e6448dc50bcfdb9a4535a04eaaa7` | [receipt](../evidence/20260910T010421.237392Z_WeightedSampledPotential.json), 181.195 seconds, one deprecation warning |

Every accepted theorem depends only on propext, Classical.choice and Quot.sound.
The single warning concerns ContinuousLinearMap.zero_apply, confirmed at line
343 of pinned Mathlib's ContinuousLinearMap/Basic.lean to be a deprecated alias
of the same zero_apply theorem. The source is retained exactly as checked.
The [local milestone receipt](../evidence/WEIGHTED_SPATIAL_MILESTONE_LOCAL.json)
binds the original receipts, full logs, artifacts and warning review.

The first AliasWeights attempt is preserved in attempts/alias_weights_r1.
Its two script errors, warning and failed sorryAx reports are rejected evidence.
No upstream code or new dependency is imported. No old proof, Comparator or
additional independent kernel has been run for this milestone.

Manual snapshots precede each long check. Watcher session 27367 continues
minute snapshots and has no reboot autostart. The eventual dated local and Git
readback receipts determine exact coverage; main and sealed predecessors remain
unchanged.
