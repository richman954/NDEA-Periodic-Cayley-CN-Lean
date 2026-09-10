# Actual initial weights and spatial moments

Accepted 2026-09-10T02:00 UTC: InitialWeightedCutoff and WeightedSpatialMoments.
Exp016 now has 59 accepted development modules. The two successful checks
have 19 transitive standard-axiom reports, zero warnings and zero errors.
Exp016 remains unsealed; combined/fresh independent qualification is pending.

## Barrier removed

InitialWeightedCutoff constructs finite input coefficients as an actual
Exp014.FourierState using sealed ofCoefficients. It proves the exact coefficient
identity and specializes the existing sampledInitialState_eq_tsum to a finite
sampled mode sum. For any finite support s, arbitrary spinor coefficients c,
and physical odd grid N=2M+1 with N*h=2*pi, the proved bound is

`W_p(sampledInitialState M h (finiteInitialState s c)) <= I_p(s,c)`

where `I_p(s,c) = sum_{ell in s} (1+|ell|)^(2p) * ||c_ell||`.
There is no M or h in this initial constant. The original normalized complex
spinor DFT and actual sampling map are preserved, including unresolved aliases.
The proof uses AliasWeights's finite-sum and folded-mode inequalities; no
cutoff<=M condition or invariant finite solution band is assumed.

initialStateCutoff S a retains precisely |ell|<=S of the actual coefficients
of the original Exp014 state a. For fixed initial and potential cutoffs S,R,
the scheduled consumer combines the sampling bound with the actual ordered
A-half/B-full/A-half propagation theorem. Eventually every prefix j<=J on
the saved M=q+1, N=2M+1, h=2*pi/N, J=N^4, k=1/J schedule obeys

`W_p(y_j) <= exp(2*K_B) * I_p(S,a)`.

Here `K_B = cutoffPotentialWeight p R v + 1` and v has Hermitian Fourier
coefficients. The +1 includes the actual -Z contribution. The original a
remains in Exp014's second-moment class; higher moments are finite only after
cutoff. Potential and data cutoff sizes are fixed independently of the grid.

## Concrete spatial consumer

WeightedSpatialMoments connects p=2, the fourth weight, to the existing actual
certificate quantities. Pinned Mathlib's finite nonnegative-sum inequality
bounds the fourth l2 coefficient moment by W_2. The low coefficient sum is
bounded by W_p, and the strict high-frequency l1 sum satisfies

`gridTailCoefficientNorm M h y L <= W_2(y)/(1+L)^4`.

The complete potential-alias budget therefore obeys

`potentialAliasTailBudget <= (T_v(M-L) + A_v/(1+L)^4) * W_2(y)`,

with the original complete tail T_v and A_v=sum_ell ||v_ell||. The combined
stencil-plus-potential spatial budget, in the original physical L2 norm, is
bounded by `C_sp(M,L,h,v)*W_2(y)` for L<=M and Exp014.RegularPotential v, where

`C_sp = sqrt(2*pi)*h^2 + 2*sqrt(2*pi)*(T_v(M-L) + A_v/(1+L)^4)`.

The concrete endpoint consumer is
scheduledCayley_doubleCutoff_spatialBudget_eventually_le. It combines this
actual budget bound with the preceding scheduled trajectory theorem for
V_R and a_S. Its right-hand side is the explicit C_sp for V_R times
exp(2*K_B)*I_2(S,a). This is an endpoint budget estimate, not yet a proof that
the entire reconstructed slab's accumulated spatial residual vanishes.

## Doors opened, next move and remaining barrier

The next dependency is the quadratic slab bound. Bound the actual weighted
mean by (W_2(y_j)+W_2(y_{j+1}))/2 and k*W_2(velocity) by that endpoint sum.
Use the actual kinetic coefficient identity and cutoff potential bound to
control W_2(H*velocity), retaining its h-dependent coefficient. Then substitute
all three estimates into the actual spatial contribution. In particular, the
k^2 generator-velocity factor should expose k*h^(-2), which must be proved
controlled on the existing schedule.

After that, prove the explicit scalar spatial coefficient tends to zero, for
example with the low cutoff floor(M/2), and deduce scheduledSpatialSum vanishing.
The general Exp014 theorem still needs the initial-data/potential approximation
quantifiers. Quadratic between-grid-time transfer, full combined and fresh
independent qualification, controls and sealing remain separate gates.
No recurrence, reconstruction, comparison norm or predecessor was changed.

## Source-bound checking

Use the existing runner in dependency order, from exp016:

```
python3 -u -B run_lean.py lean/InitialWeightedCutoff.lean
python3 -u -B run_lean.py lean/WeightedSpatialMoments.lean
```

The unchanged environment is Lean 4.31.0 with Mathlib
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Validate imports against their original
source-bound receipts before reproduction. Complete compiler logs, frozen
source hashes, artifact hashes and each public theorem's transitive axiom
dependencies are checked by evidence/initial_weighted_20260910/record_module.py.
The current development status must be read from actual accepted receipts.


| Module | Source SHA-256 | Accepted receipt / seconds |
|---|---|---|
| InitialWeightedCutoff | `8eeca84a6e7b4ed6b9604e69aec4af36642230e85370a670a58765432dabfafc` | [receipt](../evidence/20260910T014951.285496Z_InitialWeightedCutoff.json), 182.144 |
| WeightedSpatialMoments | `cc0f86efa732ca376a8565bdd78b35a626e0a1c8f3a0d73f2e2293d1ef9c7787` | [receipt](../evidence/20260910T015406.074914Z_WeightedSpatialMoments.json), 340.753 |

Every public theorem has a transitive axiom report containing only propext,
Classical.choice and Quot.sound; no accepted theorem uses sorryAx. The
[local milestone receipt](../evidence/INITIAL_WEIGHTED_MILESTONE_LOCAL.json)
binds both original checks and all 57 previous source/receipt/log/artifact
bindings, 130 import artifacts and 789 sealed Exp013–015 payloads/packets.

The first InitialWeightedCutoff attempt omitted the FourierGrid namespace
opening. Its exact source, three compiler errors, log and receipt are preserved
under attempts/initial_weighted_cutoff_r1. Its sorryAx dependency reports are
rejected evidence. The correction adds the missing namespace opening without
changing any theorem statement or assumption.

Manual recovery checkpoints precede long checks, and watcher session 27367
continues minute snapshots without reboot autostart. Git readback receipts
identify exact off-device coverage. Main, dependency pins and sealed Exp013–015
remain immutable. Comparator and an additional independent kernel are not run
by these modular development checks.
