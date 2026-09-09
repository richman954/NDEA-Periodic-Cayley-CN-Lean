# Experiment 004 — symmetric Cayley second-order comparison

The symmetric step is

`S_h = Chat A (h/4) * Chat B (h/2) * Chat A (h/4)`.

For Hermitian A,B, put `M=‖operatorOf A‖+‖operatorOf B‖`. The fixed-time
bound is `1000 |t|³ M³/N²`, for N>0 with `2|t|M≤N`, in the induced
continuous-linear-map norm. The corresponding operator-norm convergence
includes every finite dimension, including zero, and every real time.

The [final evaluation](FINAL_EVALUATION_REPORT.md) gives the release verdict,
qualifying verification records, controls, and scope boundaries.

- [Frozen plan and specification](PLAN.md).
- [Mathematical derivation](MATHEMATICAL_DERIVATION.md).
- [Local proof](../../NDEAEvolve/Experiments/Exp004/SymmetricCayleyLocal.lean).
- [Global bound and limit](../../NDEAEvolve/Experiments/Exp004/SymmetricCayleyGlobal.lean).
- [Controls](controls/lean/NegativeControls.lean).
- [Theorem map](evidence/THEOREM_MAP.md).
- [Verification and recovery instructions](assurance/README.md).
- [Development failure/repair history](FAILURE_AND_REPAIR_LOG.md).

The immutable predecessor is Experiment 003 Step 5 commit
`3a5078a02bbc1423a302016d4e14c78f874f021f`.
The off-tree release directory is
`NDEA_Evolve_offruntime/exp004/releases/20260907_verified_final`.
Its `DELIVERY_RECEIPT.json` is the authority for final commit/tag identity,
archive and bundle hashes, and fresh local recovery results.
