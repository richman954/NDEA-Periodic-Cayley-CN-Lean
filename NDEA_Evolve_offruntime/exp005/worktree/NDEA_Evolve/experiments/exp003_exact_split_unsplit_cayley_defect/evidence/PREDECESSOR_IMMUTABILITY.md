# Predecessor immutability receipt

Required predecessor:

- commit: `b28aabe00cc6a65da8043f71353cf8d496b27379`;
- annotated tag:
  `exp003-step2-exact-order-defect-opnorm-bound-verified-final-20260907`;
- tag object: `38be67791edff6efb06efecb1bc593d30a648a4d`;
- peeled tag target: `b28aabe00cc6a65da8043f71353cf8d496b27379`.

The separate Step 2 worktree at
`/home/richman954/NDEA_Evolve_offruntime/exp003_step2/worktree/NDEA_Evolve`
reported HEAD `b28aabe00cc6a65da8043f71353cf8d496b27379` and an empty porcelain
status. The required commit is an ancestor of the Step 3 branch.

A zero-exit `git diff --exit-code` from the required commit covered all prior
Exp002, Step 1, and Step 2 production/evidence directories together with:

- `NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean`;
- `NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean`;
- `lakefile.toml`;
- `lake-manifest.json`;
- `lean-toolchain`.

Thus predecessor production modules, historical evidence, release material,
and pinned project metadata were not edited. Import-adjusted copies used for
RAM verification already belonged to the immutable Step 2 release and are
documented separately; they do not replace or modify predecessor sources.
