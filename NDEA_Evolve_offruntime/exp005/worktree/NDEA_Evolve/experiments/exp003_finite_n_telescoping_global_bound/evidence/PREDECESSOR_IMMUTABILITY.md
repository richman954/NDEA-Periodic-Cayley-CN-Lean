# Predecessor immutability receipt

Required predecessor:

- commit: `e4dc7128c4651974bbab405726e586b04fb9b3dc`;
- annotated tag:
  `exp003-step3-exact-split-unsplit-cayley-defect-verified-final-20260907`;
- tag object: `a9c5802cd1aa67c6feada06c2a5d021b29e20f61`;
- peeled tag target: `e4dc7128c4651974bbab405726e586b04fb9b3dc`.

The separate Step 3 worktree at
`/home/richman954/NDEA_Evolve_offruntime/exp003_step3/worktree/NDEA_Evolve`
reported HEAD `e4dc7128c4651974bbab405726e586b04fb9b3dc` and an empty porcelain
status. The required commit is an ancestor of the Step 4 branch.

A zero-exit `git diff --exit-code` from the required commit covered all prior
Exp002 and Exp003 production/evidence directories together with:

- `NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean`;
- `NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean`;
- `NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean`;
- `lakefile.toml`;
- `lake-manifest.json`;
- `lean-toolchain`.

Thus predecessor production modules, historical manifests/evidence, release
material, and pinned project metadata were not edited. Every difference from
the predecessor is an addition confined to the new Step 4 production module
or Step 4 experiment directory.
