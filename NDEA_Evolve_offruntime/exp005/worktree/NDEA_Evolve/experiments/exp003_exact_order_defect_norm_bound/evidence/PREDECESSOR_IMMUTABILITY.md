# Predecessor immutability receipt

Required predecessor:

- commit: `638f13d2394fea1a3ebd44a0ab38096e9758f294`;
- annotated tag:
  `exp003-step1-euclidean-resolvent-contraction-verified-final-20260906`;
- tag object: `fe7fc8f43a5304956b04d74b0268b10ae493db5c`;
- peeled tag target: `638f13d2394fea1a3ebd44a0ab38096e9758f294`.

The separate Step 1 worktree at
`/home/richman954/NDEA_Evolve_offruntime/exp003/worktree/NDEA_Evolve` reported
HEAD `638f13d2394fea1a3ebd44a0ab38096e9758f294` and an empty porcelain status.
The required commit is an ancestor of the Step 2 branch.

A zero-exit `git diff --exit-code` from the required commit to the Step 2
checkpoint covered:

- `NDEAEvolve/Experiments/Exp002/OperatorCayley.lean`;
- `NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean`;
- `NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean`;
- `lakefile.toml`;
- `lake-manifest.json`;
- `lean-toolchain`.

Thus the predecessor production sources and pinned project metadata were not
edited. Import-adjusted copies used for the RAM verification are isolated under
the Step 2 `proof_attempts/shadow_sources` directory and are documented
separately; they do not replace or modify the predecessor.
