#!/usr/bin/env bash
set -euo pipefail

stage=${1:-production}
repo=/home/richman954/NDEA_Evolve_offruntime/exp003_step2/worktree/NDEA_Evolve
packages=/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages
toolchain=/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/lib/lean
shadow="$repo/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources"
ram=/dev/shm/exp003_step2_shadow
ram_lib="$ram/lib/lean"

mkdir -p "$ram_lib/NDEAEvolve/Experiments/Exp002" "$ram_lib/NDEAEvolve/Experiments/Exp003"

roots=(
  --root "$packages/mathlib"
  --root "$packages/batteries"
  --root "$packages/Qq"
  --root "$packages/aesop"
  --root "$packages/proofwidgets"
  --root "$packages/importGraph"
  --root "$packages/LeanSearchClient"
  --root "$packages/plausible"
)
artifacts=(
  --artifact-root "$packages/mathlib/.lake/build/lib/lean"
  --artifact-root "$packages/batteries/.lake/build/lib/lean"
  --artifact-root "$packages/Qq/.lake/build/lib/lean"
  --artifact-root "$packages/aesop/.lake/build/lib/lean"
  --artifact-root "$packages/proofwidgets/.lake/build/lib/lean"
  --artifact-root "$packages/importGraph/.lake/build/lib/lean"
  --artifact-root "$packages/LeanSearchClient/.lake/build/lib/lean"
  --artifact-root "$packages/plausible/.lake/build/lib/lean"
)
modules=(
  Mathlib.Analysis.CStarAlgebra.Matrix
  Mathlib.LinearAlgebra.Matrix.Hermitian
  Mathlib.LinearAlgebra.Matrix.PosDef
  Mathlib.Tactic.NoncommRing
  Mathlib.Tactic.FinCases
  Mathlib.Tactic.Module
  Mathlib.Tactic.NormNum
  Mathlib.Tactic.Ring
)

python3 "$repo/experiments/exp003_exact_order_defect_norm_bound/assurance/lean_import_closure.py" \
  "${roots[@]}" "${artifacts[@]}" --copy-artifacts-to "$ram_lib" "${modules[@]}" >/dev/null

export LEAN_PATH="$ram_lib:$toolchain"

if [[ "$stage" == combined-controls ]]; then
  combined="$ram/CombinedStep2Verification.lean"
  python3 "$repo/experiments/exp003_exact_order_defect_norm_bound/assurance/make_combined_verification.py" \
    --repo "$repo" --output "$combined"
  timeout 900s lean -j 1 "$combined"
  exit 0
fi

timeout 900s lean -j 1 -R "$shadow" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp002/OperatorCayley.olean" \
  "$shadow/NDEAEvolve/Experiments/Exp002/OperatorCayley.lean"

if [[ "$stage" == operator ]]; then
  exit 0
fi

timeout 900s lean -j 1 -R "$shadow" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.olean" \
  "$shadow/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"

if [[ "$stage" == step1 ]]; then
  exit 0
fi

timeout 900s lean -j 1 -R "$repo" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.olean" \
  "$repo/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean"

if [[ "$stage" == production ]]; then
  exit 0
fi

timeout 900s lean -j 1 -R "$shadow" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.olean" \
  "$shadow/NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean"

timeout 900s lean -j 1 -R "$repo" \
  "$repo/experiments/exp003_exact_order_defect_norm_bound/controls/lean/NegativeControls.lean"
