#!/usr/bin/env bash
set -euo pipefail

stage=${1:-production}
repo=/home/richman954/NDEA_Evolve_offruntime/exp003_step4/worktree/NDEA_Evolve
packages=/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages
toolchain=/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/lib/lean
step2="$repo/experiments/exp003_exact_order_defect_norm_bound"
step4="$repo/experiments/exp003_finite_n_telescoping_global_bound"
shadow="$step2/proof_attempts/shadow_sources"
ram=/dev/shm/exp003_step4_shadow
ram_lib="$ram/lib/lean"

mkdir -p "$ram_lib/NDEAEvolve/Experiments/Exp002" \
  "$ram_lib/NDEAEvolve/Experiments/Exp003"

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
  Mathlib.Algebra.BigOperators.Group.Finset.Basic
  Mathlib.LinearAlgebra.Matrix.Hermitian
  Mathlib.LinearAlgebra.Matrix.PosDef
  Mathlib.Tactic.NoncommRing
  Mathlib.Tactic.FinCases
  Mathlib.Tactic.Module
  Mathlib.Tactic.NormNum
  Mathlib.Tactic.Ring
)

python3 "$step2/assurance/lean_import_closure.py" \
  "${roots[@]}" "${artifacts[@]}" --copy-artifacts-to "$ram_lib" \
  "${modules[@]}" >/dev/null

export LEAN_PATH="$ram_lib:$toolchain"

if [[ "$stage" == telescope-probe ]]; then
  timeout 300s lean -j 1 \
    "$step4/proof_attempts/TelescopingProbe.lean"
  exit 0
fi

if [[ "$stage" == norm-probe ]]; then
  timeout 300s lean -j 1 \
    "$step4/proof_attempts/NormProbe.lean"
  exit 0
fi

if [[ "$stage" == combined || "$stage" == combined-controls ]]; then
  combined="$ram/CombinedStep4Verification.lean"
  args=(--repo "$repo" --output "$combined")
  if [[ "$stage" == combined-controls ]]; then
    args+=(--controls)
  fi
  python3 "$step4/assurance/make_combined_verification.py" "${args[@]}"
  timeout 900s lean -j 1 "$combined"
  exit 0
fi

timeout 900s lean -j 1 -R "$shadow" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp002/OperatorCayley.olean" \
  "$shadow/NDEAEvolve/Experiments/Exp002/OperatorCayley.lean"

timeout 900s lean -j 1 -R "$shadow" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.olean" \
  "$shadow/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"

timeout 900s lean -j 1 -R "$repo" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.olean" \
  "$repo/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean"

timeout 900s lean -j 1 -R "$repo" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.olean" \
  "$repo/NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean"

timeout 900s lean -j 1 -R "$repo" \
  -o "$ram_lib/NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.olean" \
  "$repo/NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.lean"

if [[ "$stage" == production ]]; then
  exit 0
fi

timeout 900s lean -j 1 -R "$repo" \
  "$step4/controls/lean/NegativeControls.lean"
