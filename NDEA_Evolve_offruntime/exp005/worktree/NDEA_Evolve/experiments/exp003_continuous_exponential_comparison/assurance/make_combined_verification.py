#!/usr/bin/env python3
"""Generate one-process Step-5 verification from the recorded source files."""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


EXPERIMENT = "experiments/exp003_continuous_exponential_comparison"
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$")
BASE_IMPORTS = (
    "Mathlib.Analysis.CStarAlgebra.Matrix",
    "Mathlib.Algebra.BigOperators.Group.Finset.Basic",
    "Mathlib.LinearAlgebra.Matrix.Hermitian",
    "Mathlib.LinearAlgebra.Matrix.PosDef",
    "Mathlib.Analysis.Normed.Algebra.Exponential",
    "Mathlib.Analysis.SpecificLimits.Basic",
    "Mathlib.Analysis.Normed.Group.Continuity",
    "Mathlib.Tactic.FinCases",
    "Mathlib.Tactic.Module",
    "Mathlib.Tactic.NoncommRing",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Ring",
    "Lean.Elab.Tactic.Omega",
)


def source_groups(repo: Path) -> tuple[list[Path], list[Path]]:
    shadow = repo / "experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources"
    predecessor = [
        shadow / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean",
        shadow / "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean",
        repo / "NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean",
        repo / "NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean",
        repo / "NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.lean",
    ]
    production = [
        repo / "NDEAEvolve/Experiments/Exp003/ExponentialRemainder.lean",
        repo / "NDEAEvolve/Experiments/Exp003/ContinuousExponentialComparison.lean",
        repo / "NDEAEvolve/Experiments/Exp003/ContinuousExponentialLimit.lean",
    ]
    return predecessor, production


def external_imports(sources: list[Path]) -> list[str]:
    imports = set(BASE_IMPORTS)
    for source in sources:
        if not source.is_file():
            continue
        for line in source.read_text(encoding="utf-8").splitlines():
            match = IMPORT_RE.match(line)
            if match:
                for module in match.group(1).split("--", 1)[0].split():
                    if not module.startswith("NDEAEvolve."):
                        imports.add(module)
    return sorted(imports)


def filtered_source(path: Path, suppress_audit: bool) -> str:
    lines: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if IMPORT_RE.match(line):
            continue
        stripped = line.lstrip()
        if suppress_audit and (stripped.startswith("#check ") or stripped.startswith("#print ")):
            continue
        lines.append(line)
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--controls", action="store_true")
    args = parser.parse_args()
    predecessor, production = source_groups(args.repo.resolve())
    sources = [(path, True) for path in predecessor] + [(path, False) for path in production]
    if args.controls:
        sources.append((args.repo / EXPERIMENT / "controls/lean/NegativeControls.lean", False))
    imports = external_imports([path for path, _ in sources])
    chunks = ["".join(f"import {module}\n" for module in imports)]
    for source, suppress_audit in sources:
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        chunks.append(f"\n-- BEGIN {source} SHA256 {digest}\n")
        chunks.append(filtered_source(source, suppress_audit))
        chunks.append(f"-- END {source}\n")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(chunks), encoding="utf-8")


if __name__ == "__main__":
    main()
