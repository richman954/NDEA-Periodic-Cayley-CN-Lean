#!/usr/bin/env python3
"""Generate a transient one-process Step-2 verification source."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


IMPORTS = """\
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
"""


def filtered_source(path: Path, suppress_audit: bool) -> str:
    lines: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.lstrip()
        if stripped.startswith("import "):
            continue
        if suppress_audit and (stripped.startswith("#check ") or stripped.startswith("#print ")):
            continue
        lines.append(line)
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    experiment = args.repo / "experiments/exp003_exact_order_defect_norm_bound"
    shadow = experiment / "proof_attempts/shadow_sources"
    sources = [
        (shadow / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean", True),
        (shadow / "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean", True),
        (args.repo / "NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean", True),
        (shadow / "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean", True),
        (experiment / "controls/lean/NegativeControls.lean", False),
    ]

    chunks = [IMPORTS]
    for source, suppress_audit in sources:
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        chunks.append(f"\n-- BEGIN {source} SHA256 {digest}\n")
        chunks.append(filtered_source(source, suppress_audit))
        chunks.append(f"-- END {source}\n")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(chunks), encoding="utf-8")


if __name__ == "__main__":
    main()
