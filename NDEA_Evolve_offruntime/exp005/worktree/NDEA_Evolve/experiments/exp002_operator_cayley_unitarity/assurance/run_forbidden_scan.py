#!/usr/bin/env python3
"""Strictly scan the two production Lean sources for forbidden proof shortcuts."""

from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
FILES = [
    REPO / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean",
    REPO / "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean",
]
TOKENS = ["sorry", "admit", "axiom", "unsafe", "native_decide"]
PATTERN = re.compile(r"\b(?:" + "|".join(map(re.escape, TOKENS)) + r")\b")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    records = []
    total_matches = 0
    for path in FILES:
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"production source missing or symlinked: {path}")
        matches = []
        for number, line in enumerate(path.read_text().splitlines(), 1):
            for match in PATTERN.finditer(line):
                matches.append({"line": number, "token": match.group(0), "text": line})
        total_matches += len(matches)
        records.append(
            {
                "path": str(path.relative_to(REPO)),
                "size_bytes": path.stat().st_size,
                "sha256": sha256(path),
                "matches": matches,
            }
        )
    result = {
        "schema": "ndea.exp002.forbidden_token_scan.v1",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "policy": {
            "case_sensitive": True,
            "matching": "Unicode word-boundary full token",
            "scan_includes_comments_and_strings": True,
            "tokens": TOKENS,
        },
        "production_file_count": len(FILES),
        "total_matches": total_matches,
        "status": "PASS" if total_matches == 0 else "FAIL",
        "files": records,
    }
    output = HERE / "final_forbidden_scan.json"
    if output.exists():
        raise SystemExit(f"refusing to overwrite existing result: {output}")
    with output.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if total_matches == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
