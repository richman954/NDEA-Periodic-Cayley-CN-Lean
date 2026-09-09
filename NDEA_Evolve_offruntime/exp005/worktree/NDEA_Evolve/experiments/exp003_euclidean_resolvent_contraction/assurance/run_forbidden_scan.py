#!/usr/bin/env python3
"""Scan every Experiment 003 production Lean source for prohibited constructs."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path


FILES = (
    Path("NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"),
)
TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide", "sorryAx")
PATTERN = re.compile(r"\b(?:" + "|".join(map(re.escape, TOKENS)) + r")\b")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    if output.exists():
        raise SystemExit(f"refusing to overwrite {output}")
    records = []
    total = 0
    for relative in FILES:
        path = repo / relative
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"missing/nonregular production source: {path}")
        text = path.read_text(encoding="utf-8", errors="strict")
        matches = []
        for line_number, line in enumerate(text.splitlines(), 1):
            for match in PATTERN.finditer(line):
                matches.append(
                    {"line": line_number, "token": match.group(0), "text": line}
                )
        total += len(matches)
        records.append(
            {
                "path": relative.as_posix(),
                "size_bytes": path.stat().st_size,
                "sha256": sha256(path),
                "matches": matches,
            }
        )
    result = {
        "schema": "ndea.exp003.forbidden_token_scan.v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "status": "PASS" if total == 0 else "FAIL",
        "policy": {
            "case_sensitive": True,
            "whole_token": True,
            "comments_and_strings_included": True,
            "tokens": list(TOKENS),
        },
        "production_file_count": len(FILES),
        "total_matches": total,
        "files": records,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if total == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
