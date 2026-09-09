#!/usr/bin/env python3
"""Strictly parse the three Step-1 signatures and transitive dependency reports."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path


DECLARATIONS = (
    "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_eq_average",
    "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_apply_norm_le",
    "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_opNorm_le_one",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BEGIN = '"NDEA_EXP003_AUDIT_BEGIN" : String'
END = '"NDEA_EXP003_AUDIT_END" : String'
AXIOM_BLOCK = re.compile(
    r"^'([^'\n]+)' depends on axioms: \[([A-Za-z0-9_.,\s]*)\]$",
    re.MULTILINE,
)
NO_AXIOM = re.compile(
    r"^'([^'\n]+)' does not depend on any axioms$", re.MULTILINE
)
AXIOM_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")
LEAN_INFO_PREFIX = re.compile(
    r"^info: NDEAEvolve/Experiments/Exp003/"
    r"EuclideanResolventContraction\.lean:[0-9]+:[0-9]+: "
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def fail(reason: str) -> None:
    raise SystemExit(f"EXP003_SIGNATURE_AXIOM_AUDIT=FAIL\nREASON={reason}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    log = args.log.resolve()
    output = args.output.resolve()
    if output.exists():
        fail(f"refusing to overwrite {output}")
    try:
        text = log.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        fail(f"cannot read strict UTF-8 log: {error}")
    raw_lines = text.splitlines()
    prefixed_begin = sum(
        LEAN_INFO_PREFIX.match(line) is not None
        and LEAN_INFO_PREFIX.sub("", line, count=1) == BEGIN
        for line in raw_lines
    )
    prefixed_end = sum(
        LEAN_INFO_PREFIX.match(line) is not None
        and LEAN_INFO_PREFIX.sub("", line, count=1) == END
        for line in raw_lines
    )
    if prefixed_begin != 1 or prefixed_end != 1:
        fail("expected exactly one source-prefixed audit marker pair")
    normalized_prefix_count = sum(
        LEAN_INFO_PREFIX.match(line) is not None for line in raw_lines
    )
    text = "\n".join(
        LEAN_INFO_PREFIX.sub("", line, count=1) for line in raw_lines
    )
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        fail("expected exactly one audit marker pair")
    begin = text.index(BEGIN) + len(BEGIN)
    end = text.index(END, begin)
    region = text[begin:end]

    lines = region.splitlines()
    signature_starts: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        for name in DECLARATIONS:
            if line.startswith("@" + name + " :"):
                signature_starts.append((index, name))
    if tuple(name for _, name in signature_starts) != DECLARATIONS:
        fail(f"signature sequence mismatch: {signature_starts!r}")

    signatures: dict[str, str] = {}
    first_print = next(
        (i for i, line in enumerate(lines) if line.startswith("theorem ")), len(lines)
    )
    for offset, (start, name) in enumerate(signature_starts):
        stop = (
            signature_starts[offset + 1][0]
            if offset + 1 < len(signature_starts)
            else first_print
        )
        signature = "\n".join(lines[start:stop]).strip()
        if not signature.startswith("@" + name + " :"):
            fail(f"malformed signature for {name}")
        signatures[name] = signature

    printed = [
        name
        for line in lines
        for name in DECLARATIONS
        if line.startswith("theorem " + name + " :")
    ]
    if tuple(printed) != DECLARATIONS:
        fail(f"#print declaration sequence mismatch: {printed!r}")

    rows: dict[str, list[str]] = {}
    for match in AXIOM_BLOCK.finditer(region):
        name, payload = match.groups()
        values = [] if not payload.strip() else [item.strip() for item in payload.split(",")]
        if not values or any(AXIOM_NAME.fullmatch(value) is None for value in values):
            fail(f"malformed dependency list for {name}: {values!r}")
        if len(values) != len(set(values)) or name in rows:
            fail(f"duplicate dependency data for {name}")
        rows[name] = values
    for match in NO_AXIOM.finditer(region):
        name = match.group(1)
        if name in rows:
            fail(f"duplicate dependency report for {name}")
        rows[name] = []
    if set(rows) != set(DECLARATIONS) or len(rows) != len(DECLARATIONS):
        fail(
            "dependency declaration mismatch: "
            f"missing={sorted(set(DECLARATIONS) - set(rows))!r}, "
            f"extra={sorted(set(rows) - set(DECLARATIONS))!r}"
        )
    unexpected = sorted({value for values in rows.values() for value in values} - ALLOWED)
    status = "PASS" if not unexpected else "FAIL"
    result = {
        "schema": "ndea.exp003.signature_axiom_audit.v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "status": status,
        "source_log": str(log),
        "source_log_sha256": sha256(log),
        "audit_marker_pair_count": 1,
        "normalized_source_info_prefix_count": normalized_prefix_count,
        "headline_declaration_count": len(DECLARATIONS),
        "allowed_dependencies": sorted(ALLOWED),
        "unexpected_dependencies": unexpected,
        "declarations": [
            {"name": name, "signature": signatures[name], "dependencies": rows[name]}
            for name in DECLARATIONS
        ],
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
