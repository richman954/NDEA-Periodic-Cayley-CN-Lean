#!/usr/bin/env python3
"""List the transitive source-import closure for selected Lean modules."""

from __future__ import annotations

import argparse
import re
import shutil
from pathlib import Path


IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s]+)"
)


def header_imports(text: str) -> list[str]:
    """Read import commands before the first substantive non-import command."""
    imports: list[str] = []
    block_depth = 0
    for raw_line in text.splitlines():
        line: list[str] = []
        index = 0
        while index < len(raw_line):
            pair = raw_line[index : index + 2]
            if block_depth:
                if pair == "/-":
                    block_depth += 1
                    index += 2
                elif pair == "-/":
                    block_depth -= 1
                    index += 2
                else:
                    index += 1
            elif pair == "/-":
                block_depth = 1
                index += 2
            elif pair == "--":
                break
            else:
                line.append(raw_line[index])
                index += 1
        content = "".join(line).strip()
        if not content:
            continue
        if content in {"module", "prelude"}:
            continue
        match = IMPORT_RE.match(content)
        if match:
            imports.append(match.group(1))
        else:
            break
    return imports


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--root", action="append", type=Path, required=True)
    parser.add_argument("--artifact-root", action="append", type=Path, default=[])
    parser.add_argument("--copy-artifacts-to", type=Path)
    parser.add_argument("--report-artifact-bytes", action="store_true")
    args = parser.parse_args()

    pending = list(args.modules)
    seen: set[str] = set()
    missing: set[str] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = next((root / relative for root in args.root if (root / relative).is_file()), None)
        if source is None:
            missing.add(module)
            continue
        pending.extend(header_imports(source.read_text(encoding="utf-8")))

    resolved = sorted(seen - missing)
    artifact_bytes = 0
    artifact_count = 0
    for module in resolved:
        print(module)
        relative = Path(*module.split("."))
        for suffix in (".olean", ".olean.private", ".olean.server", ".ir"):
            artifact_relative = relative.with_suffix(suffix)
            artifact = next(
                (root / artifact_relative for root in args.artifact_root
                 if (root / artifact_relative).is_file()),
                None,
            )
            if artifact is None:
                continue
            artifact_bytes += artifact.stat().st_size
            artifact_count += 1
            if args.copy_artifacts_to is not None:
                target = args.copy_artifacts_to / artifact_relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(artifact, target)
    if missing:
        print("# unresolved (normally Lean core modules)")
        for module in sorted(missing):
            print(f"# {module}")
    if args.report_artifact_bytes:
        print(f"# artifacts {artifact_count} bytes {artifact_bytes}")


if __name__ == "__main__":
    main()
