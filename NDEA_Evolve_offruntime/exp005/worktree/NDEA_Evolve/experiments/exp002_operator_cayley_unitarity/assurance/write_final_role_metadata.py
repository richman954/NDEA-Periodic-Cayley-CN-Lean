#!/usr/bin/env python3
"""Write one fail-closed Lean assurance-role metadata record."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
ROLES = {
    "production_build",
    "positive_witness",
    "axiom_audit",
    "negative_controls",
    "forbidden_scan",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command_output(argv: list[str]) -> str:
    run = subprocess.run(argv, cwd=REPO, text=True, capture_output=True, check=False)
    if run.returncode != 0:
        raise SystemExit(f"version command failed ({run.returncode}): {argv!r}: {run.stderr}")
    return (run.stdout + run.stderr).strip()


def resolve_tool(env_name: str, default_name: str) -> str:
    candidate = os.environ.get(env_name) or shutil.which(default_name)
    if not candidate:
        raise SystemExit(f"{default_name} NOT FOUND: set {env_name} or update PATH")
    return str(Path(candidate).resolve())


def set_dotted(target: dict, dotted: str, value: str) -> None:
    parts = dotted.split(".")
    if not parts or any(not part for part in parts):
        raise SystemExit(f"invalid dotted binding field: {dotted!r}")
    cursor = target
    for part in parts[:-1]:
        next_value = cursor.setdefault(part, {})
        if not isinstance(next_value, dict):
            raise SystemExit(f"binding field collision at {dotted!r}")
        cursor = next_value
    if parts[-1] in cursor:
        raise SystemExit(f"duplicate binding field: {dotted!r}")
    cursor[parts[-1]] = value


def relative_regular(raw: str) -> tuple[str, Path]:
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts or str(relative) in {"", "."}:
        raise SystemExit(f"binding path must be canonical and repository-relative: {raw!r}")
    path = REPO / relative
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"binding path is not a regular non-link file: {raw!r}")
    return relative.as_posix(), path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--role", required=True, choices=sorted(ROLES))
    parser.add_argument("--output", required=True)
    parser.add_argument("--timing", required=True)
    parser.add_argument("--binding", action="append", default=[])
    args = parser.parse_args()

    timing_relative, timing_path = relative_regular(args.timing)
    try:
        timing = json.loads(timing_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise SystemExit(f"cannot read timing record: {error}") from error
    if not isinstance(timing, dict) or timing.get("schema") != "ndea.exp002.logged_command.v1":
        raise SystemExit("timing record schema mismatch")
    if timing.get("exit_code") != 0:
        raise SystemExit("refusing to write PASS metadata for a nonzero timing-record exit")
    argv = timing.get("argv")
    if not isinstance(argv, list) or not argv or any(type(item) is not str or not item for item in argv):
        raise SystemExit("--argv-json must be a nonempty array of nonempty strings")
    try:
        started = datetime.fromisoformat(str(timing.get("started_utc", "")).replace("Z", "+00:00"))
        finished = datetime.fromisoformat(str(timing.get("finished_utc", "")).replace("Z", "+00:00"))
    except ValueError as error:
        raise SystemExit(f"invalid timestamp: {error}") from error
    elapsed_seconds = timing.get("elapsed_seconds")
    if (
        started.tzinfo is None
        or finished.tzinfo is None
        or finished < started
        or type(elapsed_seconds) not in {int, float}
        or elapsed_seconds < 0
    ):
        raise SystemExit("timestamps/elapsed interval are inconsistent")

    lean = resolve_tool("NDEA_LEAN", "lean")
    lake = resolve_tool("NDEA_LAKE", "lake")
    elan = resolve_tool("NDEA_ELAN", "elan")
    lean_full = command_output([lean, "--version"])
    lake_full = command_output([lake, "--version"])
    elan_full = command_output([elan, "--version"])
    lean_match = re.search(r"version\s+(\d+\.\d+\.\d+)", lean_full)
    if not lean_match:
        raise SystemExit(f"could not parse Lean version: {lean_full!r}")
    manifest = json.loads((REPO / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = [row for row in manifest["packages"] if row.get("name") == "mathlib"]
    if len(mathlib) != 1:
        raise SystemExit("lake-manifest.json does not have exactly one Mathlib dependency")

    record = {
        "schema": "ndea.exp002.lean_assurance_role.v1",
        "role": args.role,
        "status": "PASS",
        "exit_code": timing["exit_code"],
        "argv": argv,
        "cwd": timing.get("cwd"),
        "started_utc": started.astimezone(timezone.utc).isoformat(),
        "finished_utc": finished.astimezone(timezone.utc).isoformat(),
        "elapsed_seconds": elapsed_seconds,
        "metadata_generated_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": lean_match.group(1),
        "lean_version_full": lean_full,
        "lake_version": lake_full,
        "elan_version": elan_full,
        "mathlib_revision": mathlib[0]["rev"],
        "lean_toolchain": (REPO / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "timing_record_path": timing_relative,
        "timing_sha256": sha256(timing_path),
    }
    bound_paths: dict[str, str] = {"timing_sha256": timing_relative}
    for item in args.binding:
        if "=" not in item:
            raise SystemExit(f"binding must have FIELD=PATH form: {item!r}")
        field, raw_path = item.split("=", 1)
        relative, path = relative_regular(raw_path)
        if relative in bound_paths.values():
            raise SystemExit(f"duplicate bound path: {relative!r}")
        bound_paths[field] = relative
        set_dotted(record, field, sha256(path))
    if not bound_paths:
        raise SystemExit("at least one --binding is required")
    record["bound_paths"] = bound_paths

    if (REPO / args.output).exists():
        raise SystemExit(f"refusing to overwrite existing metadata: {args.output}")
    output_relative, output_path = (args.output, REPO / args.output)
    if Path(output_relative).is_absolute() or ".." in Path(output_relative).parts:
        raise SystemExit("--output must be repository-relative")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "role": args.role,
        "status": "PASS",
        "output": Path(output_relative).as_posix(),
        "sha256": sha256(output_path),
        "binding_count": len(bound_paths),
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
