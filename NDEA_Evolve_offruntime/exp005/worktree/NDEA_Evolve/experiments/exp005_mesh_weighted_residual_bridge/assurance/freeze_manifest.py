#!/usr/bin/env python3
"""Freeze checksums of all indexed deliverables after intended files are staged.

The manifest excludes itself. Untracked files are never added implicitly, and
existing output files are refused. This helper does not stage or commit files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess


FINAL_MANIFEST = "experiments/exp005_mesh_weighted_residual_bridge/evidence/FINAL_SHA256SUMS"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def git(repo: Path, *arguments: str) -> bytes:
    command = ["git", "-C", str(repo), *arguments]
    result = subprocess.run(command, capture_output=True, timeout=60)
    require(result.returncode == 0,
            f"Git check failed ({' '.join(arguments)}): "
            f"{result.stderr.decode(errors='replace').strip() or 'unstaged changes or invalid index'}")
    return result.stdout


def safe_relative(raw: bytes) -> str:
    relative = raw.decode("utf-8", errors="strict")
    path = PurePosixPath(relative)
    require(bool(relative) and not path.is_absolute() and ".." not in path.parts
            and path.as_posix() == relative and "\\" not in relative
            and all(ord(character) >= 32 and ord(character) != 127 for character in relative),
            f"Unsafe, noncanonical, or newline-containing indexed path: {relative!r}")
    return relative


def hash_stable_regular(path: Path) -> str:
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and path.resolve(strict=True) == path,
            f"Indexed deliverable is a symlink or not a regular file: {path}")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    after = path.lstat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            f"Deliverable changed while hashing: {path}")
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--output", type=Path,
                        help="New manifest path inside the repository; defaults to evidence/FINAL_SHA256SUMS.")
    args = parser.parse_args()
    repo = args.repo.resolve(strict=True)
    requested = args.output or Path(FINAL_MANIFEST)
    output = requested if requested.is_absolute() else repo / requested
    require(not output.exists() and not output.is_symlink(), f"Refusing to overwrite manifest: {output}")
    require(output.parent.resolve(strict=True).is_relative_to(repo),
            "Manifest output must have an existing parent inside the repository.")
    output = output.parent.resolve(strict=True) / output.name
    output_relative = output.relative_to(repo).as_posix()
    safe_relative(output_relative.encode("utf-8"))

    # Capture the index itself as well as its names to detect concurrent staging.
    index_before = git(repo, "ls-files", "--stage", "-z")
    require(not git(repo, "ls-files", "--unmerged", "-z"), "Unmerged index entries cannot be frozen.")
    git(repo, "diff", "--quiet", "--no-ext-diff", "--")
    raw_names = git(repo, "ls-files", "-z").split(b"\0")
    names = [safe_relative(raw) for raw in raw_names if raw]
    require(len(names) == len(set(names)), "Duplicate indexed paths cannot be frozen.")
    names = sorted(name for name in names if name != output_relative)
    require(bool(names), "No indexed deliverable files were found.")
    require(Path(__file__).resolve().relative_to(repo).as_posix() in names,
            "Stage this manifest helper together with all intended deliverables before freezing.")

    rows = [f"{hash_stable_regular(repo / name)}  {name}\n" for name in names]
    require(index_before == git(repo, "ls-files", "--stage", "-z"),
            "The staged index changed while the manifest was being prepared.")
    git(repo, "diff", "--quiet", "--no-ext-diff", "--")
    payload = "".join(rows).encode("utf-8")
    with output.open("xb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    print(json.dumps({"manifest": str(output), "entry_count": len(rows),
                      "manifest_sha256": hashlib.sha256(payload).hexdigest(),
                      "excluded_self": output_relative,
                      "selection": "All git ls-files -z entries; untracked files excluded."}, indent=2))


if __name__ == "__main__":
    main()
