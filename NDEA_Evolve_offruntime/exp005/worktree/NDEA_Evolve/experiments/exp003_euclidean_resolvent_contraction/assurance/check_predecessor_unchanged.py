#!/usr/bin/env python3
"""Fail-closed audit that the immutable Experiment 002 predecessor is unchanged.

This script is intentionally read-only except for exclusively creating the JSON
path supplied with ``--output``. It does not invoke Lean, Lake, Julia, or any
network service. Every Git command and its result is preserved in that receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "ndea.exp003.predecessor_postcheck.v1"

PREDECESSOR_REPO = Path(
    "/home/richman954/NDEA_Evolve_offruntime/exp002/worktree/NDEA_Evolve"
)
PREDECESSOR_COMMIT = "207cf3650499d69102dbfc21d26e68a7b7ac8b09"
PREDECESSOR_TAG = "exp002-operator-cayley-unitarity-verified-final-20260906"
PREDECESSOR_TAG_OBJECT = "657e9a0e4808b4ef106fa480c0ef787fc1b07b40"

EXPECTED_FILE_SHA256 = {
    "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean":
        "be29c41df0bd17e977c9e12d7a81e348be3deb6cf7e64b67a117aa6cc3722a54",
    "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean":
        "ef71de8e6a7188aec8df817550fe848048358268cb1a2e63f4ba4be4b002dd17",
    "lean-toolchain":
        "efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee",
    "lakefile.toml":
        "bb18391d73c83a7a3d0a971769f48fe5d6011bb5eb01d6887f8dfa02898e5b24",
    "lake-manifest.json":
        "8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158",
}
EXPECTED_TOOLCHAIN_CONTENTS = "leanprover/lean4:v4.31.0"
EXPECTED_TOOLCHAIN_FILE_CONTENTS = EXPECTED_TOOLCHAIN_CONTENTS + "\n"
EXPECTED_MATHLIB_REVISION = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
EXPECTED_MATHLIB_INPUT_REVISION = "v4.31.0"
EXPECTED_MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"

PREDECESSOR_DELIVERY_DIR = Path(
    "/home/richman954/NDEA_Evolve_offruntime/exp002/final_delivery_20260906"
)
EXPECTED_EXTERNAL_FILES = {
    PREDECESSOR_DELIVERY_DIR / "NDEA_Evolve_exp002_final_evidence.tar.gz":
        "49cb77754f5276a8b09697b18a80930b6673467b0390ed014243e8e8189b971e",
    PREDECESSOR_DELIVERY_DIR / "NDEA_Evolve_exp002_final.bundle":
        "12dc3635e9bee8776cd6929bad1844e4293003b2117d4bc7c8dcee2023fe79d2",
}

# These are the exact Git objects at the immutable Exp002 commit. Directory
# entries are trees and file entries are blobs. Checking them in the source
# repository, at the retained tag, and at the current Exp003 HEAD prevents a
# copied or modified predecessor subtree from passing on content labels alone.
EXPECTED_GIT_OBJECTS = {
    "NDEAEvolve/Experiments/Exp002": {
        "oid": "ffc2b29a07b544d2c5323c5b68a7c68e72b56899",
        "type": "tree",
    },
    "experiments/exp002_operator_cayley_unitarity": {
        "oid": "6542576f8d086ef9d9ec23fb1857fe9061328464",
        "type": "tree",
    },
    "lean-toolchain": {
        "oid": "18640c8b066b182147f324d3aefd8ee48ee45238",
        "type": "blob",
    },
    "lakefile.toml": {
        "oid": "a62e22edd1ccbf3eda0514bc3c4c8901c29411b5",
        "type": "blob",
    },
    "lake-manifest.json": {
        "oid": "9d7e58f96268bd595a19b05dc0da88b35edaa2b6",
        "type": "blob",
    },
}

GIT_TIMEOUT_SECONDS = 30
HEX40 = re.compile(r"[0-9a-f]{40}\Z")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def strict_json_load(path: Path) -> Any:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key {key!r}")
            result[key] = value
        return result

    text = path.read_text(encoding="utf-8", errors="strict")
    return json.loads(
        text,
        object_pairs_hook=reject_duplicates,
        parse_constant=lambda token: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON constant {token!r}")
        ),
    )


class Audit:
    def __init__(self, git: Path) -> None:
        self.git = git
        self.commands: list[dict[str, Any]] = []
        self.checks: list[dict[str, Any]] = []
        self.files: list[dict[str, Any]] = []

    def check(
        self,
        name: str,
        passed: bool,
        *,
        expected: Any = None,
        observed: Any = None,
        detail: str | None = None,
    ) -> bool:
        row: dict[str, Any] = {
            "name": name,
            "status": "PASS" if passed else "FAIL",
            "expected": expected,
            "observed": observed,
        }
        if detail is not None:
            row["detail"] = detail
        self.checks.append(row)
        return passed

    def run_git(self, repo: Path, *arguments: str) -> dict[str, Any]:
        argv = [str(self.git), *arguments]
        started = utc_now()
        before = time.monotonic()
        timed_out = False
        error: str | None = None
        returncode: int | None = None
        stdout = b""
        stderr = b""
        try:
            completed = subprocess.run(
                argv,
                cwd=repo,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
                timeout=GIT_TIMEOUT_SECONDS,
            )
            returncode = completed.returncode
            stdout = completed.stdout
            stderr = completed.stderr
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            stdout = exc.stdout or b""
            stderr = exc.stderr or b""
            error = f"TimeoutExpired after {GIT_TIMEOUT_SECONDS} seconds"
        except (OSError, subprocess.SubprocessError) as exc:
            error = f"{type(exc).__name__}: {exc}"
        elapsed = time.monotonic() - before
        finished = utc_now()
        try:
            stdout_text = stdout.decode("utf-8", errors="strict")
            stderr_text = stderr.decode("utf-8", errors="strict")
            utf8 = True
        except UnicodeDecodeError:
            stdout_text = stdout.decode("utf-8", errors="backslashreplace")
            stderr_text = stderr.decode("utf-8", errors="backslashreplace")
            utf8 = False
        row = {
            "sequence": len(self.commands) + 1,
            "argv": argv,
            "cwd": str(repo),
            "started_utc": started,
            "finished_utc": finished,
            "elapsed_seconds": elapsed,
            "timeout_seconds": GIT_TIMEOUT_SECONDS,
            "timed_out": timed_out,
            "returncode": returncode,
            "spawn_error": error,
            "stdout_utf8": utf8,
            "stdout": stdout_text,
            "stderr": stderr_text,
            "stdout_sha256": sha256_bytes(stdout),
            "stderr_sha256": sha256_bytes(stderr),
        }
        self.commands.append(row)
        return row

    def git_value(
        self,
        repo: Path,
        check_name: str,
        arguments: tuple[str, ...],
        expected: str,
    ) -> str | None:
        command = self.run_git(repo, *arguments)
        observed = command["stdout"].strip() if command["returncode"] == 0 else None
        passed = (
            command["returncode"] == 0
            and not command["timed_out"]
            and command["spawn_error"] is None
            and command["stdout_utf8"]
            and command["stderr"] == ""
            and observed == expected
        )
        self.check(check_name, passed, expected=expected, observed=observed)
        return observed

    def verify_file(self, path: Path, expected_hash: str, label: str) -> bool:
        regular_nonlink = path.is_file() and not path.is_symlink()
        actual_hash = sha256_file(path) if regular_nonlink else None
        size = path.stat().st_size if regular_nonlink else None
        passed = regular_nonlink and actual_hash == expected_hash
        row = {
            "label": label,
            "path": str(path),
            "regular_nonlink": regular_nonlink,
            "bytes": size,
            "expected_sha256": expected_hash,
            "observed_sha256": actual_hash,
            "status": "PASS" if passed else "FAIL",
        }
        self.files.append(row)
        self.check(
            f"file:{label}",
            passed,
            expected=expected_hash,
            observed=actual_hash,
            detail=str(path),
        )
        return passed


def reserve_output(path: Path) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    return os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)


def write_reserved(descriptor: int, payload: dict[str, Any]) -> None:
    rendered = json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n"
    data = rendered.encode("utf-8")
    with os.fdopen(descriptor, "wb", closefd=True) as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit immutable Experiment 002 predecessor identities"
    )
    parser.add_argument(
        "--repo",
        required=True,
        help="explicit path to the current isolated Experiment 003 Git worktree",
    )
    parser.add_argument(
        "--output",
        required=True,
        help="new JSON receipt path; every pre-existing target is rejected",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    requested_repo = Path(arguments.repo).expanduser()
    requested_output = Path(arguments.output).expanduser()

    if requested_repo.is_symlink() or not requested_repo.is_dir():
        raise SystemExit(f"--repo must be a non-symlink directory: {requested_repo}")
    repo = requested_repo.resolve()
    predecessor_repo = PREDECESSOR_REPO.resolve()
    delivery_dir = PREDECESSOR_DELIVERY_DIR.resolve()
    output = requested_output.resolve(strict=False)
    if repo == predecessor_repo:
        raise SystemExit("--repo must be the isolated Exp003 repository, not Exp002")
    if output.is_relative_to(predecessor_repo) or output.is_relative_to(delivery_dir):
        raise SystemExit("refusing to write audit output inside immutable Exp002 locations")

    try:
        output_descriptor = reserve_output(output)
    except FileExistsError as exc:
        raise SystemExit(f"refusing to overwrite existing output: {output}") from exc

    started_utc = utc_now()
    started_monotonic = time.monotonic()
    git_raw = shutil.which("git")
    audit: Audit | None = None
    unexpected_error: dict[str, str] | None = None
    try:
        if git_raw is None:
            raise RuntimeError("git NOT FOUND")
        git = Path(git_raw).resolve()
        if not git.is_file() or not os.access(git, os.X_OK):
            raise RuntimeError(f"git is not an executable regular file: {git}")
        audit = Audit(git)

        # Resolve and identify both repositories without trusting the supplied
        # paths to be their Git top levels.
        audit.git_value(
            predecessor_repo,
            "source:is_inside_worktree",
            ("rev-parse", "--is-inside-work-tree"),
            "true",
        )
        audit.git_value(
            predecessor_repo,
            "source:top_level",
            ("rev-parse", "--show-toplevel"),
            str(predecessor_repo),
        )
        audit.git_value(
            repo,
            "current:is_inside_worktree",
            ("rev-parse", "--is-inside-work-tree"),
            "true",
        )
        audit.git_value(
            repo,
            "current:top_level",
            ("rev-parse", "--show-toplevel"),
            str(repo),
        )

        # The original Exp002 source worktree must remain globally clean and
        # exactly at its immutable release commit.
        audit.git_value(
            predecessor_repo,
            "source:head_commit",
            ("rev-parse", "--verify", "HEAD^{commit}"),
            PREDECESSOR_COMMIT,
        )
        source_status = audit.run_git(
            predecessor_repo,
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
        )
        source_clean = (
            source_status["returncode"] == 0
            and not source_status["timed_out"]
            and source_status["spawn_error"] is None
            and source_status["stdout_utf8"]
            and source_status["stdout"] == ""
            and source_status["stderr"] == ""
        )
        audit.check(
            "source:globally_clean",
            source_clean,
            expected="empty porcelain-v1 -z status",
            observed=source_status["stdout"],
        )

        for prefix, worktree in (("source", predecessor_repo), ("current", repo)):
            tag_ref = f"refs/tags/{PREDECESSOR_TAG}"
            audit.git_value(
                worktree,
                f"{prefix}:predecessor_tag_object",
                ("rev-parse", "--verify", tag_ref),
                PREDECESSOR_TAG_OBJECT,
            )
            audit.git_value(
                worktree,
                f"{prefix}:predecessor_tag_type",
                ("cat-file", "-t", tag_ref),
                "tag",
            )
            audit.git_value(
                worktree,
                f"{prefix}:predecessor_tag_peeled_commit",
                ("rev-parse", "--verify", f"{tag_ref}^{{commit}}"),
                PREDECESSOR_COMMIT,
            )

        # File bytes are checked in the pristine source worktree and again in
        # the current Exp003 worktree, independently of Git metadata.
        for relative, expected_hash in EXPECTED_FILE_SHA256.items():
            audit.verify_file(
                predecessor_repo / relative,
                expected_hash,
                f"source:{relative}",
            )
            audit.verify_file(
                repo / relative,
                expected_hash,
                f"current:{relative}",
            )

        source_toolchain = predecessor_repo / "lean-toolchain"
        current_toolchain = repo / "lean-toolchain"
        for prefix, path in (("source", source_toolchain), ("current", current_toolchain)):
            contents = (
                path.read_text(encoding="utf-8", errors="strict")
                if path.is_file() and not path.is_symlink()
                else None
            )
            audit.check(
                f"{prefix}:lean_toolchain_contents",
                contents == EXPECTED_TOOLCHAIN_FILE_CONTENTS,
                expected=EXPECTED_TOOLCHAIN_FILE_CONTENTS,
                observed=contents,
            )

        # Strictly parse each manifest and require one exact Mathlib package.
        for prefix, path in (
            ("source", predecessor_repo / "lake-manifest.json"),
            ("current", repo / "lake-manifest.json"),
        ):
            try:
                manifest = strict_json_load(path)
                packages = manifest.get("packages") if isinstance(manifest, dict) else None
                mathlib_rows = (
                    [
                        package
                        for package in packages
                        if isinstance(package, dict) and package.get("name") == "mathlib"
                    ]
                    if isinstance(packages, list)
                    else []
                )
                observed_mathlib = mathlib_rows[0] if len(mathlib_rows) == 1 else None
                manifest_ok = (
                    len(mathlib_rows) == 1
                    and observed_mathlib.get("type") == "git"
                    and observed_mathlib.get("rev") == EXPECTED_MATHLIB_REVISION
                    and observed_mathlib.get("inputRev") == EXPECTED_MATHLIB_INPUT_REVISION
                    and observed_mathlib.get("url") == EXPECTED_MATHLIB_URL
                )
                detail = None
            except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
                observed_mathlib = None
                manifest_ok = False
                detail = f"{type(exc).__name__}: {exc}"
            audit.check(
                f"{prefix}:mathlib_manifest_identity",
                manifest_ok,
                expected={
                    "count": 1,
                    "type": "git",
                    "rev": EXPECTED_MATHLIB_REVISION,
                    "inputRev": EXPECTED_MATHLIB_INPUT_REVISION,
                    "url": EXPECTED_MATHLIB_URL,
                },
                observed=observed_mathlib,
                detail=detail,
            )

        # Exact adjacent off-runtime release artifacts are immutable sentinels.
        for path, expected_hash in EXPECTED_EXTERNAL_FILES.items():
            audit.verify_file(path, expected_hash, f"external:{path.name}")

        # Compare every frozen path's object ID/type in three views: the
        # original source commit, the retained tag in Exp003, and Exp003 HEAD.
        current_head = audit.run_git(repo, "rev-parse", "--verify", "HEAD^{commit}")
        current_head_value = (
            current_head["stdout"].strip() if current_head["returncode"] == 0 else None
        )
        audit.check(
            "current:head_is_commit",
            current_head_value is not None and HEX40.fullmatch(current_head_value) is not None,
            expected="40 lowercase hexadecimal Git object ID",
            observed=current_head_value,
        )
        tag_commit_spec = f"refs/tags/{PREDECESSOR_TAG}^{{commit}}"
        for relative, expected in EXPECTED_GIT_OBJECTS.items():
            expected_oid = expected["oid"]
            expected_type = expected["type"]
            views = (
                ("source_commit", predecessor_repo, f"{PREDECESSOR_COMMIT}:{relative}"),
                ("current_tag", repo, f"{tag_commit_spec}:{relative}"),
                ("current_head", repo, f"HEAD:{relative}"),
            )
            for view, worktree, spec in views:
                audit.git_value(
                    worktree,
                    f"git_object:{view}:{relative}:oid",
                    ("rev-parse", "--verify", spec),
                    expected_oid,
                )
                audit.git_value(
                    worktree,
                    f"git_object:{view}:{relative}:type",
                    ("cat-file", "-t", spec),
                    expected_type,
                )

        immutable_paths = tuple(EXPECTED_GIT_OBJECTS)
        predecessor_status = audit.run_git(
            repo,
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--",
            *immutable_paths,
        )
        paths_clean = (
            predecessor_status["returncode"] == 0
            and not predecessor_status["timed_out"]
            and predecessor_status["spawn_error"] is None
            and predecessor_status["stdout_utf8"]
            and predecessor_status["stdout"] == ""
            and predecessor_status["stderr"] == ""
        )
        audit.check(
            "current:immutable_predecessor_paths_clean",
            paths_clean,
            expected="empty porcelain-v1 -z status for frozen paths",
            observed=predecessor_status["stdout"],
        )

        exp003_marker = repo / "experiments/exp003_euclidean_resolvent_contraction/FROZEN_SPECIFICATION.md"
        marker_ok = exp003_marker.is_file() and not exp003_marker.is_symlink()
        audit.check(
            "current:exp003_frozen_specification_present",
            marker_ok,
            expected=str(exp003_marker),
            observed=str(exp003_marker) if marker_ok else None,
        )
    except Exception as exc:  # Preserve an attributable fail-closed receipt.
        unexpected_error = {"type": type(exc).__name__, "message": str(exc)}

    finished_utc = utc_now()
    elapsed_seconds = time.monotonic() - started_monotonic
    checks = audit.checks if audit is not None else []
    commands = audit.commands if audit is not None else []
    files = audit.files if audit is not None else []
    passed = unexpected_error is None and len(checks) > 0 and all(
        check["status"] == "PASS" for check in checks
    )
    result = {
        "schema": SCHEMA,
        "status": "PASS" if passed else "FAIL",
        "started_utc": started_utc,
        "finished_utc": finished_utc,
        "elapsed_seconds": elapsed_seconds,
        "requested_repo": str(requested_repo),
        "resolved_repo": str(repo),
        "requested_output": str(requested_output),
        "resolved_output": str(output),
        "write_policy": "exclusive_create_no_overwrite",
        "expected": {
            "predecessor_repo": str(predecessor_repo),
            "commit": PREDECESSOR_COMMIT,
            "tag": PREDECESSOR_TAG,
            "annotated_tag_object": PREDECESSOR_TAG_OBJECT,
            "tag_peeled_commit": PREDECESSOR_COMMIT,
            "lean_toolchain_contents": EXPECTED_TOOLCHAIN_CONTENTS,
            "mathlib_revision": EXPECTED_MATHLIB_REVISION,
            "immutable_git_objects": EXPECTED_GIT_OBJECTS,
            "external_files": {
                str(path): expected_hash
                for path, expected_hash in EXPECTED_EXTERNAL_FILES.items()
            },
        },
        "check_counts": {
            "total": len(checks),
            "passed": sum(check["status"] == "PASS" for check in checks),
            "failed": sum(check["status"] != "PASS" for check in checks),
        },
        "checks": checks,
        "file_checks": files,
        "commands": commands,
        "unexpected_error": unexpected_error,
        "no_lean_lake_julia_or_network_commands": True,
    }
    if passed:
        # Delivery tooling consumes this compact preflight-compatible summary.
        # Detailed independent observations remain in `checks`, `file_checks`,
        # and `commands` above; these fields are emitted only after all of them
        # have passed.
        result.update(
            {
                "expected_and_observed_commit": PREDECESSOR_COMMIT,
                "tag": PREDECESSOR_TAG,
                "annotated_tag_object": PREDECESSOR_TAG_OBJECT,
                "tag_peeled_commit": PREDECESSOR_COMMIT,
                "operator_cayley_sha256": EXPECTED_FILE_SHA256[
                    "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean"
                ],
                "adversarial_witnesses_sha256": EXPECTED_FILE_SHA256[
                    "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean"
                ],
                "lean_toolchain_contents": EXPECTED_TOOLCHAIN_CONTENTS,
                "lean_toolchain_sha256": EXPECTED_FILE_SHA256["lean-toolchain"],
                "lakefile_sha256": EXPECTED_FILE_SHA256["lakefile.toml"],
                "lake_manifest_sha256": EXPECTED_FILE_SHA256["lake-manifest.json"],
                "mathlib_revision": EXPECTED_MATHLIB_REVISION,
                "final_archive_sha256": EXPECTED_EXTERNAL_FILES[
                    PREDECESSOR_DELIVERY_DIR / "NDEA_Evolve_exp002_final_evidence.tar.gz"
                ],
                "final_git_bundle_sha256": EXPECTED_EXTERNAL_FILES[
                    PREDECESSOR_DELIVERY_DIR / "NDEA_Evolve_exp002_final.bundle"
                ],
            }
        )
    try:
        write_reserved(output_descriptor, result)
    except Exception:
        try:
            os.close(output_descriptor)
        except OSError:
            pass
        raise
    print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
