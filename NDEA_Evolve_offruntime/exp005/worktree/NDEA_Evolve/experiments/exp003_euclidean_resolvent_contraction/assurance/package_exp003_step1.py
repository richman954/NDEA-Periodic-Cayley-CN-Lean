#!/usr/bin/env python3
"""Fail-closed manifest and delivery packager for Experiment 003, Step 1.

This program intentionally does not run Lean, create a Git commit, or create a
Git tag.  ``manifest-write`` is the final in-tree mutation; ``package`` accepts
only an already clean, committed tree whose branch and annotated tag resolve to
the explicitly supplied commit.  The independently runnable delivery verifier
performs the fresh-extraction audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tarfile
import time
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


EXP_ROOT = "experiments/exp003_euclidean_resolvent_contraction"
FINAL_MANIFEST = f"{EXP_ROOT}/FINAL_SHA256SUMS"
ARCHIVE_ROOT = "NDEA_Evolve"
SELECTED_ROOTS = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "NDEAEvolve.lean",
    "NDEAEvolve/Basic.lean",
    "NDEAEvolve/Experiments/Exp002",
    "NDEAEvolve/Experiments/Exp003",
    EXP_ROOT,
)

PACKAGER_SCHEMA = "ndea.exp003.step1.packager.v1"
RECEIPT_SCHEMA = "ndea.exp003.step1.final_delivery.v1"
SPEC_SCHEMA = "ndea.exp003.step1.delivery_spec.v1"
CONTROL_SCHEMA = "ndea.exp003.lean_negative_controls.v1"
EXPECTED_CONTROL_CASES = (
    "01_strict_bound_false",
    "02_dropped_hermiticity_false",
)
EXPECTED_CONTROL_REASON = "EXPECTED_FALSE_STATEMENT_TYPE_MISMATCH"
NEGATIVE_PROCESS_ID = "exp003-lean-batched-negative-controls-001"
DEFAULT_CONTROL_RESULTS = (
    f"{EXP_ROOT}/controls/lean/rejection_diagnostics/results.json"
)
REQUIRED_EVIDENCE_LABELS = {
    "final_build_log",
    "final_build_timing",
    "signature_axiom_audit",
    "forbidden_scan",
    "negative_control_execution_receipt",
    "predecessor_postcheck",
}
PRODUCTION_SOURCES = (
    "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean",
)
FINAL_BUILD_TARGET = "NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction"
PINNED_LAKE = "/home/richman954/.elan/bin/lake"
NEGATIVE_BATCH_SOURCE = f"{EXP_ROOT}/controls/lean/BatchedNegativeControls.lean"
HEADLINE_DECLARATIONS = (
    "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_eq_average",
    "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_apply_norm_le",
    "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_opNorm_le_one",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide", "sorryAx")
FINAL_BUILD_TIMING_SCHEMA = "ndea.exp003.logged_command.v1"
SIGNATURE_AUDIT_SCHEMA = "ndea.exp003.signature_axiom_audit.v1"
FORBIDDEN_SCAN_SCHEMA = "ndea.exp003.forbidden_token_scan.v1"
NEGATIVE_RECEIPT_SCHEMA = "ndea.exp003.lean_negative_controls.execution_receipt.v1"
NEGATIVE_ACCEPTANCE_KEYS = {
    "natural_lean_exit_code",
    "one_lean_invocation",
    "two_attributable_type_mismatches",
    "global_diagnostic_checks",
    "exclusive_create_no_overwrite",
}
PREDECESSOR_POSTCHECK_SCHEMA = "ndea.exp003.predecessor_postcheck.v1"

PREDECESSOR_TAG = "exp002-operator-cayley-unitarity-verified-final-20260906"
PREDECESSOR_TAG_OBJECT = "657e9a0e4808b4ef106fa480c0ef787fc1b07b40"
PREDECESSOR_COMMIT = "207cf3650499d69102dbfc21d26e68a7b7ac8b09"
PREDECESSOR_OPERATOR_SHA256 = "be29c41df0bd17e977c9e12d7a81e348be3deb6cf7e64b67a117aa6cc3722a54"
PREDECESSOR_WITNESS_SHA256 = "ef71de8e6a7188aec8df817550fe848048358268cb1a2e63f4ba4be4b002dd17"
PINNED_LEAN_TOOLCHAIN = "leanprover/lean4:v4.31.0"
PINNED_LEAN_TOOLCHAIN_SHA256 = "efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee"
PINNED_LAKEFILE_SHA256 = "bb18391d73c83a7a3d0a971769f48fe5d6011bb5eb01d6887f8dfa02898e5b24"
PINNED_LAKE_MANIFEST_SHA256 = "8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158"
PINNED_MATHLIB_REVISION = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
PREDECESSOR_ARCHIVE_SHA256 = "49cb77754f5276a8b09697b18a80930b6673467b0390ed014243e8e8189b971e"
PREDECESSOR_BUNDLE_SHA256 = "12dc3635e9bee8776cd6929bad1844e4293003b2117d4bc7c8dcee2023fe79d2"
PREDECESSOR_IMMUTABLE_PATHS = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "NDEAEvolve.lean",
    "NDEAEvolve/Basic.lean",
    "NDEAEvolve/Experiments/Exp002",
    "experiments/exp002_operator_cayley_unitarity",
)

HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
SAFE_REF = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/+\-]*\Z")
SAFE_BASENAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._+\-]*\Z")
MANIFEST_LINE = re.compile(r"([0-9a-f]{64})  (.+)\Z")

MAX_ARCHIVE_BYTES = 2 * 1024**3
MAX_MEMBERS = 20_000
MAX_FILE_BYTES = 512 * 1024**2
MAX_TOTAL_BYTES = 2 * 1024**3
MAX_PATH_BYTES = 4096


class PackagingError(RuntimeError):
    """A condition that makes a trustworthy package impossible."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def reject_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number is forbidden: {value}")


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def read_json_strict(path: Path) -> Any:
    try:
        return json.loads(
            path.read_text(encoding="utf-8", errors="strict"),
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=reject_json_constant,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        raise PackagingError(f"cannot parse strict JSON {path}: {error}") from error


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def canonical_relative(raw: str, label: str = "path") -> str:
    if (
        not isinstance(raw, str)
        or not raw
        or "\x00" in raw
        or "\\" in raw
        or any(ord(character) < 32 or ord(character) == 127 for character in raw)
    ):
        raise PackagingError(f"{label} is not a canonical POSIX relative path: {raw!r}")
    try:
        encoded = raw.encode("utf-8", errors="strict")
    except UnicodeError as error:
        raise PackagingError(f"{label} is not UTF-8 encodable: {raw!r}") from error
    if len(encoded) > MAX_PATH_BYTES:
        raise PackagingError(f"{label} exceeds the path-byte limit: {raw!r}")
    pure = PurePosixPath(raw)
    parts = pure.parts
    if pure.is_absolute() or not parts or any(part in {"", ".", ".."} for part in parts):
        raise PackagingError(f"{label} is not canonical and relative: {raw!r}")
    if re.match(r"^[A-Za-z]:", parts[0]):
        raise PackagingError(f"{label} has a Windows drive prefix: {raw!r}")
    if pure.as_posix() != raw:
        raise PackagingError(f"{label} is not in canonical POSIX form: {raw!r}")
    return raw


def canonical_directory(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise PackagingError(f"{label} must be absolute: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        metadata = os.lstat(path)
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise PackagingError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical or not stat.S_ISDIR(metadata.st_mode):
        raise PackagingError(f"{label} must be a canonical non-link directory: {path}")
    return resolved


def new_directory(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise PackagingError(f"{label} must be an absolute path that does not exist: {path}")
    canonical_directory(path.parent, f"{label} parent")
    return Path(os.path.abspath(path))


def regular_file(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise PackagingError(f"{label} must be absolute: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        metadata = os.lstat(path)
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise PackagingError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical or not stat.S_ISREG(metadata.st_mode):
        raise PackagingError(f"{label} must be a canonical regular non-link file: {path}")
    return resolved


def hash_regular(path: Path) -> tuple[str, int]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise PackagingError(f"cannot open {path} without following links: {error}") from error
    digest = hashlib.sha256()
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise PackagingError(f"not a regular file: {path}")
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            digest.update(block)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    try:
        current = os.lstat(path)
    except OSError as error:
        raise PackagingError(f"file disappeared while hashing: {path}") from error
    identity_before = (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if identity_before != identity_after or (current.st_dev, current.st_ino) != (
        before.st_dev,
        before.st_ino,
    ):
        raise PackagingError(f"file changed while hashing: {path}")
    return digest.hexdigest(), before.st_size


def write_exclusive(path: Path, payload: bytes, mode: int = 0o600) -> None:
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    except OSError as error:
        raise PackagingError(f"refusing to overwrite {path}: {error}") from error
    try:
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise PackagingError(f"short write while creating {path}")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def clean_git_environment() -> dict[str, str]:
    environment = os.environ.copy()
    for key in list(environment):
        if key.startswith("GIT_CONFIG_") or key in {
            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_COMMON_DIR",
            "GIT_DIR",
            "GIT_INDEX_FILE",
            "GIT_NAMESPACE",
            "GIT_OBJECT_DIRECTORY",
            "GIT_REPLACE_REF_BASE",
            "GIT_WORK_TREE",
        }:
            environment.pop(key, None)
    environment.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_TERMINAL_PROMPT": "0",
            "LC_ALL": "C.UTF-8",
        }
    )
    return environment


class CommandLog:
    def __init__(self) -> None:
        self.rows: list[dict[str, Any]] = []

    def run(
        self,
        argv: list[str],
        cwd: Path,
        *,
        label: str,
        input_bytes: bytes | None = None,
        timeout: int = 120,
        require_zero: bool = True,
    ) -> bytes:
        started = utc_now()
        before = time.monotonic()
        try:
            completed = subprocess.run(
                argv,
                cwd=cwd,
                env=clean_git_environment(),
                input=input_bytes,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise PackagingError(f"command {label} could not complete: {error}") from error
        row = {
            "label": label,
            "argv": argv,
            "cwd": str(cwd),
            "started_utc": started,
            "elapsed_seconds": time.monotonic() - before,
            "exit_code": completed.returncode,
            "stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
            "stdout_bytes": len(completed.stdout),
            "stderr_sha256": hashlib.sha256(completed.stderr).hexdigest(),
            "stderr_bytes": len(completed.stderr),
        }
        self.rows.append(row)
        if require_zero and completed.returncode != 0:
            stderr = completed.stderr.decode("utf-8", errors="replace")[-4000:]
            raise PackagingError(f"command {label} failed ({completed.returncode}): {stderr}")
        return completed.stdout

    def text(self, argv: list[str], cwd: Path, *, label: str) -> str:
        raw = self.run(argv, cwd, label=label)
        try:
            return raw.decode("utf-8", errors="strict").strip()
        except UnicodeError as error:
            raise PackagingError(f"command {label} returned non-UTF-8 output") from error


def walk_selected(repo: Path, root: Path) -> Iterable[tuple[str, Path]]:
    try:
        entries = sorted(os.scandir(root), key=lambda entry: entry.name.encode("utf-8"))
    except (OSError, UnicodeError) as error:
        raise PackagingError(f"cannot scan selected directory {root}: {error}") from error
    for entry in entries:
        path = Path(entry.path)
        metadata = entry.stat(follow_symlinks=False)
        relative = path.relative_to(repo).as_posix()
        canonical_relative(relative, "selected file")
        if stat.S_ISLNK(metadata.st_mode):
            raise PackagingError(f"symlink below selected roots: {relative}")
        if stat.S_ISDIR(metadata.st_mode):
            yield from walk_selected(repo, path)
        elif stat.S_ISREG(metadata.st_mode):
            yield relative, path
        else:
            raise PackagingError(f"special file below selected roots: {relative}")


def selected_files(repo: Path, *, exclude_manifest: bool) -> dict[str, Path]:
    result: dict[str, Path] = {}
    folded: set[str] = set()
    for raw in SELECTED_ROOTS:
        canonical_relative(raw, "selected root")
        target = repo.joinpath(*PurePosixPath(raw).parts)
        try:
            metadata = os.lstat(target)
        except OSError as error:
            raise PackagingError(f"required selected root is unavailable: {raw}: {error}") from error
        if stat.S_ISLNK(metadata.st_mode):
            raise PackagingError(f"selected root is a symlink: {raw}")
        if stat.S_ISREG(metadata.st_mode):
            rows = [(raw, target)]
        elif stat.S_ISDIR(metadata.st_mode):
            rows = list(walk_selected(repo, target))
            if not rows:
                raise PackagingError(f"selected directory is empty: {raw}")
        else:
            raise PackagingError(f"selected root is not a file or directory: {raw}")
        for relative, path in rows:
            if exclude_manifest and relative == FINAL_MANIFEST:
                continue
            folded_name = relative.casefold()
            if relative in result or folded_name in folded:
                raise PackagingError(f"duplicate/case-fold collision: {relative}")
            result[relative] = path
            folded.add(folded_name)
    return dict(sorted(result.items(), key=lambda item: item[0].encode("utf-8")))


def reject_ignored(repo: Path, files: dict[str, Path], commands: CommandLog) -> None:
    payload = b"\0".join(path.encode("utf-8") for path in files) + b"\0"
    stdout = commands.run(
        ["git", "check-ignore", "--no-index", "-z", "--stdin"],
        repo,
        label="git_check_ignore_selected",
        input_bytes=payload,
        require_zero=False,
    )
    return_code = commands.rows[-1]["exit_code"]
    if return_code not in {0, 1}:
        raise PackagingError(f"git check-ignore returned {return_code}")
    ignored = [item.decode("utf-8", errors="strict") for item in stdout.split(b"\0") if item]
    if (return_code == 0) != bool(ignored):
        raise PackagingError("git check-ignore status/output mismatch")
    if any(path not in files for path in ignored):
        raise PackagingError(f"git check-ignore returned unexpected paths: {ignored!r}")
    if ignored:
        raise PackagingError(f"ignored selected files are forbidden: {sorted(ignored)!r}")


def render_manifest(files: dict[str, Path]) -> bytes:
    rows = []
    for relative, path in files.items():
        digest, _ = hash_regular(path)
        rows.append(f"{digest}  {relative}")
    return ("\n".join(rows) + "\n").encode("utf-8")


def manifest_status(repo: Path, commands: CommandLog) -> dict[str, Any]:
    all_files = selected_files(repo, exclude_manifest=False)
    reject_ignored(repo, all_files, commands)
    manifest = regular_file(repo / FINAL_MANIFEST, "FINAL_SHA256SUMS")
    files = {key: value for key, value in all_files.items() if key != FINAL_MANIFEST}
    expected = render_manifest(files)
    if manifest.read_bytes() != expected:
        raise PackagingError("FINAL_SHA256SUMS is not the exact selected-file digest list")
    if render_manifest(selected_files(repo, exclude_manifest=True)) != expected:
        raise PackagingError("selected files changed during manifest validation")
    digest, size = hash_regular(manifest)
    return {
        "path": FINAL_MANIFEST,
        "sha256": digest,
        "size_bytes": size,
        "entries": len(files),
        "selected_roots": list(SELECTED_ROOTS),
    }


def write_manifest(repo: Path) -> dict[str, Any]:
    commands = CommandLog()
    files = selected_files(repo, exclude_manifest=True)
    reject_ignored(repo, files, commands)
    payload = render_manifest(files)
    manifest = repo / FINAL_MANIFEST
    if manifest.exists() or manifest.is_symlink():
        regular_file(manifest, "existing FINAL_SHA256SUMS")
        if manifest.read_bytes() != payload:
            raise PackagingError("refusing to overwrite a differing FINAL_SHA256SUMS")
        disposition = "ALREADY_IDENTICAL"
    else:
        canonical_directory(manifest.parent, "FINAL_SHA256SUMS parent")
        write_exclusive(manifest, payload)
        disposition = "CREATED_EXCLUSIVELY"
    status = manifest_status(repo, commands)
    return {"schema": PACKAGER_SCHEMA, "status": "PASS", "disposition": disposition, **status}


def is_under_selected(path: str) -> bool:
    return any(path == root or path.startswith(root + "/") for root in SELECTED_ROOTS)


def parse_manifest(path: Path) -> dict[str, str]:
    rows: dict[str, str] = {}
    folded: set[str] = set()
    for number, line in enumerate(path.read_text(encoding="utf-8", errors="strict").splitlines(), 1):
        match = MANIFEST_LINE.fullmatch(line)
        if match is None:
            raise PackagingError(f"malformed manifest line {number}")
        digest, relative = match.groups()
        canonical_relative(relative, f"manifest line {number}")
        if not is_under_selected(relative) or relative == FINAL_MANIFEST:
            raise PackagingError(f"manifest line outside the selected payload: {relative}")
        if relative in rows or relative.casefold() in folded:
            raise PackagingError(f"duplicate/case-fold manifest path: {relative}")
        rows[relative] = digest
        folded.add(relative.casefold())
    if not rows:
        raise PackagingError("manifest is empty")
    return rows


def control_summary(repo: Path, relative: str) -> dict[str, Any]:
    canonical_relative(relative, "negative-control result path")
    if not is_under_selected(relative):
        raise PackagingError("negative-control results are outside selected roots")
    path = regular_file(repo / relative, "negative-control results")
    value = read_json_strict(path)
    if not isinstance(value, dict) or value.get("schema") != CONTROL_SCHEMA:
        raise PackagingError(f"negative-control schema must be {CONTROL_SCHEMA!r}")
    if (
        value.get("status") != "PASS"
        or value.get("failed_unique_cases") != 0
        or value.get("passed_unique_cases") != 2
    ):
        raise PackagingError("negative-control aggregate status/count is not 2/2 PASS")
    if value.get("unique_cases") != 2 or value.get("total_process_invocations") != 1:
        raise PackagingError("negative controls must distinguish two cases from one Lean invocation")
    shared = value.get("shared_process")
    if not isinstance(shared, dict):
        raise PackagingError("negative controls lack shared_process metadata")
    expected_control_argv = [
        PINNED_LAKE,
        "env",
        "lean",
        str(repo / NEGATIVE_BATCH_SOURCE),
    ]
    if (
        shared.get("argv") != expected_control_argv
        or shared.get("cwd") != str(repo)
        or shared.get("process_invocation_id") != NEGATIVE_PROCESS_ID
        or shared.get("exit_code") != 1
        or shared.get("timed_out") is not False
        or shared.get("spawn_error") is not None
        or shared.get("output_limit_exceeded") is not False
        or shared.get("total_process_invocations") != 1
    ):
        raise PackagingError("Lean negative-control child did not naturally reject with exit 1")
    global_checks = value.get("global_diagnostic_checks")
    required_global_checks = {
        "diagnostic_utf8",
        "exactly_two_diagnostic_headers",
        "all_headers_are_errors",
        "no_unframed_output",
        "exact_source_path_and_line_sequence",
        "no_import_or_infrastructure_error",
        "no_syntax_error",
        "no_tactic_or_elaboration_error",
        "bound_inputs_unchanged_during_run",
        "control_inputs_unchanged_during_run",
    }
    if (
        not isinstance(global_checks, dict)
        or set(global_checks) != required_global_checks
        or any(item is not True for item in global_checks.values())
    ):
        raise PackagingError("a global negative-control diagnostic check failed")
    results = value.get("results")
    if not isinstance(results, list) or len(results) != 2:
        raise PackagingError("negative-control result list must contain exactly two rows")
    observed: list[str] = []
    process_ids: set[str] = set()
    for row in results:
        if not isinstance(row, dict):
            raise PackagingError("negative-control case row is not an object")
        case = row.get("case")
        observed.append(case if isinstance(case, str) else "")
        if (
            row.get("status") != "PASS"
            or row.get("attributable_rejection") is not True
            or row.get("reason_code") != EXPECTED_CONTROL_REASON
        ):
            raise PackagingError(f"negative-control case is not an attributable rejection: {case!r}")
        checks = row.get("diagnostic_checks")
        if not isinstance(checks, dict) or not checks or any(item is not True for item in checks.values()):
            raise PackagingError(f"negative-control diagnostic check failed: {case!r}")
        required = {
            "fixture_hash_and_reconstruction_valid",
            "exactly_one_case_diagnostic",
            "intended_combined_source_path",
            "intended_combined_exact_line",
            "diagnostic_column_is_positive",
            "type_mismatch_header",
            "own_witness_present_only",
            "has_actual_and_expected_types",
            "no_import_or_infrastructure_error",
            "no_syntax_error",
            "no_tactic_or_elaboration_error",
        }
        if set(checks) != required:
            raise PackagingError(f"negative-control case lacks required checks: {case!r}")
        process_id = row.get("process_invocation_id")
        if process_id != NEGATIVE_PROCESS_ID:
            raise PackagingError(f"negative-control case lacks process identity: {case!r}")
        process_ids.add(process_id)
    if tuple(observed) != EXPECTED_CONTROL_CASES or len(process_ids) != 1:
        raise PackagingError(
            f"negative-control identity/order mismatch: observed={observed!r} expected={EXPECTED_CONTROL_CASES!r}"
        )
    digest, size = hash_regular(path)
    return {
        "path": relative,
        "sha256": digest,
        "size_bytes": size,
        "schema": CONTROL_SCHEMA,
        "status": "PASS",
        "case_ids": list(EXPECTED_CONTROL_CASES),
        "unique_case_count": 2,
        "lean_process_invocation_count": 1,
        "lean_child_exit_code": 1,
        "classification": EXPECTED_CONTROL_REASON,
    }


def bound_path(repo: Path, bindings: dict[str, dict[str, Any]], label: str) -> Path:
    row = bindings[label]
    return regular_file(repo / str(row["path"]), f"evidence binding {label}")


def validate_final_build(
    repo: Path, bindings: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    log = bound_path(repo, bindings, "final_build_log")
    timing_path = bound_path(repo, bindings, "final_build_timing")
    timing = read_json_strict(timing_path)
    if not isinstance(timing, dict) or timing.get("schema") != FINAL_BUILD_TIMING_SCHEMA:
        raise PackagingError("final-build timing schema mismatch")
    if timing.get("exit_code") != 0:
        raise PackagingError("final-build timing does not record exit 0")
    expected_log_hash, expected_log_size = hash_regular(log)
    if (
        timing.get("cwd") != str(repo)
        or timing.get("log") != str(log)
        or timing.get("log_sha256") != expected_log_hash
        or timing.get("log_size_bytes") != expected_log_size
    ):
        raise PackagingError("final-build timing does not bind the exact log and repository")
    argv = timing.get("argv")
    if not isinstance(argv, list) or len(argv) != 8 or any(type(item) is not str for item in argv):
        raise PackagingError("final-build argv must be the exact eight-element bounded targeted Lake command")
    timeout_match = re.fullmatch(r"([1-9][0-9]{0,3})s", argv[3])
    if (
        argv[0] != "/usr/bin/timeout"
        or argv[1] != "--signal=TERM"
        or argv[2] != "--kill-after=10s"
        or timeout_match is None
        or int(timeout_match.group(1)) > 3600
        or argv[4:] != [
            PINNED_LAKE,
            "-v",
            "build",
            FINAL_BUILD_TARGET,
        ]
    ):
        raise PackagingError(f"final-build argv contract mismatch: {argv!r}")
    try:
        log_text = log.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise PackagingError(f"final-build log is not strict UTF-8: {error}") from error
    if "Build completed successfully" not in log_text or "error:" in log_text.lower():
        raise PackagingError("final-build log lacks the success marker or contains an error marker")
    return {
        "argv": argv,
        "cwd": str(repo),
        "exit_code": 0,
        "log_sha256": expected_log_hash,
        "log_size_bytes": expected_log_size,
    }


def validate_signature_audit(
    repo: Path, bindings: dict[str, dict[str, Any]], final_build: dict[str, Any]
) -> None:
    path = bound_path(repo, bindings, "signature_axiom_audit")
    audit = read_json_strict(path)
    if not isinstance(audit, dict) or audit.get("schema") != SIGNATURE_AUDIT_SCHEMA:
        raise PackagingError("signature/axiom audit schema mismatch")
    if (
        audit.get("status") != "PASS"
        or audit.get("headline_declaration_count") != 3
        or audit.get("audit_marker_pair_count") != 1
        or audit.get("unexpected_dependencies") != []
        or set(audit.get("allowed_dependencies", [])) != ALLOWED_AXIOMS
        or audit.get("source_log_sha256") != final_build["log_sha256"]
        or audit.get("source_log") != str(bound_path(repo, bindings, "final_build_log"))
    ):
        raise PackagingError("signature/axiom audit aggregate contract mismatch")
    rows = audit.get("declarations")
    if not isinstance(rows, list) or len(rows) != 3:
        raise PackagingError("signature/axiom audit must contain exactly three declarations")
    observed: list[str] = []
    for row in rows:
        if not isinstance(row, dict):
            raise PackagingError("signature/axiom declaration row is not an object")
        name = row.get("name")
        signature = row.get("signature")
        dependencies = row.get("dependencies")
        observed.append(name if isinstance(name, str) else "")
        if (
            not isinstance(signature, str)
            or not signature.startswith("@" + str(name) + " :")
            or not isinstance(dependencies, list)
            or any(not isinstance(item, str) for item in dependencies)
            or len(dependencies) != len(set(dependencies))
            or not set(dependencies).issubset(ALLOWED_AXIOMS)
        ):
            raise PackagingError(f"invalid signature/dependency row: {name!r}")
    if tuple(observed) != HEADLINE_DECLARATIONS:
        raise PackagingError("signature/axiom headline identity or order mismatch")


def validate_forbidden_scan(repo: Path, bindings: dict[str, dict[str, Any]]) -> None:
    path = bound_path(repo, bindings, "forbidden_scan")
    result = read_json_strict(path)
    if not isinstance(result, dict) or result.get("schema") != FORBIDDEN_SCAN_SCHEMA:
        raise PackagingError("forbidden-scan schema mismatch")
    if (
        result.get("status") != "PASS"
        or result.get("production_file_count") != 1
        or result.get("total_matches") != 0
    ):
        raise PackagingError("forbidden scan is not a one-file zero-match PASS")
    policy = result.get("policy")
    expected_policy = {
        "case_sensitive": True,
        "whole_token": True,
        "comments_and_strings_included": True,
        "tokens": list(FORBIDDEN_TOKENS),
    }
    if policy != expected_policy:
        raise PackagingError("forbidden-scan policy mismatch")
    pattern = re.compile(r"\b(?:" + "|".join(map(re.escape, FORBIDDEN_TOKENS)) + r")\b")
    rows = result.get("files")
    if not isinstance(rows, list) or len(rows) != 1:
        raise PackagingError("forbidden scan must contain exactly one source row")
    observed: list[str] = []
    for row in rows:
        if not isinstance(row, dict):
            raise PackagingError("forbidden-scan source row is not an object")
        relative = row.get("path")
        observed.append(relative if isinstance(relative, str) else "")
        if not isinstance(relative, str):
            raise PackagingError("forbidden-scan path is missing")
        source = regular_file(repo / relative, "forbidden-scan production source")
        text = source.read_text(encoding="utf-8", errors="strict")
        matches = [match.group(0) for line in text.splitlines() for match in pattern.finditer(line)]
        digest, size = hash_regular(source)
        if matches or row.get("matches") != [] or row.get("sha256") != digest or row.get("size_bytes") != size:
            raise PackagingError(f"forbidden-scan result does not match recomputation: {relative}")
    if tuple(observed) != PRODUCTION_SOURCES:
        raise PackagingError("forbidden-scan production-source identity/order mismatch")


def validate_predecessor_postcheck(repo: Path, bindings: dict[str, dict[str, Any]]) -> None:
    path = bound_path(repo, bindings, "predecessor_postcheck")
    value = read_json_strict(path)
    if not isinstance(value, dict) or value.get("schema") != PREDECESSOR_POSTCHECK_SCHEMA:
        raise PackagingError("predecessor postcheck schema mismatch")
    expected = {
        "status": "PASS",
        "expected_and_observed_commit": PREDECESSOR_COMMIT,
        "tag": PREDECESSOR_TAG,
        "annotated_tag_object": PREDECESSOR_TAG_OBJECT,
        "tag_peeled_commit": PREDECESSOR_COMMIT,
        "operator_cayley_sha256": PREDECESSOR_OPERATOR_SHA256,
        "adversarial_witnesses_sha256": PREDECESSOR_WITNESS_SHA256,
        "lean_toolchain_contents": PINNED_LEAN_TOOLCHAIN,
        "lean_toolchain_sha256": PINNED_LEAN_TOOLCHAIN_SHA256,
        "lakefile_sha256": PINNED_LAKEFILE_SHA256,
        "lake_manifest_sha256": PINNED_LAKE_MANIFEST_SHA256,
        "mathlib_revision": PINNED_MATHLIB_REVISION,
        "final_archive_sha256": PREDECESSOR_ARCHIVE_SHA256,
        "final_git_bundle_sha256": PREDECESSOR_BUNDLE_SHA256,
    }
    mismatches = {key: value.get(key) for key, expected_value in expected.items() if value.get(key) != expected_value}
    if mismatches:
        raise PackagingError(f"predecessor postcheck immutable identity mismatch: {mismatches!r}")
    current_expected = {
        "operator_cayley_sha256": hash_regular(repo / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean")[0],
        "adversarial_witnesses_sha256": hash_regular(repo / "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean")[0],
        "lean_toolchain_sha256": hash_regular(repo / "lean-toolchain")[0],
        "lakefile_sha256": hash_regular(repo / "lakefile.toml")[0],
        "lake_manifest_sha256": hash_regular(repo / "lake-manifest.json")[0],
    }
    for field, digest in current_expected.items():
        if value.get(field) != digest:
            raise PackagingError(f"predecessor postcheck does not match current immutable bytes: {field}")


def validate_negative_receipt(
    repo: Path,
    bindings: dict[str, dict[str, Any]],
    control_relative: str,
) -> None:
    results_path = regular_file(repo / control_relative, "negative-control results")
    results = read_json_strict(results_path)
    if not isinstance(results, dict):
        raise PackagingError("negative-control results are not a JSON object")
    receipt_path = bound_path(repo, bindings, "negative_control_execution_receipt")
    receipt = read_json_strict(receipt_path)
    if not isinstance(receipt, dict) or receipt.get("schema") != NEGATIVE_RECEIPT_SCHEMA:
        raise PackagingError("negative-control execution receipt schema mismatch")
    if (
        receipt.get("status") != "PASS"
        or receipt.get("process_invocation_id") != NEGATIVE_PROCESS_ID
        or receipt.get("command_and_timing") != results.get("shared_process")
    ):
        raise PackagingError("negative-control receipt status/process binding mismatch")
    if receipt.get("counts") != {
        "unique_cases": 2,
        "total_process_invocations": 1,
        "passed_unique_cases": 2,
        "failed_unique_cases": 0,
    }:
        raise PackagingError("negative-control receipt count contract mismatch")
    acceptance = receipt.get("acceptance_contract")
    if (
        not isinstance(acceptance, dict)
        or set(acceptance) != NEGATIVE_ACCEPTANCE_KEYS
        or any(item is not True for item in acceptance.values())
    ):
        raise PackagingError("negative-control receipt acceptance contract is not all true")
    evidence = receipt.get("evidence")
    if not isinstance(evidence, dict):
        raise PackagingError("negative-control receipt evidence is missing")
    semantic = evidence.get("semantic_results")
    raw = evidence.get("raw_diagnostic")
    if not isinstance(semantic, dict) or not isinstance(raw, dict):
        raise PackagingError("negative-control receipt result/raw bindings are missing")
    result_hash, result_size = hash_regular(results_path)
    if (
        semantic.get("path") != control_relative
        or semantic.get("sha256") != result_hash
        or semantic.get("bytes") != result_size
        or raw.get("path") != results.get("raw_diagnostic")
        or raw.get("sha256") != results.get("raw_diagnostic_sha256")
    ):
        raise PackagingError("negative-control receipt evidence hashes are inconsistent")
    raw_relative = results.get("raw_diagnostic")
    if not isinstance(raw_relative, str):
        raise PackagingError("negative-control results lack raw-diagnostic path")
    canonical_relative(raw_relative, "negative raw diagnostic")
    if not is_under_selected(raw_relative):
        raise PackagingError("negative-control raw diagnostic is outside selected roots")
    raw_path = regular_file(repo / raw_relative, "negative raw diagnostic")
    raw_hash, raw_size = hash_regular(raw_path)
    if (
        raw.get("path") != raw_relative
        or raw.get("sha256") != raw_hash
        or raw.get("bytes") != raw_size
        or results.get("raw_diagnostic_sha256") != raw_hash
    ):
        raise PackagingError("negative-control raw-diagnostic hashes are inconsistent")
    case_identities = evidence.get("case_diagnostics")
    result_rows = results.get("results")
    if (
        not isinstance(case_identities, list)
        or len(case_identities) != 2
        or not isinstance(result_rows, list)
        or len(result_rows) != 2
    ):
        raise PackagingError("negative-control receipt must bind exactly two case diagnostics")
    for identity, result_row in zip(case_identities, result_rows, strict=True):
        if not isinstance(identity, dict) or not isinstance(result_row, dict):
            raise PackagingError("negative-control diagnostic identity is malformed")
        relative = result_row.get("diagnostic")
        if not isinstance(relative, str):
            raise PackagingError("negative-control case diagnostic path is missing")
        canonical_relative(relative, "negative case diagnostic")
        if not is_under_selected(relative):
            raise PackagingError("negative-control case diagnostic is outside selected roots")
        diagnostic = regular_file(repo / relative, "negative case diagnostic")
        diagnostic_hash, diagnostic_size = hash_regular(diagnostic)
        if (
            result_row.get("diagnostic_sha256") != diagnostic_hash
            or identity.get("path") != relative
            or identity.get("sha256") != diagnostic_hash
            or identity.get("bytes") != diagnostic_size
        ):
            raise PackagingError(f"negative-control case diagnostic hash mismatch: {relative}")
    source_identities = receipt.get("source_identities")
    if not isinstance(source_identities, dict):
        raise PackagingError("negative-control receipt source identities are missing")
    if (
        source_identities.get("bound_inputs_before") != source_identities.get("bound_inputs_after")
        or source_identities.get("control_inputs_before") != source_identities.get("control_inputs_after")
    ):
        raise PackagingError("negative-control receipt records an input race")
    for stem in ("bound_inputs", "control_inputs"):
        for suffix in ("before", "after"):
            category = f"{stem}_{suffix}"
            if source_identities.get(category) != results.get(category):
                raise PackagingError(
                    f"negative-control receipt/results source identities differ: {category}"
                )
        category = f"{stem}_before"
        identities = source_identities.get(category)
        if not isinstance(identities, list) or not identities:
            raise PackagingError(f"negative-control receipt lacks {category}")
        for identity in identities:
            if not isinstance(identity, dict) or not isinstance(identity.get("path"), str):
                raise PackagingError(f"negative-control identity is malformed in {category}")
            relative = canonical_relative(identity["path"], f"negative {category} path")
            if not is_under_selected(relative):
                raise PackagingError(f"negative-control bound input escapes selected roots: {relative}")
            source = regular_file(repo / relative, f"negative {category} file")
            digest, size = hash_regular(source)
            if identity.get("sha256") != digest or identity.get("bytes") != size:
                raise PackagingError(f"negative-control bound-input hash mismatch: {relative}")


def validate_bound_evidence(
    repo: Path,
    bindings: dict[str, dict[str, Any]],
    control_relative: str,
) -> dict[str, Any]:
    final_build = validate_final_build(repo, bindings)
    validate_signature_audit(repo, bindings, final_build)
    validate_forbidden_scan(repo, bindings)
    validate_negative_receipt(repo, bindings, control_relative)
    validate_predecessor_postcheck(repo, bindings)
    return final_build


def parse_bindings(repo: Path, raw_items: list[str]) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    bound_paths: set[str] = set()
    for item in raw_items:
        if "=" not in item:
            raise PackagingError(f"evidence binding must have LABEL=REPO_RELATIVE_PATH form: {item!r}")
        label, relative = item.split("=", 1)
        if SAFE_BASENAME.fullmatch(label) is None or label in result:
            raise PackagingError(f"invalid or duplicate evidence label: {label!r}")
        canonical_relative(relative, f"evidence binding {label}")
        if not is_under_selected(relative):
            raise PackagingError(f"evidence binding is outside selected roots: {relative}")
        if relative in bound_paths:
            raise PackagingError(f"duplicate evidence-bound path: {relative!r}")
        path = regular_file(repo / relative, f"evidence binding {label}")
        digest, size = hash_regular(path)
        result[label] = {"path": relative, "sha256": digest, "size_bytes": size}
        bound_paths.add(relative)
    if set(result) != REQUIRED_EVIDENCE_LABELS:
        raise PackagingError(
            "evidence-binding label set mismatch: "
            f"missing={sorted(REQUIRED_EVIDENCE_LABELS-set(result))!r} "
            f"extra={sorted(set(result)-REQUIRED_EVIDENCE_LABELS)!r}"
        )
    return dict(sorted(result.items()))


def safe_ref(value: str, label: str) -> str:
    if SAFE_REF.fullmatch(value) is None or value.startswith("-") or ".." in value:
        raise PackagingError(f"invalid {label}: {value!r}")
    return value


def verify_repository(
    repo: Path,
    commands: CommandLog,
    *,
    commit: str,
    branch: str,
    final_tag: str,
) -> dict[str, Any]:
    if HEX40.fullmatch(commit) is None:
        raise PackagingError("--commit must be a full lowercase 40-hex object ID")
    safe_ref(branch, "branch")
    safe_ref(final_tag, "final tag")
    shallow = commands.text(["git", "rev-parse", "--is-shallow-repository"], repo, label="git_shallow")
    if shallow != "false":
        raise PackagingError("a complete, non-shallow repository is required")
    replacements = commands.text(
        ["git", "for-each-ref", "--format=%(refname)", "refs/replace/"], repo, label="git_replace_refs"
    )
    if replacements:
        raise PackagingError("Git replacement refs are forbidden")
    graft_path = commands.text(["git", "rev-parse", "--git-path", "info/grafts"], repo, label="git_graft_path")
    graft = Path(graft_path)
    if not graft.is_absolute():
        graft = repo / graft
    if graft.exists() and graft.stat().st_size:
        raise PackagingError("Git grafts are forbidden")
    status = commands.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all"],
        repo,
        label="git_status",
    )
    if status:
        raise PackagingError("repository must be completely clean before packaging")
    head = commands.text(["git", "rev-parse", "--verify", "HEAD^{commit}"], repo, label="git_head")
    branch_commit = commands.text(
        ["git", "rev-parse", "--verify", f"refs/heads/{branch}^{{commit}}"], repo, label="git_branch"
    )
    final_object = commands.text(
        ["git", "rev-parse", "--verify", f"refs/tags/{final_tag}"], repo, label="git_final_tag_object"
    )
    final_type = commands.text(["git", "cat-file", "-t", f"refs/tags/{final_tag}"], repo, label="git_final_tag_type")
    final_commit = commands.text(
        ["git", "rev-parse", "--verify", f"refs/tags/{final_tag}^{{commit}}"], repo, label="git_final_tag_commit"
    )
    predecessor_object = commands.text(
        ["git", "rev-parse", "--verify", f"refs/tags/{PREDECESSOR_TAG}"], repo, label="git_predecessor_tag_object"
    )
    predecessor_type = commands.text(
        ["git", "cat-file", "-t", f"refs/tags/{PREDECESSOR_TAG}"], repo, label="git_predecessor_tag_type"
    )
    predecessor_commit = commands.text(
        ["git", "rev-parse", "--verify", f"refs/tags/{PREDECESSOR_TAG}^{{commit}}"],
        repo,
        label="git_predecessor_tag_commit",
    )
    if not (head == branch_commit == final_commit == commit):
        raise PackagingError("HEAD, branch, final tag, and supplied commit do not agree")
    if final_type != "tag" or HEX40.fullmatch(final_object) is None:
        raise PackagingError("final tag must be an annotated tag object")
    if (
        predecessor_type != "tag"
        or predecessor_object != PREDECESSOR_TAG_OBJECT
        or predecessor_commit != PREDECESSOR_COMMIT
    ):
        raise PackagingError("immutable Experiment 002 predecessor identity mismatch")
    immutable_objects: dict[str, str] = {}
    for index, path in enumerate(PREDECESSOR_IMMUTABLE_PATHS):
        original = commands.text(
            ["git", "rev-parse", f"{PREDECESSOR_COMMIT}:{path}"],
            repo,
            label=f"git_predecessor_object_{index}",
        )
        current = commands.text(
            ["git", "rev-parse", f"{commit}:{path}"],
            repo,
            label=f"git_final_object_{index}",
        )
        if original != current:
            raise PackagingError(f"immutable predecessor path changed: {path}")
        immutable_objects[path] = original
    return {
        "source_repository_root": str(repo),
        "commit": commit,
        "branch": branch,
        "final_tag": final_tag,
        "final_tag_object": final_object,
        "predecessor_tag": PREDECESSOR_TAG,
        "predecessor_tag_object": predecessor_object,
        "predecessor_commit": predecessor_commit,
        "predecessor_immutable_objects": immutable_objects,
    }


def audit_tar(path: Path, commit: str) -> dict[str, Any]:
    _, archive_size = hash_regular(path)
    if archive_size > MAX_ARCHIVE_BYTES:
        raise PackagingError("archive exceeds safety limit")
    names: set[str] = set()
    folded: set[str] = set()
    kinds: dict[str, str] = {}
    regular_files: list[str] = []
    total = 0
    with tarfile.open(path, "r:gz") as archive:
        for member in archive:
            if len(names) >= MAX_MEMBERS:
                raise PackagingError("archive member-count limit exceeded")
            name = canonical_relative(member.name.rstrip("/"), "archive member")
            if name != ARCHIVE_ROOT and not name.startswith(ARCHIVE_ROOT + "/"):
                raise PackagingError(f"archive member is outside {ARCHIVE_ROOT}/: {name}")
            if name in names or name.casefold() in folded:
                raise PackagingError(f"duplicate/case-fold archive member: {name}")
            if member.issym() or member.islnk() or not (member.isdir() or member.isreg()):
                raise PackagingError(f"archive link or special member: {name}")
            if member.linkname or "linkpath" in member.pax_headers or getattr(member, "sparse", None):
                raise PackagingError(f"archive member has forbidden link/sparse metadata: {name}")
            unexpected_pax = set(member.pax_headers) - {"comment"}
            if unexpected_pax or (
                "comment" in member.pax_headers and member.pax_headers["comment"] != commit
            ):
                raise PackagingError(f"archive member has unexpected PAX metadata: {name}")
            if member.mode & 0o7000:
                raise PackagingError(f"archive member has special permission bits: {name}")
            if member.isdir() and member.size != 0:
                raise PackagingError(f"archive directory has nonzero size: {name}")
            if member.isreg():
                if member.size < 0 or member.size > MAX_FILE_BYTES:
                    raise PackagingError(f"archive file exceeds safety limit: {name}")
                total += member.size
                if total > MAX_TOTAL_BYTES:
                    raise PackagingError("archive expanded-size limit exceeded")
                regular_files.append(name)
            parent = PurePosixPath(name).parent
            while parent.as_posix() not in {".", ""}:
                if kinds.get(parent.as_posix()) == "file":
                    raise PackagingError(f"archive member is nested beneath a file: {name}")
                parent = parent.parent
            kinds[name] = "directory" if member.isdir() else "file"
            names.add(name)
            folded.add(name.casefold())
    expected_prefixes = tuple(f"{ARCHIVE_ROOT}/{root}" for root in SELECTED_ROOTS)
    for name in regular_files:
        if not any(name == root or name.startswith(root + "/") for root in expected_prefixes):
            raise PackagingError(f"archive regular file is outside selected roots: {name}")
    return {
        "member_count": len(names),
        "regular_file_count": len(regular_files),
        "expanded_regular_bytes": total,
        "links_or_special_entries": 0,
    }


def delivery_manifest_bytes(paths: list[Path]) -> bytes:
    rows = []
    for path in sorted(paths, key=lambda value: value.name.encode("utf-8")):
        if path.parent != paths[0].parent or SAFE_BASENAME.fullmatch(path.name) is None:
            raise PackagingError("delivery-manifest inputs must be safe basenames in one directory")
        digest, _ = hash_regular(path)
        rows.append(f"{digest}  {path.name}")
    return ("\n".join(rows) + "\n").encode("utf-8")


def package(args: argparse.Namespace) -> dict[str, Any]:
    repo = canonical_directory(Path(args.repo_root), "repository root")
    output = new_directory(Path(args.output_directory), "delivery output directory")
    verification = new_directory(Path(args.verification_output_directory), "verification output directory")
    if output == verification:
        raise PackagingError("delivery and verification output directories must differ")
    for label, candidate in (("delivery", output), ("verification", verification)):
        if os.path.commonpath([str(repo), str(candidate)]) == str(repo):
            raise PackagingError(f"{label} output directory must be outside the repository")
    control_relative = canonical_relative(args.control_results, "control-results path")
    commands = CommandLog()
    manifest = manifest_status(repo, commands)
    controls = control_summary(repo, control_relative)
    evidence = parse_bindings(repo, args.evidence_binding)
    final_build = validate_bound_evidence(repo, evidence, control_relative)
    repository = verify_repository(
        repo,
        commands,
        commit=args.commit,
        branch=args.branch,
        final_tag=args.final_tag,
    )
    output.mkdir(mode=0o700)
    archive = output / args.archive_name
    bundle = output / args.bundle_name
    receipt_path = output / args.receipt_name
    spec_path = output / args.spec_name
    delivery_manifest = output / "DELIVERY_SHA256SUMS"
    for path in (archive, bundle, receipt_path, spec_path, delivery_manifest):
        if path.exists() or path.is_symlink() or SAFE_BASENAME.fullmatch(path.name) is None:
            raise PackagingError(f"unsafe or existing package output: {path}")
    try:
        commands.run(
            [
                "git",
                "archive",
                "--format=tar.gz",
                f"--prefix={ARCHIVE_ROOT}/",
                f"--output={archive}",
                args.commit,
                "--",
                *SELECTED_ROOTS,
            ],
            repo,
            label="git_archive",
            timeout=300,
        )
        tar_audit = audit_tar(archive, args.commit)
        commands.run(
            [
                "git",
                "bundle",
                "create",
                str(bundle),
                f"refs/heads/{args.branch}",
                f"refs/tags/{args.final_tag}",
                f"refs/tags/{PREDECESSOR_TAG}",
            ],
            repo,
            label="git_bundle_create",
            timeout=300,
        )
        commands.run(["git", "bundle", "verify", str(bundle)], repo, label="git_bundle_verify")
        archive_hash, archive_size = hash_regular(archive)
        bundle_hash, bundle_size = hash_regular(bundle)
        receipt = {
            "schema": RECEIPT_SCHEMA,
            "status": "PASS",
            "generated_utc": utc_now(),
            "repository": repository,
            "selected_roots": list(SELECTED_ROOTS),
            "internal_manifest": manifest,
            "negative_controls": controls,
            "evidence_bindings": evidence,
            "qualifying_build": {
                **final_build,
                "target": FINAL_BUILD_TARGET,
                "root_default_build_covered": False,
                "root_import_file_unchanged_from_predecessor": True,
            },
            "artifacts": {
                "archive": {
                    "path": str(archive),
                    "sha256": archive_hash,
                    "size_bytes": archive_size,
                    "safe_tar_audit": tar_audit,
                },
                "bundle": {"path": str(bundle), "sha256": bundle_hash, "size_bytes": bundle_size},
            },
            "assurance_scope": {
                "preserved_lean_execution_evidence_bound": True,
                "fresh_lean_execution_performed": False,
                "kernel_proof_replay_performed": False,
                "fresh_delivery_verification_pending": True,
                "external_review": "PENDING",
                "statement": (
                    "Packaging binds the targeted Step-1 Lean build evidence; the unchanged root "
                    "default target was not rebuilt, and this is not a fresh kernel proof replay."
                ),
            },
            "packaging_commands": commands.rows,
        }
        write_exclusive(receipt_path, json_bytes(receipt))
        receipt_hash, receipt_size = hash_regular(receipt_path)
        spec = {
            "schema": SPEC_SCHEMA,
            "delivery": {
                "archive_path": str(archive),
                "archive_sha256": archive_hash,
                "archive_size_bytes": archive_size,
                "bundle_path": str(bundle),
                "bundle_sha256": bundle_hash,
                "bundle_size_bytes": bundle_size,
                "receipt_path": str(receipt_path),
                "receipt_sha256": receipt_hash,
                "receipt_size_bytes": receipt_size,
                "delivery_manifest_path": str(delivery_manifest),
                "verification_output_directory": str(verification),
                "archive_root": ARCHIVE_ROOT,
            },
            "repository": repository,
            "selected_roots": list(SELECTED_ROOTS),
            "internal_manifest": manifest,
            "negative_controls": controls,
            "evidence_bindings": evidence,
            "qualifying_build": {
                **final_build,
                "target": FINAL_BUILD_TARGET,
                "root_default_build_covered": False,
                "root_import_file_unchanged_from_predecessor": True,
            },
            "limits": {
                "max_archive_bytes": MAX_ARCHIVE_BYTES,
                "max_members": MAX_MEMBERS,
                "max_file_bytes": MAX_FILE_BYTES,
                "max_total_bytes": MAX_TOTAL_BYTES,
                "max_path_bytes": MAX_PATH_BYTES,
                "command_timeout_seconds": 300,
            },
            "verification_scope": {
                "fresh_lean_execution_expected": False,
                "kernel_proof_replay_expected": False,
                "external_review_expected": "PENDING",
            },
        }
        write_exclusive(spec_path, json_bytes(spec))
        write_exclusive(
            delivery_manifest,
            delivery_manifest_bytes([archive, bundle, receipt_path, spec_path]),
        )
        delivery_hash, delivery_size = hash_regular(delivery_manifest)
        return {
            "schema": PACKAGER_SCHEMA,
            "status": "PASS",
            "archive": {"path": str(archive), "sha256": archive_hash, "size_bytes": archive_size},
            "bundle": {"path": str(bundle), "sha256": bundle_hash, "size_bytes": bundle_size},
            "receipt": {"path": str(receipt_path), "sha256": receipt_hash, "size_bytes": receipt_size},
            "spec": {"path": str(spec_path), "sha256": hash_regular(spec_path)[0]},
            "delivery_manifest": {
                "path": str(delivery_manifest),
                "sha256": delivery_hash,
                "size_bytes": delivery_size,
            },
            "verification_output_directory": str(verification),
            "fresh_verification_status": "PENDING",
            "external_review": "PENDING",
        }
    except Exception as error:
        marker = output / "PACKAGING_FAILED.json"
        if not marker.exists():
            try:
                write_exclusive(
                    marker,
                    json_bytes(
                        {
                            "schema": "ndea.exp003.step1.packaging_failure.v1",
                            "status": "FAIL",
                            "timestamp_utc": utc_now(),
                            "error_type": type(error).__name__,
                            "error": str(error),
                            "commands": commands.rows,
                        }
                    ),
                )
            except Exception:
                pass
        raise


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    for name in ("manifest-write", "manifest-check"):
        command = subcommands.add_parser(name)
        command.add_argument("--repo-root", required=True)
    package_parser = subcommands.add_parser("package")
    package_parser.add_argument("--repo-root", required=True)
    package_parser.add_argument("--output-directory", required=True)
    package_parser.add_argument("--verification-output-directory", required=True)
    package_parser.add_argument("--commit", required=True)
    package_parser.add_argument("--branch", required=True)
    package_parser.add_argument("--final-tag", required=True)
    package_parser.add_argument("--control-results", default=DEFAULT_CONTROL_RESULTS)
    package_parser.add_argument("--evidence-binding", action="append", default=[])
    package_parser.add_argument("--archive-name", default="NDEA_Evolve_exp003_step1_final_evidence.tar.gz")
    package_parser.add_argument("--bundle-name", default="NDEA_Evolve_exp003_step1_final.bundle")
    package_parser.add_argument("--receipt-name", default="NDEA_Evolve_exp003_step1_final_delivery_receipt.json")
    package_parser.add_argument("--spec-name", default="NDEA_Evolve_exp003_step1_delivery_spec.json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.command == "manifest-write":
            outcome = write_manifest(canonical_directory(Path(args.repo_root), "repository root"))
        elif args.command == "manifest-check":
            commands = CommandLog()
            outcome = {
                "schema": PACKAGER_SCHEMA,
                "status": "PASS",
                **manifest_status(canonical_directory(Path(args.repo_root), "repository root"), commands),
            }
        else:
            for name in (args.archive_name, args.bundle_name, args.receipt_name, args.spec_name):
                if SAFE_BASENAME.fullmatch(name) is None or name in {".", "..", "DELIVERY_SHA256SUMS"}:
                    raise PackagingError(f"unsafe output basename: {name!r}")
            outcome = package(args)
    except Exception as error:
        print(f"EXP003_STEP1_PACKAGING_STATUS=FAIL\nERROR={type(error).__name__}: {error}", file=sys.stderr)
        return 1
    print(json.dumps(outcome, indent=2, sort_keys=True))
    print("EXP003_STEP1_PACKAGING_STATUS=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
