#!/usr/bin/env python3
"""Fresh, fail-closed verifier for an Experiment 003 Step-1 delivery.

The verifier validates hashes, archive safety, fresh extraction, the internal
manifest, Git bundle/ref/tree identities, bound assurance evidence, and the two
required mathematical-rejection classifications.  It deliberately does *not*
run Lean and must not be described as a fresh kernel proof replay.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import time
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any


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

SPEC_SCHEMA = "ndea.exp003.step1.delivery_spec.v1"
RECEIPT_SCHEMA = "ndea.exp003.step1.final_delivery.v1"
LOCAL_RECEIPT_SCHEMA = "ndea.exp003.step1.local_delivery_verification.v1"
CONTROL_SCHEMA = "ndea.exp003.lean_negative_controls.v1"
EXPECTED_CONTROL_CASES = (
    "01_strict_bound_false",
    "02_dropped_hermiticity_false",
)
EXPECTED_CONTROL_REASON = "EXPECTED_FALSE_STATEMENT_TYPE_MISMATCH"
NEGATIVE_PROCESS_ID = "exp003-lean-batched-negative-controls-001"
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


class VerificationError(RuntimeError):
    """A condition that invalidates the delivery."""


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
        raise VerificationError(f"cannot parse strict JSON {path}: {error}") from error


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def require_mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise VerificationError(f"{label} must be an object")
    return value


def exact_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    observed = set(value)
    if observed != expected:
        raise VerificationError(
            f"{label} key-set mismatch: missing={sorted(expected-observed)!r} extra={sorted(observed-expected)!r}"
        )


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise VerificationError(f"{label} must be a nonempty string")
    return value


def require_int(value: Any, label: str, minimum: int, maximum: int) -> int:
    if type(value) is not int or value < minimum or value > maximum:
        raise VerificationError(f"{label} must be an integer in [{minimum}, {maximum}]")
    return value


def canonical_relative(raw: str, label: str, max_path_bytes: int) -> str:
    if (
        not isinstance(raw, str)
        or not raw
        or "\x00" in raw
        or "\\" in raw
        or any(ord(character) < 32 or ord(character) == 127 for character in raw)
    ):
        raise VerificationError(f"{label} is not a canonical POSIX relative path: {raw!r}")
    try:
        encoded = raw.encode("utf-8", errors="strict")
    except UnicodeError as error:
        raise VerificationError(f"{label} is not UTF-8 encodable: {raw!r}") from error
    if len(encoded) > max_path_bytes:
        raise VerificationError(f"{label} exceeds the configured path limit: {raw!r}")
    pure = PurePosixPath(raw)
    if (
        pure.is_absolute()
        or not pure.parts
        or any(part in {"", ".", ".."} for part in pure.parts)
        or pure.as_posix() != raw
        or re.match(r"^[A-Za-z]:", pure.parts[0])
    ):
        raise VerificationError(f"{label} is not canonical and relative: {raw!r}")
    return raw


def regular_file(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise VerificationError(f"{label} must be absolute: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        metadata = os.lstat(path)
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise VerificationError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical or not stat.S_ISREG(metadata.st_mode):
        raise VerificationError(f"{label} must be a canonical regular non-link file: {path}")
    return resolved


def canonical_directory(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise VerificationError(f"{label} must be absolute: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        metadata = os.lstat(path)
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise VerificationError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical or not stat.S_ISDIR(metadata.st_mode):
        raise VerificationError(f"{label} must be a canonical non-link directory: {path}")
    return resolved


def new_directory(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise VerificationError(f"{label} must be an absolute path that does not exist: {path}")
    canonical_directory(path.parent, f"{label} parent")
    return Path(os.path.abspath(path))


def hash_regular(path: Path) -> tuple[str, int]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise VerificationError(f"cannot open {path} without following links: {error}") from error
    digest = hashlib.sha256()
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise VerificationError(f"not a regular file: {path}")
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            digest.update(block)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    current = os.lstat(path)
    before_id = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
    after_id = (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
    if before_id != after_id or (current.st_dev, current.st_ino) != (before.st_dev, before.st_ino):
        raise VerificationError(f"file changed while hashing: {path}")
    return digest.hexdigest(), before.st_size


def write_exclusive(path: Path, payload: bytes) -> None:
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except OSError as error:
        raise VerificationError(f"refusing to overwrite {path}: {error}") from error
    try:
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise VerificationError(f"short write while creating {path}")
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


class Audit:
    def __init__(self) -> None:
        self.checks: list[dict[str, Any]] = []
        self.commands: list[dict[str, Any]] = []

    def require(self, label: str, condition: bool, observed: Any, expected: Any) -> None:
        self.checks.append(
            {"label": label, "status": "PASS" if condition else "FAIL", "observed": observed, "expected": expected}
        )
        if not condition:
            raise VerificationError(f"check failed: {label}: observed={observed!r} expected={expected!r}")

    def run(self, argv: list[str], cwd: Path, label: str, timeout: int) -> bytes:
        started = utc_now()
        before = time.monotonic()
        try:
            completed = subprocess.run(
                argv,
                cwd=cwd,
                env=clean_git_environment(),
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise VerificationError(f"command {label} could not complete: {error}") from error
        self.commands.append(
            {
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
        )
        if completed.returncode != 0:
            stderr = completed.stderr.decode("utf-8", errors="replace")[-4000:]
            raise VerificationError(f"command {label} failed ({completed.returncode}): {stderr}")
        return completed.stdout

    def text(self, argv: list[str], cwd: Path, label: str, timeout: int) -> str:
        try:
            return self.run(argv, cwd, label, timeout).decode("utf-8", errors="strict").strip()
        except UnicodeError as error:
            raise VerificationError(f"command {label} returned non-UTF-8 output") from error


def safe_ref(value: Any, label: str) -> str:
    text = require_string(value, label)
    if SAFE_REF.fullmatch(text) is None or text.startswith("-") or ".." in text:
        raise VerificationError(f"invalid {label}: {text!r}")
    return text


def parse_limits(raw: Any) -> dict[str, int]:
    value = require_mapping(raw, "limits")
    expected = {
        "max_archive_bytes",
        "max_members",
        "max_file_bytes",
        "max_total_bytes",
        "max_path_bytes",
        "command_timeout_seconds",
    }
    exact_keys(value, expected, "limits")
    result = {
        "max_archive_bytes": require_int(value["max_archive_bytes"], "max_archive_bytes", 1, 20 * 1024**3),
        "max_members": require_int(value["max_members"], "max_members", 1, 100_000),
        "max_file_bytes": require_int(value["max_file_bytes"], "max_file_bytes", 1, 10 * 1024**3),
        "max_total_bytes": require_int(value["max_total_bytes"], "max_total_bytes", 1, 20 * 1024**3),
        "max_path_bytes": require_int(value["max_path_bytes"], "max_path_bytes", 64, 16_384),
        "command_timeout_seconds": require_int(value["command_timeout_seconds"], "command_timeout_seconds", 1, 1800),
    }
    if result["max_file_bytes"] > result["max_total_bytes"]:
        raise VerificationError("max_file_bytes cannot exceed max_total_bytes")
    return result


def parse_artifact(raw: Any, label: str) -> tuple[Path, str, int]:
    value = require_mapping(raw, label)
    exact_keys(value, {f"{label}_path", f"{label}_sha256", f"{label}_size_bytes"}, label)
    path = regular_file(Path(require_string(value[f"{label}_path"], f"{label}.path")), label)
    digest = require_string(value[f"{label}_sha256"], f"{label}.sha256")
    size = require_int(value[f"{label}_size_bytes"], f"{label}.size", 0, 20 * 1024**3)
    if HEX64.fullmatch(digest) is None:
        raise VerificationError(f"{label} hash is not lowercase SHA-256")
    return path, digest, size


def validate_control_result(
    path: Path,
    expected: dict[str, Any],
    source_repository_root: Path,
    audit: Audit,
) -> None:
    value = require_mapping(read_json_strict(path), "negative-control results")
    audit.require("control_schema", value.get("schema") == CONTROL_SCHEMA, value.get("schema"), CONTROL_SCHEMA)
    audit.require("control_status", value.get("status") == "PASS", value.get("status"), "PASS")
    audit.require(
        "control_pass_count",
        value.get("passed_unique_cases") == 2 and value.get("failed_unique_cases") == 0,
        [value.get("passed_unique_cases"), value.get("failed_unique_cases")],
        [2, 0],
    )
    audit.require("control_unique_cases", value.get("unique_cases") == 2, value.get("unique_cases"), 2)
    audit.require("control_process_count", value.get("total_process_invocations") == 1, value.get("total_process_invocations"), 1)
    shared = require_mapping(value.get("shared_process"), "negative-control shared_process")
    expected_control_argv = [
        PINNED_LAKE,
        "env",
        "lean",
        str(source_repository_root / NEGATIVE_BATCH_SOURCE),
    ]
    audit.require("control_pinned_lake_argv", shared.get("argv") == expected_control_argv, shared.get("argv"), expected_control_argv)
    audit.require("control_source_cwd", shared.get("cwd") == str(source_repository_root), shared.get("cwd"), str(source_repository_root))
    audit.require("control_process_id", shared.get("process_invocation_id") == NEGATIVE_PROCESS_ID, shared.get("process_invocation_id"), NEGATIVE_PROCESS_ID)
    audit.require("control_child_exit", shared.get("exit_code") == 1, shared.get("exit_code"), 1)
    audit.require("control_child_not_timeout", shared.get("timed_out") is False, shared.get("timed_out"), False)
    audit.require("control_child_spawn", shared.get("spawn_error") is None, shared.get("spawn_error"), None)
    audit.require("control_output_limit", shared.get("output_limit_exceeded") is False, shared.get("output_limit_exceeded"), False)
    audit.require(
        "control_shared_process_count",
        shared.get("total_process_invocations") == 1,
        shared.get("total_process_invocations"),
        1,
    )
    global_checks = require_mapping(value.get("global_diagnostic_checks"), "global diagnostic checks")
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
    audit.require(
        "control_global_check_set",
        set(global_checks) == required_global_checks,
        sorted(global_checks),
        sorted(required_global_checks),
    )
    audit.require("control_global_checks", all(item is True for item in global_checks.values()), global_checks, "all true")
    rows = value.get("results")
    if not isinstance(rows, list) or len(rows) != 2:
        raise VerificationError("negative-control results must contain exactly two case rows")
    observed_cases: list[str] = []
    process_ids: set[str] = set()
    for index, row_raw in enumerate(rows):
        row = require_mapping(row_raw, f"negative-control case {index}")
        case = require_string(row.get("case"), f"negative-control case {index}.case")
        observed_cases.append(case)
        audit.require(f"control_{case}_status", row.get("status") == "PASS", row.get("status"), "PASS")
        audit.require(f"control_{case}_attributable", row.get("attributable_rejection") is True, row.get("attributable_rejection"), True)
        audit.require(f"control_{case}_reason", row.get("reason_code") == EXPECTED_CONTROL_REASON, row.get("reason_code"), EXPECTED_CONTROL_REASON)
        checks = require_mapping(row.get("diagnostic_checks"), f"negative-control {case} checks")
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
        audit.require(f"control_{case}_required_checks", set(checks) == required, sorted(checks), sorted(required))
        audit.require(f"control_{case}_all_checks", bool(checks) and all(item is True for item in checks.values()), checks, "all true")
        process_id = require_string(row.get("process_invocation_id"), f"negative-control {case} process ID")
        audit.require(f"control_{case}_process_id", process_id == NEGATIVE_PROCESS_ID, process_id, NEGATIVE_PROCESS_ID)
        process_ids.add(process_id)
    audit.require("control_case_identity_order", tuple(observed_cases) == EXPECTED_CONTROL_CASES, observed_cases, list(EXPECTED_CONTROL_CASES))
    audit.require("control_one_shared_process", len(process_ids) == 1, len(process_ids), 1)
    audit.require("control_spec_case_ids", expected.get("case_ids") == list(EXPECTED_CONTROL_CASES), expected.get("case_ids"), list(EXPECTED_CONTROL_CASES))
    audit.require("control_spec_unique_count", expected.get("unique_case_count") == 2, expected.get("unique_case_count"), 2)
    audit.require("control_spec_process_count", expected.get("lean_process_invocation_count") == 1, expected.get("lean_process_invocation_count"), 1)
    audit.require("control_spec_child_exit", expected.get("lean_child_exit_code") == 1, expected.get("lean_child_exit_code"), 1)
    audit.require("control_spec_classification", expected.get("classification") == EXPECTED_CONTROL_REASON, expected.get("classification"), EXPECTED_CONTROL_REASON)


def binding_file(
    root: Path, bindings: dict[str, Any], label: str, max_path_bytes: int
) -> tuple[Path, str, dict[str, Any]]:
    raw = require_mapping(bindings[label], f"evidence binding {label}")
    exact_keys(raw, {"path", "sha256", "size_bytes"}, f"evidence binding {label}")
    relative = canonical_relative(
        require_string(raw["path"], f"evidence binding {label}.path"),
        f"evidence binding {label}.path",
        max_path_bytes,
    )
    if not is_under_selected(relative):
        raise VerificationError(f"evidence binding is outside selected roots: {relative}")
    path = regular_file(root / relative, f"evidence binding {label}")
    return path, relative, raw


def verify_binding_hash(path: Path, row: dict[str, Any], label: str, audit: Audit) -> None:
    digest, size = hash_regular(path)
    audit.require(f"evidence_{label}_sha256", digest == row.get("sha256"), digest, row.get("sha256"))
    audit.require(f"evidence_{label}_size", size == row.get("size_bytes"), size, row.get("size_bytes"))


def validate_final_build_evidence(
    root: Path,
    source_repository_root: Path,
    bindings: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> dict[str, Any]:
    log, log_relative, log_row = binding_file(root, bindings, "final_build_log", max_path_bytes)
    timing_path, _, timing_row = binding_file(root, bindings, "final_build_timing", max_path_bytes)
    verify_binding_hash(log, log_row, "final_build_log", audit)
    verify_binding_hash(timing_path, timing_row, "final_build_timing", audit)
    timing = require_mapping(read_json_strict(timing_path), "final-build timing")
    audit.require("final_build_timing_schema", timing.get("schema") == FINAL_BUILD_TIMING_SCHEMA, timing.get("schema"), FINAL_BUILD_TIMING_SCHEMA)
    audit.require("final_build_exit", timing.get("exit_code") == 0, timing.get("exit_code"), 0)
    log_hash, log_size = hash_regular(log)
    expected_original_log = str(source_repository_root.joinpath(*PurePosixPath(log_relative).parts))
    audit.require("final_build_cwd", timing.get("cwd") == str(source_repository_root), timing.get("cwd"), str(source_repository_root))
    audit.require("final_build_log_path", timing.get("log") == expected_original_log, timing.get("log"), expected_original_log)
    audit.require("final_build_log_hash", timing.get("log_sha256") == log_hash, timing.get("log_sha256"), log_hash)
    audit.require("final_build_log_size", timing.get("log_size_bytes") == log_size, timing.get("log_size_bytes"), log_size)
    argv = timing.get("argv")
    if not isinstance(argv, list) or len(argv) != 8 or any(type(item) is not str for item in argv):
        raise VerificationError("final-build argv must be the exact eight-element bounded command")
    timeout_match = re.fullmatch(r"([1-9][0-9]{0,3})s", argv[3])
    expected_tail = [
        PINNED_LAKE,
        "-v",
        "build",
        FINAL_BUILD_TARGET,
    ]
    argv_ok = (
        argv[0] == "/usr/bin/timeout"
        and argv[1] == "--signal=TERM"
        and argv[2] == "--kill-after=10s"
        and timeout_match is not None
        and int(timeout_match.group(1)) <= 3600
        and argv[4:] == expected_tail
    )
    audit.require("final_build_argv", argv_ok, argv, ["/usr/bin/timeout", "--signal=TERM", "--kill-after=10s", "<1..3600>s", *expected_tail])
    try:
        log_text = log.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"final-build log is not strict UTF-8: {error}") from error
    audit.require("final_build_success_marker", "Build completed successfully" in log_text, "Build completed successfully" in log_text, True)
    audit.require("final_build_no_error_marker", "error:" not in log_text.lower(), "error:" in log_text.lower(), False)
    return {
        "argv": argv,
        "cwd": str(source_repository_root),
        "exit_code": 0,
        "log_sha256": log_hash,
        "log_size_bytes": log_size,
        "log_relative_path": log_relative,
    }


def validate_signature_evidence(
    root: Path,
    source_repository_root: Path,
    bindings: dict[str, Any],
    build: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> None:
    path, _, row = binding_file(root, bindings, "signature_axiom_audit", max_path_bytes)
    verify_binding_hash(path, row, "signature_axiom_audit", audit)
    value = require_mapping(read_json_strict(path), "signature/axiom audit")
    audit.require("signature_audit_schema", value.get("schema") == SIGNATURE_AUDIT_SCHEMA, value.get("schema"), SIGNATURE_AUDIT_SCHEMA)
    audit.require("signature_audit_status", value.get("status") == "PASS", value.get("status"), "PASS")
    audit.require("signature_audit_count", value.get("headline_declaration_count") == 3, value.get("headline_declaration_count"), 3)
    audit.require("signature_audit_markers", value.get("audit_marker_pair_count") == 1, value.get("audit_marker_pair_count"), 1)
    audit.require("signature_audit_allowed", set(value.get("allowed_dependencies", [])) == ALLOWED_AXIOMS, value.get("allowed_dependencies"), sorted(ALLOWED_AXIOMS))
    audit.require("signature_audit_unexpected", value.get("unexpected_dependencies") == [], value.get("unexpected_dependencies"), [])
    expected_source = str(source_repository_root.joinpath(*PurePosixPath(build["log_relative_path"]).parts))
    audit.require("signature_audit_source_path", value.get("source_log") == expected_source, value.get("source_log"), expected_source)
    audit.require("signature_audit_source_hash", value.get("source_log_sha256") == build["log_sha256"], value.get("source_log_sha256"), build["log_sha256"])
    rows = value.get("declarations")
    if not isinstance(rows, list) or len(rows) != 3:
        raise VerificationError("signature/axiom audit must contain exactly three declarations")
    names: list[str] = []
    for declaration in rows:
        item = require_mapping(declaration, "signature/axiom declaration")
        name = require_string(item.get("name"), "signature/axiom declaration name")
        names.append(name)
        signature = item.get("signature")
        dependencies = item.get("dependencies")
        audit.require(f"signature_text:{name}", isinstance(signature, str) and signature.startswith("@" + name + " :"), signature, "@NAME : ...")
        audit.require(
            f"signature_dependencies:{name}",
            isinstance(dependencies, list)
            and all(isinstance(dep, str) for dep in dependencies)
            and len(dependencies) == len(set(dependencies))
            and set(dependencies).issubset(ALLOWED_AXIOMS),
            dependencies,
            "unique allowed subset",
        )
    audit.require("signature_headline_order", tuple(names) == HEADLINE_DECLARATIONS, names, list(HEADLINE_DECLARATIONS))


def validate_forbidden_evidence(
    root: Path,
    bindings: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> None:
    path, _, row = binding_file(root, bindings, "forbidden_scan", max_path_bytes)
    verify_binding_hash(path, row, "forbidden_scan", audit)
    value = require_mapping(read_json_strict(path), "forbidden scan")
    audit.require("forbidden_schema", value.get("schema") == FORBIDDEN_SCAN_SCHEMA, value.get("schema"), FORBIDDEN_SCAN_SCHEMA)
    audit.require("forbidden_status", value.get("status") == "PASS", value.get("status"), "PASS")
    audit.require("forbidden_file_count", value.get("production_file_count") == 1, value.get("production_file_count"), 1)
    audit.require("forbidden_match_count", value.get("total_matches") == 0, value.get("total_matches"), 0)
    expected_policy = {
        "case_sensitive": True,
        "whole_token": True,
        "comments_and_strings_included": True,
        "tokens": list(FORBIDDEN_TOKENS),
    }
    audit.require("forbidden_policy", value.get("policy") == expected_policy, value.get("policy"), expected_policy)
    rows = value.get("files")
    if not isinstance(rows, list) or len(rows) != 1:
        raise VerificationError("forbidden scan must contain exactly one production-source row")
    pattern = re.compile(r"\b(?:" + "|".join(map(re.escape, FORBIDDEN_TOKENS)) + r")\b")
    names: list[str] = []
    for source_row_raw in rows:
        source_row = require_mapping(source_row_raw, "forbidden-scan source row")
        relative = canonical_relative(require_string(source_row.get("path"), "forbidden source path"), "forbidden source path", max_path_bytes)
        names.append(relative)
        source = regular_file(root / relative, "production source under forbidden scan")
        text = source.read_text(encoding="utf-8", errors="strict")
        recomputed = [match.group(0) for line in text.splitlines() for match in pattern.finditer(line)]
        digest, size = hash_regular(source)
        audit.require(f"forbidden_zero:{relative}", not recomputed and source_row.get("matches") == [], {"recomputed": recomputed, "recorded": source_row.get("matches")}, {"recomputed": [], "recorded": []})
        audit.require(f"forbidden_hash:{relative}", source_row.get("sha256") == digest, source_row.get("sha256"), digest)
        audit.require(f"forbidden_size:{relative}", source_row.get("size_bytes") == size, source_row.get("size_bytes"), size)
    audit.require("forbidden_source_order", tuple(names) == PRODUCTION_SOURCES, names, list(PRODUCTION_SOURCES))


def validate_predecessor_evidence(
    root: Path,
    bindings: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> None:
    path, _, row = binding_file(root, bindings, "predecessor_postcheck", max_path_bytes)
    verify_binding_hash(path, row, "predecessor_postcheck", audit)
    value = require_mapping(read_json_strict(path), "predecessor postcheck")
    expected = {
        "schema": PREDECESSOR_POSTCHECK_SCHEMA,
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
    for field, expected_value in expected.items():
        audit.require(f"predecessor_{field}", value.get(field) == expected_value, value.get(field), expected_value)
    current = {
        "operator_cayley_sha256": hash_regular(root / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean")[0],
        "adversarial_witnesses_sha256": hash_regular(root / "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean")[0],
        "lean_toolchain_sha256": hash_regular(root / "lean-toolchain")[0],
        "lakefile_sha256": hash_regular(root / "lakefile.toml")[0],
        "lake_manifest_sha256": hash_regular(root / "lake-manifest.json")[0],
    }
    for field, digest in current.items():
        audit.require(f"predecessor_current_bytes_{field}", value.get(field) == digest, value.get(field), digest)


DIAGNOSTIC_HEADER = re.compile(
    r"^(?P<path>.+):(?P<line>[0-9]+):(?P<column>[0-9]+):[ \t]+"
    r"(?P<severity>error|warning|information):[ \t]*(?P<message>.*)$",
    re.IGNORECASE | re.MULTILINE,
)
INFRA_MARKERS = (
    "unknown module prefix",
    "unknown package",
    "unknown identifier",
    "unknown constant",
    "object file",
    "does not exist in the search path",
    "no such file or directory",
    "invalid import",
    "failed to build",
    "build failed",
    "maximum heartbeats",
    "maximum recursion depth",
    "detected a panic",
)
SYNTAX_MARKERS = (
    "unexpected token",
    "unexpected end of input",
    "invalid syntax",
    "invalid 'end'",
    "unterminated",
    "declaration has metavariables",
)
TACTIC_MARKERS = (
    "tactic '",
    "tactic failed",
    "unsolved goals",
    "no goals to be solved",
    "failed to synthesize",
    "invalid field notation",
    "declaration uses 'sorry'",
)


def contains_marker(text: str, groups: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return any(marker in lowered for marker in groups)


def verify_identity_rows(
    root: Path,
    rows: Any,
    label: str,
    max_path_bytes: int,
    audit: Audit,
) -> None:
    if not isinstance(rows, list) or not rows:
        raise VerificationError(f"{label} must be a nonempty identity list")
    seen: set[str] = set()
    for raw in rows:
        row = require_mapping(raw, f"{label} identity")
        relative = canonical_relative(require_string(row.get("path"), f"{label} path"), f"{label} path", max_path_bytes)
        if relative in seen or not is_under_selected(relative):
            raise VerificationError(f"duplicate/out-of-payload {label} path: {relative}")
        seen.add(relative)
        path = regular_file(root / relative, f"{label} file")
        digest, size = hash_regular(path)
        audit.require(f"{label}_hash:{relative}", row.get("sha256") == digest, row.get("sha256"), digest)
        audit.require(f"{label}_size:{relative}", row.get("bytes") == size, row.get("bytes"), size)


def parse_strict_json_text(text: str, label: str) -> Any:
    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=reject_json_constant,
        )
    except (json.JSONDecodeError, ValueError) as error:
        raise VerificationError(f"cannot parse {label}: {error}") from error


def validate_negative_evidence(
    root: Path,
    bindings: dict[str, Any],
    control_path: Path,
    results: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> None:
    receipt_path, _, receipt_row = binding_file(
        root, bindings, "negative_control_execution_receipt", max_path_bytes
    )
    verify_binding_hash(receipt_path, receipt_row, "negative_control_execution_receipt", audit)
    receipt = require_mapping(read_json_strict(receipt_path), "negative-control execution receipt")
    audit.require("negative_receipt_schema", receipt.get("schema") == NEGATIVE_RECEIPT_SCHEMA, receipt.get("schema"), NEGATIVE_RECEIPT_SCHEMA)
    audit.require("negative_receipt_status", receipt.get("status") == "PASS", receipt.get("status"), "PASS")
    audit.require("negative_receipt_process_id", receipt.get("process_invocation_id") == NEGATIVE_PROCESS_ID, receipt.get("process_invocation_id"), NEGATIVE_PROCESS_ID)
    audit.require("negative_receipt_process", receipt.get("command_and_timing") == results.get("shared_process"), receipt.get("command_and_timing"), results.get("shared_process"))
    expected_counts = {
        "unique_cases": 2,
        "total_process_invocations": 1,
        "passed_unique_cases": 2,
        "failed_unique_cases": 0,
    }
    audit.require("negative_receipt_counts", receipt.get("counts") == expected_counts, receipt.get("counts"), expected_counts)
    acceptance = require_mapping(receipt.get("acceptance_contract"), "negative receipt acceptance")
    audit.require(
        "negative_receipt_acceptance_keys",
        set(acceptance) == NEGATIVE_ACCEPTANCE_KEYS,
        sorted(acceptance),
        sorted(NEGATIVE_ACCEPTANCE_KEYS),
    )
    audit.require("negative_receipt_acceptance", all(item is True for item in acceptance.values()), acceptance, "all true")
    source_ids = require_mapping(receipt.get("source_identities"), "negative receipt source identities")
    for category in ("bound_inputs", "control_inputs"):
        before = source_ids.get(category + "_before")
        after = source_ids.get(category + "_after")
        audit.require(f"negative_{category}_stable", before == after, before, after)
        verify_identity_rows(root, before, "negative_" + category, max_path_bytes, audit)
        audit.require(f"negative_results_{category}_before", results.get(category + "_before") == before, results.get(category + "_before"), before)
        audit.require(f"negative_results_{category}_after", results.get(category + "_after") == after, results.get(category + "_after"), after)

    evidence = require_mapping(receipt.get("evidence"), "negative receipt evidence")
    semantic = require_mapping(evidence.get("semantic_results"), "negative semantic-results identity")
    results_relative = canonical_relative(require_string(semantic.get("path"), "negative results path"), "negative results path", max_path_bytes)
    digest, size = hash_regular(control_path)
    audit.require("negative_semantic_result_path", root / results_relative == control_path, results_relative, str(control_path.relative_to(root)))
    audit.require("negative_semantic_result_hash", semantic.get("sha256") == digest, semantic.get("sha256"), digest)
    audit.require("negative_semantic_result_size", semantic.get("bytes") == size, semantic.get("bytes"), size)

    raw_relative = canonical_relative(require_string(results.get("raw_diagnostic"), "negative raw diagnostic"), "negative raw diagnostic", max_path_bytes)
    raw_path = regular_file(root / raw_relative, "negative raw diagnostic")
    raw_hash, raw_size = hash_regular(raw_path)
    audit.require("negative_raw_hash", results.get("raw_diagnostic_sha256") == raw_hash, results.get("raw_diagnostic_sha256"), raw_hash)
    raw_identity = require_mapping(evidence.get("raw_diagnostic"), "negative raw-diagnostic identity")
    audit.require("negative_receipt_raw_path", raw_identity.get("path") == raw_relative, raw_identity.get("path"), raw_relative)
    audit.require("negative_receipt_raw_hash", raw_identity.get("sha256") == raw_hash, raw_identity.get("sha256"), raw_hash)
    audit.require("negative_receipt_raw_size", raw_identity.get("bytes") == raw_size, raw_identity.get("bytes"), raw_size)

    combined_relative = canonical_relative(require_string(results.get("combined_source"), "negative combined source"), "negative combined source", max_path_bytes)
    combined_path = regular_file(root / combined_relative, "negative combined source")
    combined_hash, _ = hash_regular(combined_path)
    audit.require("negative_combined_hash", results.get("combined_source_sha256") == combined_hash, results.get("combined_source_sha256"), combined_hash)

    raw_text = raw_path.read_text(encoding="utf-8", errors="strict")
    harness_marker = "=== SHARED PROCESS HARNESS ===\n"
    output_marker = "\n=== MERGED STDOUT+STDERR ===\n"
    if not raw_text.startswith(harness_marker) or raw_text.count(output_marker) != 1:
        raise VerificationError("negative raw diagnostic framing mismatch")
    harness_text, output = raw_text[len(harness_marker) :].split(output_marker, 1)
    harness = require_mapping(parse_strict_json_text(harness_text, "negative raw harness"), "negative raw harness")
    audit.require("negative_raw_harness", harness == results.get("shared_process"), harness, results.get("shared_process"))
    matches = list(DIAGNOSTIC_HEADER.finditer(output))
    audit.require("negative_raw_header_count", len(matches) == 2, len(matches), 2)
    preamble = output[: matches[0].start()] if matches else output
    audit.require("negative_raw_no_preamble", preamble.strip() == "", preamble, "")
    result_rows = results.get("results")
    if not isinstance(result_rows, list) or len(result_rows) != 2:
        raise VerificationError("negative result rows missing during raw replay")
    source_argument = results.get("shared_process", {}).get("argv", [None])[-1]
    witnesses = [require_string(row.get("witness_expected_in_diagnostic"), "negative witness") for row in result_rows]
    case_diagnostic_identities = evidence.get("case_diagnostics")
    if not isinstance(case_diagnostic_identities, list) or len(case_diagnostic_identities) != 2:
        raise VerificationError("negative receipt must bind exactly two case diagnostics")
    for index, (match, row_raw) in enumerate(zip(matches, result_rows, strict=True)):
        row = require_mapping(row_raw, f"negative case {index}")
        end = matches[index + 1].start() if index + 1 < len(matches) else len(output)
        block = output[match.start() : end]
        audit.require(f"negative_raw_severity_{index}", match.group("severity").lower() == "error", match.group("severity"), "error")
        audit.require(f"negative_raw_message_{index}", match.group("message").strip().lower() == "type mismatch", match.group("message"), "type mismatch")
        audit.require(f"negative_raw_path_{index}", match.group("path") == source_argument, match.group("path"), source_argument)
        audit.require(f"negative_raw_line_{index}", int(match.group("line")) == row.get("combined_exact_line"), int(match.group("line")), row.get("combined_exact_line"))
        witness = witnesses[index]
        present = {candidate for candidate in witnesses if candidate in block}
        audit.require(f"negative_raw_witness_{index}", present == {witness}, sorted(present), [witness])
        audit.require(f"negative_raw_types_{index}", re.search(r"\bhas type\b[\s\S]*\bbut is expected to have type\b", block, re.IGNORECASE) is not None, block, "actual/expected type text")
        marker_free = not (
            contains_marker(block, INFRA_MARKERS)
            or contains_marker(block, SYNTAX_MARKERS)
            or contains_marker(block, TACTIC_MARKERS)
        )
        audit.require(f"negative_raw_no_bad_marker_{index}", marker_free, marker_free, True)
        source_relative = canonical_relative(require_string(row.get("source"), "negative fixture source"), "negative fixture source", max_path_bytes)
        source_path = regular_file(root / source_relative, "negative fixture source")
        source_hash, source_size = hash_regular(source_path)
        audit.require(f"negative_fixture_hash_{index}", row.get("source_sha256") == source_hash, row.get("source_sha256"), source_hash)
        audit.require(f"negative_fixture_size_{index}", row.get("source_bytes") == source_size, row.get("source_bytes"), source_size)
        diagnostic_relative = canonical_relative(require_string(row.get("diagnostic"), "case diagnostic"), "case diagnostic", max_path_bytes)
        diagnostic_path = regular_file(root / diagnostic_relative, "case diagnostic")
        diagnostic_hash, diagnostic_size = hash_regular(diagnostic_path)
        audit.require(f"negative_case_log_hash_{index}", row.get("diagnostic_sha256") == diagnostic_hash, row.get("diagnostic_sha256"), diagnostic_hash)
        identity = require_mapping(case_diagnostic_identities[index], "case diagnostic identity")
        audit.require(f"negative_receipt_case_path_{index}", identity.get("path") == diagnostic_relative, identity.get("path"), diagnostic_relative)
        audit.require(f"negative_receipt_case_hash_{index}", identity.get("sha256") == diagnostic_hash, identity.get("sha256"), diagnostic_hash)
        audit.require(f"negative_receipt_case_size_{index}", identity.get("bytes") == diagnostic_size, identity.get("bytes"), diagnostic_size)
        case_text = diagnostic_path.read_text(encoding="utf-8", errors="strict")
        case_marker = "\n=== LEAN DIAGNOSTIC BLOCK ===\n"
        if not case_text.startswith("=== SHARED PROCESS REFERENCE ===\n") or case_text.count(case_marker) != 1:
            raise VerificationError(f"case diagnostic framing mismatch: {diagnostic_relative}")
        reference_text, recorded_block = case_text[len("=== SHARED PROCESS REFERENCE ===\n") :].split(case_marker, 1)
        reference = require_mapping(parse_strict_json_text(reference_text, "case diagnostic reference"), "case diagnostic reference")
        audit.require(f"negative_case_block_{index}", recorded_block == block, recorded_block, block)
        audit.require(f"negative_case_reference_id_{index}", reference.get("case") == row.get("case"), reference.get("case"), row.get("case"))
        audit.require(f"negative_case_reference_process_{index}", reference.get("process_invocation_id") == NEGATIVE_PROCESS_ID == row.get("process_invocation_id"), reference.get("process_invocation_id"), NEGATIVE_PROCESS_ID)
        audit.require(f"negative_case_reference_raw_{index}", reference.get("raw_diagnostic_sha256") == raw_hash, reference.get("raw_diagnostic_sha256"), raw_hash)
        audit.require(f"negative_case_reference_line_{index}", reference.get("combined_exact_line") == row.get("combined_exact_line"), reference.get("combined_exact_line"), row.get("combined_exact_line"))


def validate_all_bound_evidence(
    root: Path,
    source_repository_root: Path,
    bindings: dict[str, Any],
    control_path: Path,
    control_results: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> dict[str, Any]:
    if set(bindings) != REQUIRED_EVIDENCE_LABELS:
        raise VerificationError(
            "evidence-binding label-set mismatch: "
            f"missing={sorted(REQUIRED_EVIDENCE_LABELS-set(bindings))!r} "
            f"extra={sorted(set(bindings)-REQUIRED_EVIDENCE_LABELS)!r}"
        )
    bound_relatives = [
        require_string(require_mapping(bindings[label], f"evidence binding {label}").get("path"), f"{label}.path")
        for label in sorted(REQUIRED_EVIDENCE_LABELS)
    ]
    if len(bound_relatives) != len(set(bound_relatives)):
        raise VerificationError("evidence labels must bind six distinct files")
    build = validate_final_build_evidence(
        root, source_repository_root, bindings, max_path_bytes, audit
    )
    validate_signature_evidence(
        root, source_repository_root, bindings, build, max_path_bytes, audit
    )
    validate_forbidden_evidence(root, bindings, max_path_bytes, audit)
    validate_negative_evidence(
        root, bindings, control_path, control_results, max_path_bytes, audit
    )
    validate_predecessor_evidence(root, bindings, max_path_bytes, audit)
    return build


def scan_tar(path: Path, commit: str, limits: dict[str, int]) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    _, archive_size = hash_regular(path)
    if archive_size > limits["max_archive_bytes"]:
        raise VerificationError("archive exceeds configured compressed-size limit")
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    folded: set[str] = set()
    kinds: dict[str, str] = {}
    total = 0
    with tarfile.open(path, "r:gz") as archive:
        for member in archive:
            if len(records) >= limits["max_members"]:
                raise VerificationError("archive member-count limit exceeded")
            raw_name = member.name.rstrip("/")
            name = canonical_relative(raw_name, "archive member", limits["max_path_bytes"])
            if name != ARCHIVE_ROOT and not name.startswith(ARCHIVE_ROOT + "/"):
                raise VerificationError(f"archive member is outside exact root {ARCHIVE_ROOT!r}: {name!r}")
            if name in seen or name.casefold() in folded:
                raise VerificationError(f"duplicate/case-fold-colliding archive member: {name!r}")
            if member.issym() or member.islnk() or not (member.isdir() or member.isreg()):
                raise VerificationError(f"archive links and special members are forbidden: {name!r}")
            if member.linkname or "linkpath" in member.pax_headers or getattr(member, "sparse", None):
                raise VerificationError(f"archive member has link/sparse metadata: {name!r}")
            unexpected_pax = set(member.pax_headers) - {"comment"}
            if unexpected_pax:
                raise VerificationError(f"archive member has unexpected PAX metadata: {name!r}")
            if "comment" in member.pax_headers and member.pax_headers["comment"] != commit:
                raise VerificationError(f"archive PAX commit does not match frozen commit: {name!r}")
            if member.mode & 0o7000:
                raise VerificationError(f"archive member has special permission bits: {name!r}")
            if member.isdir() and member.size != 0:
                raise VerificationError(f"archive directory has nonzero size: {name!r}")
            if member.isreg():
                if member.size < 0 or member.size > limits["max_file_bytes"]:
                    raise VerificationError(f"archive file-size limit exceeded: {name!r}")
                total += member.size
                if total > limits["max_total_bytes"]:
                    raise VerificationError("archive expanded-size limit exceeded")
            parent = PurePosixPath(name).parent
            while parent.as_posix() not in {"", "."}:
                if kinds.get(parent.as_posix()) == "file":
                    raise VerificationError(f"archive path is nested beneath a file: {name!r}")
                parent = parent.parent
            record = {
                "name": name,
                "kind": "directory" if member.isdir() else "file",
                "size": member.size,
                "mode": member.mode & 0o777,
            }
            records.append(record)
            kinds[name] = record["kind"]
            seen.add(name)
            folded.add(name.casefold())
    prefixes = tuple(f"{ARCHIVE_ROOT}/{root}" for root in SELECTED_ROOTS)
    for row in records:
        if row["kind"] == "file" and not any(
            row["name"] == prefix or row["name"].startswith(prefix + "/") for prefix in prefixes
        ):
            raise VerificationError(f"archive file outside selected roots: {row['name']!r}")
    return records, {
        "member_count": len(records),
        "regular_file_count": sum(row["kind"] == "file" for row in records),
        "expanded_regular_bytes": total,
        "links_or_special_entries": 0,
    }


def extract_scanned(path: Path, records: list[dict[str, Any]], destination: Path) -> None:
    destination.mkdir(mode=0o700)
    expected = {row["name"]: row for row in records}
    with tarfile.open(path, "r:gz") as archive:
        for member in archive:
            name = member.name.rstrip("/")
            if name not in expected:
                raise VerificationError(f"archive changed between scan and extraction: {name!r}")
            row = expected[name]
            current_kind = "directory" if member.isdir() else "file" if member.isreg() else "forbidden"
            if (
                current_kind != row["kind"]
                or member.size != row["size"]
                or (member.mode & 0o777) != row["mode"]
                or member.issym()
                or member.islnk()
                or member.linkname
                or "linkpath" in member.pax_headers
                or getattr(member, "sparse", None)
            ):
                raise VerificationError(f"archive metadata changed after the safety scan: {name!r}")
            target = destination.joinpath(*PurePosixPath(name).parts)
            lexical = Path(os.path.abspath(target))
            if os.path.commonpath([str(destination), str(lexical)]) != str(destination):
                raise VerificationError(f"extraction path escaped destination: {name!r}")
            if row["kind"] == "directory":
                target.mkdir(mode=0o700, parents=True, exist_ok=True)
                if target.is_symlink() or not target.is_dir():
                    raise VerificationError(f"cannot create safe archive directory: {name!r}")
            else:
                target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                source = archive.extractfile(member)
                if source is None:
                    raise VerificationError(f"cannot read archive file: {name!r}")
                try:
                    with target.open("xb") as output:
                        shutil.copyfileobj(source, output, length=1024 * 1024)
                finally:
                    source.close()
                os.chmod(target, 0o700 if row["mode"] & 0o111 else 0o600)


def enumerate_extracted(root: Path, max_path_bytes: int) -> dict[str, Path]:
    result: dict[str, Path] = {}
    folded: set[str] = set()
    stack = [root]
    while stack:
        directory = stack.pop()
        entries = sorted(os.scandir(directory), key=lambda entry: entry.name.encode("utf-8"), reverse=True)
        for entry in entries:
            path = Path(entry.path)
            metadata = entry.stat(follow_symlinks=False)
            relative = path.relative_to(root).as_posix()
            canonical_relative(relative, "extracted path", max_path_bytes)
            if stat.S_ISLNK(metadata.st_mode):
                raise VerificationError(f"symlink in extracted tree: {relative}")
            if stat.S_ISDIR(metadata.st_mode):
                stack.append(path)
            elif stat.S_ISREG(metadata.st_mode):
                if relative in result or relative.casefold() in folded:
                    raise VerificationError(f"duplicate/case-fold extracted file: {relative}")
                result[relative] = path
                folded.add(relative.casefold())
            else:
                raise VerificationError(f"special file in extracted tree: {relative}")
    return dict(sorted(result.items(), key=lambda item: item[0].encode("utf-8")))


def is_under_selected(path: str) -> bool:
    return any(path == root or path.startswith(root + "/") for root in SELECTED_ROOTS)


def parse_internal_manifest(path: Path, max_path_bytes: int) -> dict[str, str]:
    rows: dict[str, str] = {}
    folded: set[str] = set()
    try:
        lines = path.read_text(encoding="utf-8", errors="strict").splitlines()
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot read internal manifest: {error}") from error
    for number, line in enumerate(lines, 1):
        match = MANIFEST_LINE.fullmatch(line)
        if match is None:
            raise VerificationError(f"malformed internal manifest line {number}")
        digest, relative = match.groups()
        canonical_relative(relative, f"internal manifest line {number}", max_path_bytes)
        if not is_under_selected(relative) or relative == FINAL_MANIFEST:
            raise VerificationError(f"internal manifest path is outside payload: {relative!r}")
        if relative in rows or relative.casefold() in folded:
            raise VerificationError(f"duplicate/case-fold internal manifest path: {relative!r}")
        rows[relative] = digest
        folded.add(relative.casefold())
    if not rows:
        raise VerificationError("internal manifest is empty")
    return rows


def parse_delivery_manifest(path: Path) -> dict[str, str]:
    rows: dict[str, str] = {}
    for number, line in enumerate(path.read_text(encoding="utf-8", errors="strict").splitlines(), 1):
        match = MANIFEST_LINE.fullmatch(line)
        if match is None:
            raise VerificationError(f"malformed delivery manifest line {number}")
        digest, name = match.groups()
        if SAFE_BASENAME.fullmatch(name) is None or name in rows or name.casefold() in {item.casefold() for item in rows}:
            raise VerificationError(f"unsafe/duplicate delivery manifest name: {name!r}")
        rows[name] = digest
    return rows


def parse_ls_tree(raw: bytes, max_path_bytes: int) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    folded: set[str] = set()
    for record in raw.split(b"\0"):
        if not record:
            continue
        try:
            header, raw_path = record.split(b"\t", 1)
            mode, kind, object_id = header.decode("ascii", errors="strict").split(" ")
            path = raw_path.decode("utf-8", errors="strict")
        except (ValueError, UnicodeError) as error:
            raise VerificationError(f"malformed git ls-tree record: {record!r}") from error
        canonical_relative(path, "Git tree path", max_path_bytes)
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise VerificationError(f"Git tree has nonregular or unsupported mode: {mode} {kind} {path}")
        if path in result or path.casefold() in folded:
            raise VerificationError(f"duplicate/case-fold Git tree path: {path}")
        result[path] = {"mode": mode, "object": object_id}
        folded.add(path.casefold())
    return result


def hash_git_blobs(
    repo: Path,
    rows: dict[str, dict[str, str]],
    timeout: int,
    max_file_bytes: int,
    max_total_bytes: int,
    audit: Audit,
) -> dict[str, str]:
    argv = ["git", "-C", str(repo), "cat-file", "--batch"]
    started = utc_now()
    before = time.monotonic()
    try:
        process = subprocess.Popen(
            argv,
            cwd=repo,
            env=clean_git_environment(),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as error:
        raise VerificationError(f"cannot start git cat-file batch: {error}") from error
    if process.stdin is None or process.stdout is None or process.stderr is None:
        process.kill()
        raise VerificationError("git cat-file pipes were not created")
    hashes: dict[str, str] = {}
    total_bytes = 0
    try:
        for path, row in rows.items():
            process.stdin.write((row["object"] + "\n").encode("ascii"))
            process.stdin.flush()
            header = process.stdout.readline()
            parts = header.rstrip(b"\n").split(b" ")
            if len(parts) != 3 or parts[1] != b"blob":
                raise VerificationError(f"unexpected git cat-file header for {path}: {header!r}")
            size = int(parts[2])
            if size < 0 or size > max_file_bytes:
                raise VerificationError(f"Git blob exceeds the per-file limit for {path}: {size}")
            total_bytes += size
            if total_bytes > max_total_bytes:
                raise VerificationError("Git blobs exceed the configured total-byte limit")
            digest = hashlib.sha256()
            remaining = size
            while remaining:
                block = process.stdout.read(min(1024 * 1024, remaining))
                if not block:
                    raise VerificationError(f"truncated git blob for {path}")
                digest.update(block)
                remaining -= len(block)
            if process.stdout.read(1) != b"\n":
                raise VerificationError(f"malformed git cat-file delimiter for {path}")
            hashes[path] = digest.hexdigest()
        process.stdin.close()
        return_code = process.wait(timeout=timeout)
        stderr = process.stderr.read()
    except Exception:
        process.kill()
        process.wait()
        raise
    audit.commands.append(
        {
            "label": "git_cat_file_batch",
            "argv": argv,
            "cwd": str(repo),
            "started_utc": started,
            "elapsed_seconds": time.monotonic() - before,
            "exit_code": return_code,
            "blob_count": len(hashes),
            "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
            "stderr_bytes": len(stderr),
        }
    )
    if return_code != 0:
        raise VerificationError(f"git cat-file batch failed ({return_code}): {stderr.decode('utf-8','replace')[-4000:]}")
    return hashes


def perform(spec_path: Path) -> dict[str, Any]:
    spec_hash, spec_size = hash_regular(spec_path)
    spec = require_mapping(read_json_strict(spec_path), "verification specification")
    exact_keys(
        spec,
        {
            "schema",
            "delivery",
            "repository",
            "selected_roots",
            "internal_manifest",
            "negative_controls",
            "evidence_bindings",
            "qualifying_build",
            "limits",
            "verification_scope",
        },
        "verification specification",
    )
    if spec["schema"] != SPEC_SCHEMA:
        raise VerificationError(f"unsupported specification schema: {spec['schema']!r}")
    if spec["selected_roots"] != list(SELECTED_ROOTS):
        raise VerificationError("selected-root contract mismatch")
    limits = parse_limits(spec["limits"])
    scope = require_mapping(spec["verification_scope"], "verification_scope")
    exact_keys(scope, {"fresh_lean_execution_expected", "kernel_proof_replay_expected", "external_review_expected"}, "verification_scope")
    if scope != {
        "fresh_lean_execution_expected": False,
        "kernel_proof_replay_expected": False,
        "external_review_expected": "PENDING",
    }:
        raise VerificationError("verification scope must explicitly disclaim fresh Lean/kernel replay")

    delivery = require_mapping(spec["delivery"], "delivery")
    exact_keys(
        delivery,
        {
            "archive_path",
            "archive_sha256",
            "archive_size_bytes",
            "bundle_path",
            "bundle_sha256",
            "bundle_size_bytes",
            "receipt_path",
            "receipt_sha256",
            "receipt_size_bytes",
            "delivery_manifest_path",
            "verification_output_directory",
            "archive_root",
        },
        "delivery",
    )
    archive, expected_archive_hash, expected_archive_size = parse_artifact(
        {
            "archive_path": delivery["archive_path"],
            "archive_sha256": delivery["archive_sha256"],
            "archive_size_bytes": delivery["archive_size_bytes"],
        },
        "archive",
    )
    bundle, expected_bundle_hash, expected_bundle_size = parse_artifact(
        {
            "bundle_path": delivery["bundle_path"],
            "bundle_sha256": delivery["bundle_sha256"],
            "bundle_size_bytes": delivery["bundle_size_bytes"],
        },
        "bundle",
    )
    receipt_path, expected_receipt_hash, expected_receipt_size = parse_artifact(
        {
            "receipt_path": delivery["receipt_path"],
            "receipt_sha256": delivery["receipt_sha256"],
            "receipt_size_bytes": delivery["receipt_size_bytes"],
        },
        "receipt",
    )
    delivery_manifest = regular_file(Path(require_string(delivery["delivery_manifest_path"], "delivery manifest path")), "delivery manifest")
    output = new_directory(Path(require_string(delivery["verification_output_directory"], "verification output directory")), "verification output directory")
    if delivery["archive_root"] != ARCHIVE_ROOT:
        raise VerificationError("archive-root contract mismatch")
    parents = {archive.parent, bundle.parent, receipt_path.parent, delivery_manifest.parent, spec_path.parent}
    if len(parents) != 1:
        raise VerificationError("all delivery files and the specification must share one canonical directory")

    audit = Audit()
    for label, path, expected_hash, expected_size in (
        ("archive", archive, expected_archive_hash, expected_archive_size),
        ("bundle", bundle, expected_bundle_hash, expected_bundle_size),
        ("receipt", receipt_path, expected_receipt_hash, expected_receipt_size),
    ):
        digest, size = hash_regular(path)
        audit.require(f"outer_{label}_sha256", digest == expected_hash, digest, expected_hash)
        audit.require(f"outer_{label}_size", size == expected_size, size, expected_size)
    manifest_rows = parse_delivery_manifest(delivery_manifest)
    expected_delivery_rows = {
        archive.name: expected_archive_hash,
        bundle.name: expected_bundle_hash,
        receipt_path.name: expected_receipt_hash,
        spec_path.name: spec_hash,
    }
    audit.require("delivery_manifest_exact_entries", manifest_rows == expected_delivery_rows, manifest_rows, expected_delivery_rows)

    repository = require_mapping(spec["repository"], "repository")
    exact_keys(
        repository,
        {
            "source_repository_root",
            "commit",
            "branch",
            "final_tag",
            "final_tag_object",
            "predecessor_tag",
            "predecessor_tag_object",
            "predecessor_commit",
            "predecessor_immutable_objects",
        },
        "repository",
    )
    commit = require_string(repository["commit"], "repository.commit")
    source_repository_root = Path(
        require_string(repository["source_repository_root"], "repository.source_repository_root")
    )
    if (
        not source_repository_root.is_absolute()
        or Path(os.path.abspath(source_repository_root)) != source_repository_root
    ):
        raise VerificationError("repository.source_repository_root must be a lexical canonical absolute path")
    final_object = require_string(repository["final_tag_object"], "repository.final_tag_object")
    if HEX40.fullmatch(commit) is None or HEX40.fullmatch(final_object) is None:
        raise VerificationError("commit and final tag object must be full lowercase 40-hex IDs")
    branch = safe_ref(repository["branch"], "branch")
    final_tag = safe_ref(repository["final_tag"], "final tag")
    if (
        repository["predecessor_tag"] != PREDECESSOR_TAG
        or repository["predecessor_tag_object"] != PREDECESSOR_TAG_OBJECT
        or repository["predecessor_commit"] != PREDECESSOR_COMMIT
    ):
        raise VerificationError("Experiment 002 predecessor contract mismatch")
    immutable_objects = require_mapping(
        repository["predecessor_immutable_objects"], "repository.predecessor_immutable_objects"
    )
    if set(immutable_objects) != set(PREDECESSOR_IMMUTABLE_PATHS):
        raise VerificationError("predecessor immutable-path set mismatch")
    if any(not isinstance(value, str) or not value for value in immutable_objects.values()):
        raise VerificationError("predecessor immutable object IDs must be nonempty strings")

    records, tar_summary = scan_tar(archive, commit, limits)
    output.mkdir(mode=0o700)
    try:
        extracted_parent = output / "extracted"
        extract_scanned(archive, records, extracted_parent)
        extracted_root = canonical_directory(extracted_parent / ARCHIVE_ROOT, "fresh archive root")
        extracted_files = enumerate_extracted(extracted_root, limits["max_path_bytes"])
        if any(not is_under_selected(path) for path in extracted_files):
            raise VerificationError("fresh archive contains a regular file outside selected roots")
        internal_spec = require_mapping(spec["internal_manifest"], "internal_manifest")
        exact_keys(internal_spec, {"path", "sha256", "size_bytes", "entries", "selected_roots"}, "internal_manifest")
        if internal_spec["path"] != FINAL_MANIFEST or internal_spec["selected_roots"] != list(SELECTED_ROOTS):
            raise VerificationError("internal-manifest path/root contract mismatch")
        internal_path = regular_file(extracted_root / FINAL_MANIFEST, "fresh internal manifest")
        internal_hash, internal_size = hash_regular(internal_path)
        audit.require("internal_manifest_sha256", internal_hash == internal_spec["sha256"], internal_hash, internal_spec["sha256"])
        audit.require("internal_manifest_size", internal_size == internal_spec["size_bytes"], internal_size, internal_spec["size_bytes"])
        internal_rows = parse_internal_manifest(internal_path, limits["max_path_bytes"])
        audit.require("internal_manifest_entries", len(internal_rows) == internal_spec["entries"], len(internal_rows), internal_spec["entries"])
        audit.require(
            "internal_manifest_exact_file_set",
            set(extracted_files) == set(internal_rows) | {FINAL_MANIFEST},
            sorted(extracted_files),
            sorted(set(internal_rows) | {FINAL_MANIFEST}),
        )
        for relative, expected_hash in internal_rows.items():
            observed_hash, _ = hash_regular(extracted_files[relative])
            audit.require(f"manifest:{relative}", observed_hash == expected_hash, observed_hash, expected_hash)

        control_spec = require_mapping(spec["negative_controls"], "negative_controls")
        exact_keys(
            control_spec,
            {
                "path",
                "sha256",
                "size_bytes",
                "schema",
                "status",
                "case_ids",
                "unique_case_count",
                "lean_process_invocation_count",
                "lean_child_exit_code",
                "classification",
            },
            "negative_controls",
        )
        control_relative = canonical_relative(require_string(control_spec["path"], "negative-control path"), "negative-control path", limits["max_path_bytes"])
        control_path = regular_file(extracted_root / control_relative, "fresh negative-control results")
        control_hash, control_size = hash_regular(control_path)
        audit.require("negative_control_hash", control_hash == control_spec["sha256"], control_hash, control_spec["sha256"])
        audit.require("negative_control_size", control_size == control_spec["size_bytes"], control_size, control_spec["size_bytes"])
        control_results = require_mapping(
            read_json_strict(control_path), "negative-control results"
        )
        validate_control_result(control_path, control_spec, source_repository_root, audit)

        evidence = require_mapping(spec["evidence_bindings"], "evidence_bindings")
        build_evidence = validate_all_bound_evidence(
            extracted_root,
            source_repository_root,
            evidence,
            control_path,
            control_results,
            limits["max_path_bytes"],
            audit,
        )
        qualifying_build = require_mapping(spec["qualifying_build"], "qualifying_build")
        expected_qualifying_build = {
            "argv": build_evidence["argv"],
            "cwd": build_evidence["cwd"],
            "exit_code": 0,
            "log_sha256": build_evidence["log_sha256"],
            "log_size_bytes": build_evidence["log_size_bytes"],
            "target": FINAL_BUILD_TARGET,
            "root_default_build_covered": False,
            "root_import_file_unchanged_from_predecessor": True,
        }
        audit.require(
            "qualifying_build_contract",
            qualifying_build == expected_qualifying_build,
            qualifying_build,
            expected_qualifying_build,
        )

        receipt = require_mapping(read_json_strict(receipt_path), "remote delivery receipt")
        audit.require("receipt_schema", receipt.get("schema") == RECEIPT_SCHEMA, receipt.get("schema"), RECEIPT_SCHEMA)
        audit.require("receipt_status", receipt.get("status") == "PASS", receipt.get("status"), "PASS")
        audit.require("receipt_repository", receipt.get("repository") == repository, receipt.get("repository"), repository)
        audit.require("receipt_selected_roots", receipt.get("selected_roots") == list(SELECTED_ROOTS), receipt.get("selected_roots"), list(SELECTED_ROOTS))
        audit.require("receipt_internal_manifest", receipt.get("internal_manifest") == internal_spec, receipt.get("internal_manifest"), internal_spec)
        audit.require("receipt_negative_controls", receipt.get("negative_controls") == control_spec, receipt.get("negative_controls"), control_spec)
        audit.require("receipt_evidence_bindings", receipt.get("evidence_bindings") == evidence, receipt.get("evidence_bindings"), evidence)
        audit.require("receipt_qualifying_build", receipt.get("qualifying_build") == qualifying_build, receipt.get("qualifying_build"), qualifying_build)
        assurance_scope = require_mapping(receipt.get("assurance_scope"), "receipt assurance_scope")
        audit.require("receipt_preserved_evidence", assurance_scope.get("preserved_lean_execution_evidence_bound") is True, assurance_scope.get("preserved_lean_execution_evidence_bound"), True)
        audit.require("receipt_no_fresh_lean", assurance_scope.get("fresh_lean_execution_performed") is False, assurance_scope.get("fresh_lean_execution_performed"), False)
        audit.require("receipt_no_kernel_replay", assurance_scope.get("kernel_proof_replay_performed") is False, assurance_scope.get("kernel_proof_replay_performed"), False)
        audit.require("receipt_external_review_pending", assurance_scope.get("external_review") == "PENDING", assurance_scope.get("external_review"), "PENDING")
        receipt_artifacts = require_mapping(receipt.get("artifacts"), "receipt artifacts")
        for label, path, digest, size in (
            ("archive", archive, expected_archive_hash, expected_archive_size),
            ("bundle", bundle, expected_bundle_hash, expected_bundle_size),
        ):
            artifact = require_mapping(receipt_artifacts.get(label), f"receipt artifact {label}")
            audit.require(f"receipt_{label}_path", artifact.get("path") == str(path), artifact.get("path"), str(path))
            audit.require(f"receipt_{label}_hash", artifact.get("sha256") == digest, artifact.get("sha256"), digest)
            audit.require(f"receipt_{label}_size", artifact.get("size_bytes") == size, artifact.get("size_bytes"), size)
            if label == "archive":
                audit.require(
                    "receipt_archive_safe_tar_audit",
                    artifact.get("safe_tar_audit") == tar_summary,
                    artifact.get("safe_tar_audit"),
                    tar_summary,
                )

        bare = output / "bundle_verify.git"
        clone = output / "bundle_clone.git"
        audit.run(["git", "init", "--bare", "--template=", str(bare)], output, "git_init_bare", limits["command_timeout_seconds"])
        audit.run(["git", "-C", str(bare), "bundle", "verify", str(bundle)], output, "git_bundle_verify", limits["command_timeout_seconds"])
        heads_text = audit.text(["git", "bundle", "list-heads", str(bundle)], output, "git_bundle_heads", limits["command_timeout_seconds"])
        heads: dict[str, str] = {}
        for line in heads_text.splitlines():
            object_id, ref = line.split(" ", 1)
            if ref in heads:
                raise VerificationError(f"duplicate bundle head: {ref}")
            heads[ref] = object_id
        expected_heads = {
            f"refs/heads/{branch}": commit,
            f"refs/tags/{final_tag}": final_object,
            f"refs/tags/{PREDECESSOR_TAG}": PREDECESSOR_TAG_OBJECT,
        }
        audit.require("bundle_exact_heads", heads == expected_heads, heads, expected_heads)
        audit.run(["git", "clone", "--bare", "--template=", str(bundle), str(clone)], output, "git_clone_bundle", limits["command_timeout_seconds"])
        audit.run(["git", "-C", str(clone), "fsck", "--full", "--strict", "--no-dangling"], output, "git_fsck", limits["command_timeout_seconds"])
        observed_branch = audit.text(["git", "-C", str(clone), "rev-parse", f"refs/heads/{branch}^{{commit}}"], output, "git_branch", limits["command_timeout_seconds"])
        observed_tag_object = audit.text(["git", "-C", str(clone), "rev-parse", f"refs/tags/{final_tag}"], output, "git_final_tag_object", limits["command_timeout_seconds"])
        observed_tag_type = audit.text(["git", "-C", str(clone), "cat-file", "-t", f"refs/tags/{final_tag}"], output, "git_final_tag_type", limits["command_timeout_seconds"])
        observed_tag_commit = audit.text(["git", "-C", str(clone), "rev-parse", f"refs/tags/{final_tag}^{{commit}}"], output, "git_final_tag_commit", limits["command_timeout_seconds"])
        observed_prev_object = audit.text(["git", "-C", str(clone), "rev-parse", f"refs/tags/{PREDECESSOR_TAG}"], output, "git_predecessor_tag_object", limits["command_timeout_seconds"])
        observed_prev_type = audit.text(["git", "-C", str(clone), "cat-file", "-t", f"refs/tags/{PREDECESSOR_TAG}"], output, "git_predecessor_tag_type", limits["command_timeout_seconds"])
        observed_prev_commit = audit.text(["git", "-C", str(clone), "rev-parse", f"refs/tags/{PREDECESSOR_TAG}^{{commit}}"], output, "git_predecessor_tag_commit", limits["command_timeout_seconds"])
        audit.require("git_branch_commit", observed_branch == commit, observed_branch, commit)
        audit.require("git_final_tag_object", observed_tag_object == final_object, observed_tag_object, final_object)
        audit.require("git_final_tag_type", observed_tag_type == "tag", observed_tag_type, "tag")
        audit.require("git_final_tag_commit", observed_tag_commit == commit, observed_tag_commit, commit)
        audit.require("git_predecessor_tag_object", observed_prev_object == PREDECESSOR_TAG_OBJECT, observed_prev_object, PREDECESSOR_TAG_OBJECT)
        audit.require("git_predecessor_tag_type", observed_prev_type == "tag", observed_prev_type, "tag")
        audit.require("git_predecessor_tag_commit", observed_prev_commit == PREDECESSOR_COMMIT, observed_prev_commit, PREDECESSOR_COMMIT)
        for index, path in enumerate(PREDECESSOR_IMMUTABLE_PATHS):
            at_predecessor = audit.text(
                ["git", "-C", str(clone), "rev-parse", f"{PREDECESSOR_COMMIT}:{path}"],
                output,
                f"git_predecessor_object_{index}",
                limits["command_timeout_seconds"],
            )
            at_final = audit.text(
                ["git", "-C", str(clone), "rev-parse", f"{commit}:{path}"],
                output,
                f"git_final_object_{index}",
                limits["command_timeout_seconds"],
            )
            audit.require(
                f"predecessor_immutable:{path}",
                at_predecessor == at_final == immutable_objects[path],
                {"predecessor": at_predecessor, "final": at_final},
                immutable_objects[path],
            )
        raw_tree = audit.run(
            ["git", "-C", str(clone), "ls-tree", "-rz", "-r", "--full-tree", commit, "--", *SELECTED_ROOTS],
            output,
            "git_selected_tree",
            limits["command_timeout_seconds"],
        )
        tree = parse_ls_tree(raw_tree, limits["max_path_bytes"])
        audit.require("git_tree_exact_file_set", set(tree) == set(extracted_files), sorted(tree), sorted(extracted_files))
        blob_hashes = hash_git_blobs(
            clone,
            tree,
            limits["command_timeout_seconds"],
            limits["max_file_bytes"],
            limits["max_total_bytes"],
            audit,
        )
        tar_modes = {
            row["name"].removeprefix(ARCHIVE_ROOT + "/"): row["mode"]
            for row in records
            if row["kind"] == "file"
        }
        for relative, row in tree.items():
            extracted_hash, _ = hash_regular(extracted_files[relative])
            audit.require(f"git_blob:{relative}", blob_hashes[relative] == extracted_hash, blob_hashes[relative], extracted_hash)
            expected_executable = row["mode"] == "100755"
            observed_executable = bool(tar_modes[relative] & 0o111)
            audit.require(f"git_mode:{relative}", observed_executable == expected_executable, observed_executable, expected_executable)

        final_hashes = {
            "archive": hash_regular(archive)[0],
            "bundle": hash_regular(bundle)[0],
            "receipt": hash_regular(receipt_path)[0],
            "spec": hash_regular(spec_path)[0],
            "delivery_manifest": hash_regular(delivery_manifest)[0],
        }
        audit.require("archive_stable", final_hashes["archive"] == expected_archive_hash, final_hashes["archive"], expected_archive_hash)
        audit.require("bundle_stable", final_hashes["bundle"] == expected_bundle_hash, final_hashes["bundle"], expected_bundle_hash)
        audit.require("receipt_stable", final_hashes["receipt"] == expected_receipt_hash, final_hashes["receipt"], expected_receipt_hash)
        audit.require("spec_stable", final_hashes["spec"] == spec_hash, final_hashes["spec"], spec_hash)
        local_receipt = {
            "schema": LOCAL_RECEIPT_SCHEMA,
            "status": "PASS",
            "verified_utc": utc_now(),
            "spec": {"path": str(spec_path), "sha256": spec_hash, "size_bytes": spec_size},
            "delivery": {
                "archive": {"path": str(archive), "sha256": expected_archive_hash, "size_bytes": expected_archive_size},
                "bundle": {"path": str(bundle), "sha256": expected_bundle_hash, "size_bytes": expected_bundle_size},
                "receipt": {"path": str(receipt_path), "sha256": expected_receipt_hash, "size_bytes": expected_receipt_size},
                "delivery_manifest": {"path": str(delivery_manifest), "sha256": final_hashes["delivery_manifest"]},
            },
            "repository": repository,
            "safe_extraction": tar_summary,
            "internal_manifest": internal_spec,
            "qualifying_build": qualifying_build,
            "negative_controls": {
                "status": "PASS",
                "unique_case_count": 2,
                "lean_process_invocation_count": 1,
                "case_ids": list(EXPECTED_CONTROL_CASES),
                "classification": EXPECTED_CONTROL_REASON,
            },
            "evidence_bindings": evidence,
            "checks": audit.checks,
            "commands": audit.commands,
            "assurance_scope": {
                "preserved_lean_execution_evidence_verified": True,
                "fresh_lean_execution_performed": False,
                "kernel_proof_replay_performed": False,
                "external_review": "PENDING",
                "statement": (
                    "This is a fresh byte/tree/evidence verification, not a fresh Lean "
                    "execution or kernel proof replay."
                ),
            },
        }
        receipt_out = output / "local_final_delivery_verification.json"
        write_exclusive(receipt_out, json_bytes(local_receipt))
        receipt_out_hash, receipt_out_size = hash_regular(receipt_out)
        return {
            "status": "PASS",
            "output_directory": str(output),
            "local_receipt": str(receipt_out),
            "local_receipt_sha256": receipt_out_hash,
            "local_receipt_size_bytes": receipt_out_size,
            "check_count": len(audit.checks),
            "command_count": len(audit.commands),
            "fresh_lean_execution_performed": False,
            "kernel_proof_replay_performed": False,
            "external_review": "PENDING",
        }
    except Exception as error:
        failure = output / "VERIFICATION_FAILED.json"
        if not failure.exists():
            try:
                write_exclusive(
                    failure,
                    json_bytes(
                        {
                            "schema": "ndea.exp003.step1.local_delivery_verification_failure.v1",
                            "status": "FAIL",
                            "timestamp_utc": utc_now(),
                            "spec_path": str(spec_path),
                            "spec_sha256": spec_hash,
                            "error_type": type(error).__name__,
                            "error": str(error),
                            "checks": audit.checks,
                            "commands": audit.commands,
                        }
                    ),
                )
            except Exception:
                pass
        raise


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spec", required=True, help="absolute path to the generated delivery specification")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        spec_path = regular_file(Path(args.spec), "delivery specification")
        outcome = perform(spec_path)
    except Exception as error:
        print(
            f"EXP003_STEP1_LOCAL_VERIFICATION_STATUS=FAIL\nERROR={type(error).__name__}: {error}",
            file=sys.stderr,
        )
        return 2
    print(json.dumps(outcome, indent=2, sort_keys=True))
    print("EXP003_STEP1_LOCAL_VERIFICATION_STATUS=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
