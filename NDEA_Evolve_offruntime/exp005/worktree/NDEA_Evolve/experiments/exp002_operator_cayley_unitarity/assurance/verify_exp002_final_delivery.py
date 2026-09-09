#!/usr/bin/env python3
"""Fail-closed local verifier for an Experiment 002 final delivery.

The verifier takes one independently preserved JSON specification.  That file
binds the outer delivery hashes, final Git revision/tag, internal manifest,
evidence metadata, toolchain pins, and Experiment 001 sentinels.  Verification
never imports files from the ambient Experiment 002 worktree.  Extracted Python
checks run only after the archive and bundle have been independently bound to
the frozen specification and to one another.

This program intentionally does not run Lean or Julia.  It checks the preserved
Lean evidence and replays the independent Python matrix-certificate validator.
Use --print-example-spec to print the required specification shape.
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
import traceback
import unicodedata
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any

try:
    import tomllib
except ImportError as error:  # pragma: no cover - Python >= 3.11 is expected.
    raise RuntimeError("Python 3.11 or newer is required (missing tomllib)") from error


SPEC_SCHEMA = "ndea.exp002.final_delivery_verifier_spec.v1"
RECEIPT_SCHEMA = "ndea.exp002.local_final_delivery_verification.v1"

ARCHIVE_SELECTED_PATHS = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "NDEAEvolve.lean",
    "NDEAEvolve/Basic.lean",
    "NDEAEvolve/Experiments/Exp002",
    "experiments/exp002_operator_cayley_unitarity",
)

EXP_ROOT = "experiments/exp002_operator_cayley_unitarity"
PRODUCTION_LEAN_SOURCES = (
    "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean",
    "NDEAEvolve/Experiments/Exp002/AdversarialWitnesses.lean",
)
JULIA_PATHS = {
    "validator": f"{EXP_ROOT}/validator/validate_operator_cayley.py",
    "certificate": f"{EXP_ROOT}/certificates/operator_cayley_core.json",
    "run_receipt": f"{EXP_ROOT}/metadata/operator_cayley_run_receipt.json",
    "source_root": f"{EXP_ROOT}/source/julia",
    "regression_driver": f"{EXP_ROOT}/controls/run_validator_regression.py",
    "regression_results": f"{EXP_ROOT}/logs/validator_regression_results.json",
    "regression_log": f"{EXP_ROOT}/logs/validator_regression.log",
}

HISTORICAL_MANIFESTS = (
    {
        "label": "preflight",
        "path": f"{EXP_ROOT}/PREFLIGHT_SHA256SUMS",
        "sha256": "2754c2f7e544c9e39d7cfd9a578209f75bacac1e9283cc7b58bb78d349b41667",
        "entries": 7,
    },
    {
        "label": "julia_green",
        "path": f"{EXP_ROOT}/JULIA_GREEN_SHA256SUMS",
        "sha256": "d8be6a28dff0aef12aca5fb5a699b7c461fdb4b1e4fdbad4b33d82d2145c270b",
        "entries": 68,
    },
)

REQUIRED_LEAN_ROLES = (
    "production_build",
    "positive_witness",
    "axiom_audit",
    "negative_controls",
    "forbidden_scan",
)

REQUIRED_DECLARATIONS = (
    "NDEAEvolve.Exp002.cayleyD_isUnit",
    "NDEAEvolve.Exp002.cayleyD_det_ne_zero",
    "NDEAEvolve.Exp002.cayley_unitary",
    "NDEAEvolve.Exp002.cayley_preserves_inner",
    "NDEAEvolve.Exp002.cayley_preserves_norm",
    "NDEAEvolve.Exp002.orderedCayleyProduct_unitary",
    "NDEAEvolve.Exp002.orderedCayleyProduct_preserves_inner",
    "NDEAEvolve.Exp002.orderedCayleyProduct_preserves_norm",
    "NDEAEvolve.Exp002.cayley_order_defect",
    "NDEAEvolve.Exp002.cayley_commute_iff_of_inverse_laws",
    "NDEAEvolve.Exp002.hermitian_cayley_commute_iff",
    "NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_factors_order_sensitive",
    "NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_commutator_wrong_sign",
    "NDEAEvolve.Exp002.AdversarialWitnesses.nonhermitian_cayley_not_unitary",
    "NDEAEvolve.Exp002.AdversarialWitnesses.complex_step_half_not_unitary",
    "NDEAEvolve.Exp002.AdversarialWitnesses.zero_step_breaks_commutation_iff",
    "NDEAEvolve.Exp002.AdversarialWitnesses.cayleyR_one_sided_inverse_permutation_detected",
)

AXIOM_AUDIT_SCHEMA = "ndea.exp002.axiom_audit.v1"
AXIOM_DEPENDENCY_BLOCK = re.compile(
    r"^'([^'\n]+)' depends on axioms: \[([A-Za-z0-9_.,\s]*)\]$",
    re.MULTILINE,
)
NO_AXIOM_DEPENDENCY_LINE = re.compile(
    r"^'([^'\n]+)' does not depend on any axioms$", re.MULTILINE
)
AXIOM_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")

VALID_JULIA_CASES = (
    "valid_full_absolute",
    "valid_certificate_and_source",
    "valid_certificate_only",
)

INVALID_JULIA_CASES = {
    "malformed_json": "cannot parse",
    "duplicate_top_key": "duplicate JSON key",
    "missing_top_key": "key set mismatch",
    "extra_top_key": "key set mismatch",
    "wrong_certificate_schema": "certificate.schema",
    "wrong_core_hash": "certificate.core_sha256",
    "wrong_run_id": "certificate.run_id",
    "wrong_core_schema": "core.schema",
    "weakened_assumption": "core.metadata.assumptions",
    "changed_commutator_convention": "core.metadata.conventions",
    "noncanonical_rational": "rational must be normalized",
    "zero_denominator": "noncanonical positive denominator",
    "altered_generator_entry": "exact_instances[0].D",
    "altered_inverse_entry": "D_inverse",
    "altered_unitarity_residual": "residuals.Udagger_U_minus_I",
    "swapped_composition": "composition.P21",
    "order_defect_sign": "order_defect.coefficient",
    "order_defect_residual_nonzero": "order_defect.residual",
    "remove_adversarial_case": "adversarial witness IDs/order mismatch",
    "semigroup_false_claim_zeroed": "adversarial.semigroup.C_a_plus_b",
    "wrong_order_control_zeroed": "adversarial.wrong_left.rhs",
    "search_count_forged": "search.singular_denominator",
    "symbolic_coefficient_forged": "symbolic.X",
    "source_hash_forged": "core.source.discover_operator_cayley.jl",
    "receipt_false_pass": "receipt.statuses",
    "numeric_limit_weakened": "numeric.independent_limit",
    "numeric_single_above_limit": "numeric.single_accepted",
    "numeric_product_nan": "numeric.product_finite",
    "numeric_count_forged": "numeric.counts",
    "numeric_norm_substituted": "numeric.norm",
    "receipt_certificate_hash_forged": "receipt.certificate_sha256",
}

NEGATIVE_LEAN_CASES = {
    "01_dropped_hermiticity_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/01_dropped_hermiticity_false.lean",
        "sha256": "a6c852867b4f60d096a2ca3152b9245bc89b8c119c6fa3d69c48155ed6adaa87",
        "theorem": "false_dropped_hermiticity",
        "batched_theorem": "false_dropped_hermiticity_batched",
        "witness": "nonhermitian_cayley_not_unitary",
    },
    "02_complex_step_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/02_complex_step_false.lean",
        "sha256": "cbb25c83dce30f802a6d3dcdf3e81d0b08a63d2061f72fa822759e3423a8cc98",
        "theorem": "false_complex_step_unitarity",
        "batched_theorem": "false_complex_step_unitarity_batched",
        "witness": "complex_step_half_not_unitary",
    },
    "03_order_independence_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/03_order_independence_false.lean",
        "sha256": "313cd9b2d2fc3a6e9382303d0a79dd6ba69f515ca2a22c6d3888f3eade452d94",
        "theorem": "false_order_independence",
        "batched_theorem": "false_order_independence_batched",
        "witness": "pauli_cayley_factors_order_sensitive",
    },
    "04_wrong_defect_sign_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/04_wrong_defect_sign_false.lean",
        "sha256": "e5ca2260fc1b4d28717c14ae51ec7631e9b0c8c214517eb3bae00b0d878eb24d",
        "theorem": "false_wrong_defect_sign",
        "batched_theorem": "false_wrong_defect_sign_batched",
        "witness": "pauli_cayley_commutator_wrong_sign",
    },
    "05_one_sided_inverse_permutation_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/05_one_sided_inverse_permutation_false.lean",
        "sha256": "d381fd57a494431ca248f11a786d50968f020175d89dc3b76da5e5c027ff2990",
        "theorem": "false_one_sided_inverse_permutation",
        "batched_theorem": "false_one_sided_inverse_permutation_batched",
        "witness": "cayleyR_one_sided_inverse_permutation_detected",
    },
    "06_zero_step_iff_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/06_zero_step_iff_false.lean",
        "sha256": "3c5e5ae8a9213d3d337c3fe78971d30a8bfa3723edebdccbf39e904833bd87c1",
        "theorem": "false_zero_step_commutation_equivalence",
        "batched_theorem": "false_zero_step_commutation_equivalence_batched",
        "witness": "zero_step_breaks_commutation_iff",
    },
    "07_semigroup_merging_false": {
        "source": f"{EXP_ROOT}/controls/lean/rejected_sources/07_semigroup_merging_false.lean",
        "sha256": "5f04d971605f46e22b21146513297a3434141953a5fca2df540ac06943a8eb81",
        "theorem": "false_scalar_semigroup_merging",
        "batched_theorem": "false_scalar_semigroup_merging_batched",
        "witness": "false_semigroup_merging_witness",
    },
}

NEGATIVE_CONTROL_SCHEMA = "ndea.exp002.lean_negative_controls.v3"
NEGATIVE_CONTROL_TIMEOUT_ENV = "NDEA_EXP002_NEGATIVE_CONTROL_TIMEOUT_SECONDS"
NEGATIVE_CONTROL_SUCCESS_REASON = "EXPECTED_FALSE_STATEMENT_TYPE_MISMATCH"
NEGATIVE_CONTROL_DIAGNOSTIC_CHECKS = (
    "fixture_contract_valid",
    "diagnostic_utf8",
    "exactly_seven_diagnostic_headers",
    "all_headers_are_errors",
    "no_unframed_output",
    "exactly_one_case_error",
    "intended_combined_source_line",
    "type_mismatch",
    "own_witness_present_only",
    "has_actual_and_expected_types",
    "no_import_or_infrastructure_error",
    "no_malformed_source_error",
)
NEGATIVE_BATCHED_SOURCE = f"{EXP_ROOT}/controls/lean/BatchedNegativeControls.lean"
NEGATIVE_RAW_DIAGNOSTIC = f"{EXP_ROOT}/controls/lean/rejection_diagnostics/batched_negative_controls.raw.log"
NEGATIVE_PROCESS_INVOCATION_ID = "lean-batched-negative-controls-001"
NEGATIVE_MAX_CAPTURE_BYTES = 16 * 1024 * 1024
NEGATIVE_IMPORT_LINE = "import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses"
NEGATIVE_NAMESPACE_LINE = "namespace NDEAEvolve.Exp002.NegativeControls"
NEGATIVE_OPEN_LINE = "open AdversarialWitnesses"
NEGATIVE_FIXTURE_PREAMBLE = (
    f"{NEGATIVE_IMPORT_LINE}\n\n{NEGATIVE_NAMESPACE_LINE}\n\n{NEGATIVE_OPEN_LINE}\n\n"
)
NEGATIVE_SOURCE_EPILOGUE = f"\n\nend {NEGATIVE_NAMESPACE_LINE.removeprefix('namespace ')}\n"
NEGATIVE_BATCHED_PREAMBLE = f"""{NEGATIVE_IMPORT_LINE}

/-!
Resource-bounded execution driver for the seven existing false controls.

Each theorem body and target below is the corresponding rejected fixture's
mathematical content.  Keeping all seven commands in one Lean process shares the
large `Mathlib` import while still requiring Lean to emit seven distinct errors.
This file is assurance input, never a production module.
-/

{NEGATIVE_NAMESPACE_LINE}

{NEGATIVE_OPEN_LINE}

"""
NEGATIVE_CONTROL_INFRASTRUCTURE_MARKERS = (
    "unknown module prefix",
    "unknown package",
    "object file",
    "does not exist in the search path",
    "no such file or directory",
    "failed to build",
    "build failed",
    "invalid import",
)
NEGATIVE_CONTROL_MALFORMED_MARKERS = (
    "unexpected token",
    "unexpected end of input",
    "invalid syntax",
    "invalid 'end'",
    "unterminated",
)
LEAN_ERROR_HEADER = re.compile(
    r"^.+:[0-9]+:[0-9]+:[ \t]+error:",
    re.IGNORECASE | re.MULTILINE,
)
LEAN_ANY_DIAGNOSTIC_HEADER = re.compile(
    r"^(?P<path>.+):(?P<line>[0-9]+):(?P<column>[0-9]+):[ \t]+"
    r"(?P<severity>error|warning|information):[ \t]*(?P<message>.*)$",
    re.IGNORECASE | re.MULTILINE,
)
LEAN_DIAGNOSTIC_HEADER_PREFIX = re.compile(
    r"^.+:[0-9]+:[0-9]+:[ \t]+(?:error|warning|information):[ \t]*",
    re.IGNORECASE | re.MULTILINE,
)

DEFAULT_FORBIDDEN_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
)

HEX64 = re.compile(r"[0-9a-f]{64}\Z")
GIT_OBJECT = re.compile(r"[0-9a-f]{40}(?:[0-9a-f]{24})?\Z")
MANIFEST_LINE = re.compile(r"([0-9a-f]{64})  (.+)\Z")
SAFE_REF = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/+\-]*\Z")


class VerificationError(RuntimeError):
    """A fail-closed verification error."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def reject_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number is forbidden: {value}")


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def loads_json_strict(text: str, source: str) -> Any:
    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicate_keys,
            parse_constant=reject_json_constant,
        )
    except (UnicodeError, ValueError, json.JSONDecodeError) as error:
        raise VerificationError(f"cannot parse strict JSON {source}: {error}") from error


def read_json_strict(path: Path) -> Any:
    try:
        text = path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot read UTF-8 JSON {path}: {error}") from error
    return loads_json_strict(text, str(path))


def require_mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise VerificationError(f"{label} must be a JSON object")
    return value


def require_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise VerificationError(f"{label} must be a JSON array")
    return value


def require_string(value: Any, label: str, *, nonempty: bool = True) -> str:
    if not isinstance(value, str) or (nonempty and not value):
        raise VerificationError(f"{label} must be a{' nonempty' if nonempty else ''} string")
    return value


def require_integer(value: Any, label: str, *, minimum: int = 0, maximum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise VerificationError(f"{label} must be an integer")
    if value < minimum or (maximum is not None and value > maximum):
        raise VerificationError(f"{label} outside allowed range")
    return value


def require_boolean(value: Any, label: str) -> bool:
    if type(value) is not bool:
        raise VerificationError(f"{label} must be a boolean")
    return value


def require_exact_keys(value: dict[str, Any], required: set[str], optional: set[str], label: str) -> None:
    keys = set(value)
    missing = required - keys
    extra = keys - required - optional
    if missing or extra:
        raise VerificationError(f"{label} key mismatch; missing={sorted(missing)} extra={sorted(extra)}")


def require_sha(value: Any, label: str) -> str:
    text = require_string(value, label)
    if HEX64.fullmatch(text) is None:
        raise VerificationError(f"{label} must be exactly 64 lowercase hexadecimal characters")
    return text


def require_git_object(value: Any, label: str) -> str:
    text = require_string(value, label)
    if GIT_OBJECT.fullmatch(text) is None:
        raise VerificationError(f"{label} must be a 40- or 64-character lowercase Git object ID")
    return text


def canonical_relative(value: Any, label: str, max_path_bytes: int) -> str:
    text = require_string(value, label)
    try:
        encoded = text.encode("utf-8", errors="strict")
    except UnicodeError as error:
        raise VerificationError(f"{label} is not strict UTF-8: {error}") from error
    if len(encoded) > max_path_bytes:
        raise VerificationError(f"{label} exceeds path-length limit")
    if unicodedata.normalize("NFC", text) != text:
        raise VerificationError(f"{label} is not NFC-normalized")
    if "\\" in text or any(ord(character) < 32 or ord(character) == 127 for character in text):
        raise VerificationError(f"{label} contains a backslash or control character")
    if text.startswith("/") or text.endswith("/"):
        raise VerificationError(f"{label} must be a canonical relative file path")
    raw_parts = text.split("/")
    if any(part in {"", ".", ".."} or part.strip() != part for part in raw_parts):
        raise VerificationError(f"{label} has an empty, traversal, dot, or padded component")
    if ":" in raw_parts[0]:
        raise VerificationError(f"{label} has a drive-like first component")
    pure = PurePosixPath(text)
    if pure.is_absolute() or pure.as_posix() != text:
        raise VerificationError(f"{label} is not canonical POSIX spelling")
    return text


def require_linux_posix() -> None:
    if os.name != "posix" or sys.platform != "linux":
        raise VerificationError(
            "final-delivery verification requires a POSIX Linux host"
        )


def dotted_get(value: Any, dotted: str, label: str) -> Any:
    current = value
    for part in dotted.split("."):
        if not isinstance(current, dict) or part not in current:
            raise VerificationError(f"{label} missing field {dotted!r}")
        current = current[part]
    return current


def ensure_regular_no_links(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise VerificationError(f"{label} must be an absolute path: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        resolved = path.resolve(strict=True)
        metadata = os.lstat(path)
    except OSError as error:
        raise VerificationError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical:
        raise VerificationError(f"{label} contains a symbolic-link or noncanonical component: {path}")
    if not stat.S_ISREG(metadata.st_mode):
        raise VerificationError(f"{label} is not a regular non-link file: {path}")
    return resolved


class Audit:
    def __init__(self, output: Path, command_timeout: int):
        self.output = output
        self.logs = output / "command_logs"
        self.logs.mkdir(parents=True, exist_ok=False)
        os.chmod(self.logs, 0o700)
        self.command_timeout = command_timeout
        self.checks: list[dict[str, Any]] = []
        self.commands: list[dict[str, Any]] = []

    def require(self, name: str, condition: bool, observed: Any = None, expected: Any = None) -> None:
        record = {
            "name": name,
            "pass": bool(condition),
            "observed": observed,
            "expected": expected,
        }
        self.checks.append(record)
        print(f"{'PASS' if condition else 'FAIL'} {name}")
        if not condition:
            raise VerificationError(f"check failed: {name}; observed={observed!r}; expected={expected!r}")

    def run(self, label: str, argv: list[str], cwd: Path, *, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
        if not argv or any(not isinstance(item, str) or not item for item in argv):
            raise VerificationError(f"invalid argv for {label}")
        sequence = len(self.commands) + 1
        log = self.logs / f"{sequence:03d}_{re.sub(r'[^A-Za-z0-9_.-]+', '_', label)}.json"
        started = utc_now()
        before = time.monotonic()
        environment = clean_git_environment() if argv[0] == "git" else None
        try:
            result = subprocess.run(
                argv,
                cwd=cwd,
                env=environment,
                text=True,
                encoding="utf-8",
                errors="replace",
                capture_output=True,
                timeout=timeout or self.command_timeout,
                check=False,
            )
            timed_out = False
        except subprocess.TimeoutExpired as error:
            result = subprocess.CompletedProcess(
                argv,
                124,
                error.stdout.decode("utf-8", "replace") if isinstance(error.stdout, bytes) else (error.stdout or ""),
                error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else (error.stderr or ""),
            )
            timed_out = True
        record = {
            "label": label,
            "argv": argv,
            "cwd": str(cwd),
            "started_utc": started,
            "elapsed_seconds": time.monotonic() - before,
            "exit_code": result.returncode,
            "timed_out": timed_out,
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
        log.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        command_record = {
            key: value for key, value in record.items() if key not in {"stdout", "stderr"}
        }
        command_record.update({"log": str(log), "log_sha256": sha256(log)})
        self.commands.append(command_record)
        self.require(f"command:{label}", result.returncode == 0 and not timed_out, result.returncode, 0)
        return result

    def run_bytes(self, label: str, argv: list[str], cwd: Path) -> bytes:
        sequence = len(self.commands) + 1
        safe_label = re.sub(r"[^A-Za-z0-9_.-]+", "_", label)
        stdout_path = self.logs / f"{sequence:03d}_{safe_label}.stdout.bin"
        stderr_path = self.logs / f"{sequence:03d}_{safe_label}.stderr.txt"
        started = utc_now()
        before = time.monotonic()
        try:
            result = subprocess.run(
                argv,
                cwd=cwd,
                env=clean_git_environment() if argv and argv[0] == "git" else None,
                capture_output=True,
                timeout=self.command_timeout,
                check=False,
            )
            timed_out = False
        except subprocess.TimeoutExpired as error:
            result = subprocess.CompletedProcess(argv, 124, error.stdout or b"", error.stderr or b"")
            timed_out = True
        stdout = result.stdout if isinstance(result.stdout, bytes) else str(result.stdout).encode()
        stderr = result.stderr if isinstance(result.stderr, bytes) else str(result.stderr).encode()
        stdout_path.write_bytes(stdout)
        stderr_path.write_bytes(stderr)
        self.commands.append(
            {
                "label": label,
                "argv": argv,
                "cwd": str(cwd),
                "started_utc": started,
                "elapsed_seconds": time.monotonic() - before,
                "exit_code": result.returncode,
                "timed_out": timed_out,
                "stdout": str(stdout_path),
                "stdout_sha256": sha256(stdout_path),
                "stdout_bytes": len(stdout),
                "stderr": str(stderr_path),
                "stderr_sha256": sha256(stderr_path),
            }
        )
        self.require(f"command:{label}", result.returncode == 0 and not timed_out, result.returncode, 0)
        return stdout


def validate_spec(spec: dict[str, Any]) -> None:
    require_exact_keys(
        spec,
        {
            "schema",
            "delivery",
            "repository",
            "manifest",
            "pins",
            "julia",
            "lean_evidence",
            "receipt_contract",
            "exp001",
            "limits",
        },
        set(),
        "spec",
    )
    if spec["schema"] != SPEC_SCHEMA:
        raise VerificationError(f"unsupported spec schema: {spec['schema']!r}")


def clean_git_environment() -> dict[str, str]:
    environment = os.environ.copy()
    for key in list(environment):
        if key.startswith("GIT_CONFIG_") or key in {
            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_COMMON_DIR",
            "GIT_DIR",
            "GIT_INDEX_FILE",
            "GIT_OBJECT_DIRECTORY",
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


def parse_limits(spec: dict[str, Any]) -> dict[str, int]:
    limits = require_mapping(spec["limits"], "limits")
    require_exact_keys(
        limits,
        {
            "max_archive_bytes",
            "max_members",
            "max_file_bytes",
            "max_total_bytes",
            "max_path_bytes",
            "command_timeout_seconds",
        },
        set(),
        "limits",
    )
    parsed = {
        "max_archive_bytes": require_integer(
            limits["max_archive_bytes"],
            "limits.max_archive_bytes",
            minimum=1,
            maximum=20 * 1024**3,
        ),
        "max_members": require_integer(limits["max_members"], "limits.max_members", minimum=1, maximum=100_000),
        "max_file_bytes": require_integer(limits["max_file_bytes"], "limits.max_file_bytes", minimum=1, maximum=10 * 1024**3),
        "max_total_bytes": require_integer(limits["max_total_bytes"], "limits.max_total_bytes", minimum=1, maximum=20 * 1024**3),
        "max_path_bytes": require_integer(limits["max_path_bytes"], "limits.max_path_bytes", minimum=64, maximum=16_384),
        "command_timeout_seconds": require_integer(limits["command_timeout_seconds"], "limits.command_timeout_seconds", minimum=1, maximum=3_600),
    }
    if parsed["max_file_bytes"] > parsed["max_total_bytes"]:
        raise VerificationError("limits.max_file_bytes cannot exceed limits.max_total_bytes")
    return parsed


def scan_tar(
    archive_path: Path,
    archive_root: str,
    expected_git_commit: str,
    limits: dict[str, int],
) -> list[dict[str, Any]]:
    members: list[dict[str, Any]] = []
    seen: set[str] = set()
    seen_casefold: set[str] = set()
    kinds: dict[str, str] = {}
    total_size = 0
    try:
        with tarfile.open(archive_path, "r:*") as archive:
            for member in archive:
                if len(members) >= limits["max_members"]:
                    raise VerificationError("archive member-count safety limit exceeded")
                name = canonical_relative(member.name, "archive member", limits["max_path_bytes"])
                parts = name.split("/")
                if parts[0] != archive_root:
                    raise VerificationError(f"archive member outside exact root {archive_root!r}: {name!r}")
                folded = name.casefold()
                if name in seen or folded in seen_casefold:
                    raise VerificationError(f"duplicate or case-fold-colliding archive member: {name!r}")
                if member.issym() or member.islnk() or not (member.isdir() or member.isreg()):
                    raise VerificationError(f"archive links and special entries are forbidden: {name!r}")
                if member.linkname or "linkpath" in member.pax_headers:
                    raise VerificationError(f"archive member has forbidden link metadata: {name!r}")
                unexpected_pax = set(member.pax_headers) - {"comment"}
                if unexpected_pax:
                    raise VerificationError(
                        f"archive member has unexpected PAX metadata {sorted(unexpected_pax)}: {name!r}"
                    )
                if "comment" in member.pax_headers and member.pax_headers["comment"] != expected_git_commit:
                    raise VerificationError(
                        f"archive Git PAX comment does not bind the frozen commit: {name!r}"
                    )
                if getattr(member, "sparse", None):
                    raise VerificationError(f"sparse archive member is forbidden: {name!r}")
                if member.mode & 0o7000:
                    raise VerificationError(f"archive member has special permission bits: {name!r}")
                kind = "directory" if member.isdir() else "file"
                if kind == "directory" and member.size != 0:
                    raise VerificationError(f"archive directory has nonzero declared size: {name!r}")
                if kind == "file":
                    if member.size < 0 or member.size > limits["max_file_bytes"]:
                        raise VerificationError(f"archive file-size safety limit exceeded: {name!r}")
                    total_size += member.size
                    if total_size > limits["max_total_bytes"]:
                        raise VerificationError("archive total-expanded-size safety limit exceeded")
                seen.add(name)
                seen_casefold.add(folded)
                kinds[name] = kind
                members.append(
                    {
                        "name": name,
                        "kind": kind,
                        "size": member.size,
                        "mode": member.mode,
                        "pax_headers": dict(member.pax_headers),
                    }
                )
    except (OSError, tarfile.TarError) as error:
        raise VerificationError(f"cannot scan archive {archive_path}: {error}") from error
    if not members:
        raise VerificationError("archive is empty")
    if kinds.get(archive_root) != "directory":
        raise VerificationError("archive does not contain its exact root as a directory entry")
    for name, kind in kinds.items():
        if name == archive_root:
            continue
        parts = name.split("/")
        for index in range(1, len(parts)):
            prefix = "/".join(parts[:index])
            if kinds.get(prefix) == "file":
                raise VerificationError(f"archive file/directory prefix conflict: {prefix!r} vs {name!r}")
    regular_names = {row["name"] for row in members if row["kind"] == "file"}
    expected_directories = {archive_root}
    for name in regular_names:
        parts = name.split("/")
        expected_directories.update("/".join(parts[:index]) for index in range(1, len(parts)))
    actual_directories = {row["name"] for row in members if row["kind"] == "directory"}
    if actual_directories != expected_directories:
        raise VerificationError(
            "archive directory set is not the exact ancestor closure of its files; "
            f"extra={sorted(actual_directories - expected_directories)} "
            f"missing={sorted(expected_directories - actual_directories)}"
        )
    return members


def contained(root: Path, candidate: Path) -> bool:
    try:
        return os.path.commonpath((str(root), str(candidate))) == str(root)
    except ValueError:
        return False


def extract_tar_safely(
    archive_path: Path,
    destination: Path,
    scanned: list[dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    destination.mkdir(parents=True, exist_ok=False)
    os.chmod(destination, 0o700)
    root = destination.resolve()
    extracted: dict[str, dict[str, Any]] = {}
    try:
        with tarfile.open(archive_path, "r:*") as archive:
            index = 0
            for member in archive:
                if index >= len(scanned):
                    raise VerificationError("archive changed between pre-scan and extraction")
                expected = scanned[index]
                observed = {
                    "name": member.name,
                    "kind": "directory" if member.isdir() else "file" if member.isreg() else "special",
                    "size": member.size,
                    "mode": member.mode,
                    "pax_headers": dict(member.pax_headers),
                }
                if observed != expected:
                    raise VerificationError(
                        f"archive changed between pre-scan and extraction at member {index}: {observed!r} != {expected!r}"
                    )
                index += 1
                target = destination.joinpath(*PurePosixPath(member.name).parts)
                resolved_target = target.resolve(strict=False)
                if not contained(root, resolved_target):
                    raise VerificationError(f"archive target escapes extraction root: {member.name!r}")
                if member.isdir():
                    if target.exists() and not target.is_dir():
                        raise VerificationError(f"archive directory conflicts with an existing target: {member.name!r}")
                    target.mkdir(parents=True, exist_ok=True)
                    os.chmod(target, 0o700)
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists() or target.is_symlink():
                    raise VerificationError(f"archive refuses conflicting write: {member.name!r}")
                source = archive.extractfile(member)
                if source is None:
                    raise VerificationError(f"cannot read regular archive member: {member.name!r}")
                digest = hashlib.sha256()
                count = 0
                with source, target.open("xb") as output:
                    while True:
                        block = source.read(1024 * 1024)
                        if not block:
                            break
                        count += len(block)
                        if count > member.size:
                            raise VerificationError(f"archive member exceeds declared size: {member.name!r}")
                        digest.update(block)
                        output.write(block)
                if count != member.size or target.stat().st_size != member.size:
                    raise VerificationError(f"archive extracted-size mismatch: {member.name!r}")
                os.chmod(target, 0o700 if member.mode & 0o111 else 0o600)
                extracted[member.name] = {
                    "sha256": digest.hexdigest(),
                    "size": count,
                    "mode": member.mode,
                }
            if index != len(scanned):
                raise VerificationError("archive lost members between pre-scan and extraction")
    except (OSError, tarfile.TarError) as error:
        raise VerificationError(f"cannot safely extract archive {archive_path}: {error}") from error

    for current, directory_names, file_names in os.walk(destination, topdown=True, followlinks=False):
        current_path = Path(current)
        for name in directory_names + file_names:
            path = current_path / name
            mode = os.lstat(path).st_mode
            if stat.S_ISLNK(mode) or not (stat.S_ISDIR(mode) or stat.S_ISREG(mode)):
                raise VerificationError(f"post-extraction link or special path detected: {path}")
    return extracted


def verify_manifest(
    repo: Path,
    archive_files: dict[str, dict[str, Any]],
    manifest_spec: dict[str, Any],
    max_path_bytes: int,
    audit: Audit,
) -> dict[str, Any]:
    require_exact_keys(manifest_spec, {"path", "expected_sha256", "expected_entries"}, set(), "manifest")
    relative = canonical_relative(manifest_spec["path"], "manifest.path", max_path_bytes)
    expected_hash = require_sha(manifest_spec["expected_sha256"], "manifest.expected_sha256")
    expected_entries = require_integer(manifest_spec["expected_entries"], "manifest.expected_entries", minimum=1)
    if relative not in archive_files:
        raise VerificationError(f"internal manifest is absent from archive: {relative}")
    manifest = repo / relative
    actual_hash = sha256(manifest)
    audit.require("manifest_outer_binding", actual_hash == expected_hash, actual_hash, expected_hash)
    try:
        text = manifest.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot read internal manifest: {error}") from error
    if not text.endswith("\n"):
        raise VerificationError("internal manifest must end with exactly a newline")
    entries: dict[str, str] = {}
    folded_entries: set[str] = set()
    manifest_order: list[str] = []
    for number, line in enumerate(text.splitlines(), 1):
        match = MANIFEST_LINE.fullmatch(line)
        if match is None:
            raise VerificationError(f"malformed internal manifest line {number}")
        expected, path_text = match.groups()
        path_text = canonical_relative(path_text, f"manifest line {number} path", max_path_bytes)
        if path_text == relative:
            raise VerificationError("internal manifest must not recursively list itself")
        if path_text in entries or path_text.casefold() in folded_entries:
            raise VerificationError(f"duplicate or case-fold-colliding manifest path: {path_text!r}")
        if path_text not in archive_files:
            raise VerificationError(f"manifest path is not an archived regular file: {path_text!r}")
        actual = archive_files[path_text]["sha256"]
        if actual != expected:
            raise VerificationError(
                f"internal manifest digest mismatch for {path_text!r}: actual={actual} expected={expected}"
            )
        entries[path_text] = expected
        folded_entries.add(path_text.casefold())
        manifest_order.append(path_text)
    if manifest_order != sorted(manifest_order):
        raise VerificationError("internal manifest paths are not in canonical lexicographic order")
    expected_set = set(archive_files) - {relative}
    if set(entries) != expected_set:
        raise VerificationError(
            "internal manifest coverage is not exact; "
            f"unlisted={sorted(expected_set - set(entries))} extra={sorted(set(entries) - expected_set)}"
        )
    audit.require("manifest_entry_count", len(entries) == expected_entries, len(entries), expected_entries)
    audit.require("manifest_exact_file_coverage", True, len(entries), len(expected_set))
    return {"path": relative, "sha256": actual_hash, "entries": len(entries)}


def verify_historical_manifests(
    repo: Path,
    archive_files: dict[str, dict[str, Any]],
    max_path_bytes: int,
    audit: Audit,
) -> list[dict[str, Any]]:
    """Verify the immutable preflight and Julia-green subset manifests in place."""
    records: list[dict[str, Any]] = []
    layer_root = repo / EXP_ROOT
    for contract in HISTORICAL_MANIFESTS:
        label = contract["label"]
        relative = contract["path"]
        if relative not in archive_files:
            raise VerificationError(f"historical {label} manifest absent from archive: {relative!r}")
        manifest = repo / relative
        actual_manifest_hash = sha256(manifest)
        audit.require(
            f"historical_manifest_hash:{label}",
            actual_manifest_hash == contract["sha256"],
            actual_manifest_hash,
            contract["sha256"],
        )
        try:
            text = manifest.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeError) as error:
            raise VerificationError(f"cannot read historical {label} manifest: {error}") from error
        if not text.endswith("\n"):
            raise VerificationError(f"historical {label} manifest lacks final newline")
        seen: set[str] = set()
        folded: set[str] = set()
        order: list[str] = []
        for number, line in enumerate(text.splitlines(), 1):
            match = MANIFEST_LINE.fullmatch(line)
            if match is None:
                raise VerificationError(f"malformed historical {label} manifest line {number}")
            expected, path_text = match.groups()
            path_text = canonical_relative(
                path_text,
                f"historical {label} manifest line {number} path",
                max_path_bytes,
            )
            if path_text in seen or path_text.casefold() in folded:
                raise VerificationError(
                    f"duplicate/case-fold-colliding historical {label} path: {path_text!r}"
                )
            archived_relative = f"{EXP_ROOT}/{path_text}"
            if archived_relative not in archive_files:
                raise VerificationError(
                    f"historical {label} path is absent from archive: {archived_relative!r}"
                )
            target = layer_root / path_text
            actual = sha256(target)
            if actual != expected or actual != archive_files[archived_relative]["sha256"]:
                raise VerificationError(
                    f"historical {label} digest mismatch for {path_text!r}: "
                    f"actual={actual} expected={expected}"
                )
            seen.add(path_text)
            folded.add(path_text.casefold())
            order.append(path_text)
        if order != sorted(order):
            raise VerificationError(f"historical {label} manifest is not lexicographically sorted")
        audit.require(
            f"historical_manifest_entry_count:{label}",
            len(seen) == contract["entries"],
            len(seen),
            contract["entries"],
        )
        records.append(
            {
                "label": label,
                "path": relative,
                "sha256": actual_manifest_hash,
                "entries": len(seen),
                "status": "PASS",
            }
        )
    return records


def parse_ls_tree(payload: bytes, max_path_bytes: int) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for record in payload.split(b"\0"):
        if not record:
            continue
        try:
            header, raw_path = record.split(b"\t", 1)
            mode, kind, object_id = header.decode("ascii").split(" ", 2)
            path = raw_path.decode("utf-8", errors="strict")
        except (ValueError, UnicodeError) as error:
            raise VerificationError(f"cannot parse git ls-tree record: {record!r}: {error}") from error
        path = canonical_relative(path, "git tree path", max_path_bytes)
        if path in result:
            raise VerificationError(f"duplicate git tree path: {path!r}")
        if kind != "blob" or mode not in {"100644", "100755"} or GIT_OBJECT.fullmatch(object_id) is None:
            raise VerificationError(f"forbidden Git tree entry for final archive: {record!r}")
        result[path] = {"mode": mode, "kind": kind, "object": object_id}
    return result


def git_text(audit: Audit, label: str, clone: Path, *args: str) -> str:
    return audit.run(label, ["git", "-C", str(clone), *args], cwd=audit.output).stdout.strip()


def verify_git_bundle_and_tree(
    bundle: Path,
    repo: Path,
    archive_files: dict[str, dict[str, Any]],
    repository: dict[str, Any],
    limits: dict[str, int],
    audit: Audit,
) -> tuple[Path, dict[str, Any]]:
    require_exact_keys(repository, {"commit", "tag", "tag_object", "branch"}, set(), "repository")
    commit = require_git_object(repository["commit"], "repository.commit")
    tag_object = require_git_object(repository["tag_object"], "repository.tag_object")
    tag = require_string(repository["tag"], "repository.tag")
    branch = require_string(repository["branch"], "repository.branch")
    for label, value in (("tag", tag), ("branch", branch)):
        if SAFE_REF.fullmatch(value) is None or value.startswith("-") or ".." in value or "//" in value:
            raise VerificationError(f"repository.{label} is not a restricted safe ref name")

    verification_repo = audit.output / "bundle_verify.git"
    clone = audit.output / "bundle_clone.git"
    audit.run("git_init_bare", ["git", "init", "--bare", str(verification_repo)], cwd=audit.output)
    audit.run(
        "git_bundle_verify",
        ["git", "-C", str(verification_repo), "bundle", "verify", str(bundle)],
        cwd=audit.output,
    )
    audit.run("git_clone_bare", ["git", "clone", "--bare", str(bundle), str(clone)], cwd=audit.output)
    audit.run(
        "git_fsck",
        ["git", "-C", str(clone), "fsck", "--full", "--strict", "--no-dangling"],
        cwd=audit.output,
    )

    observed_tag_object = git_text(audit, "git_resolve_final_tag_object", clone, "rev-parse", tag)
    observed_commit = git_text(audit, "git_resolve_final_tag_commit", clone, "rev-parse", f"{tag}^{{commit}}")
    tag_type = git_text(audit, "git_final_tag_type", clone, "cat-file", "-t", tag)
    branch_commit = git_text(audit, "git_resolve_final_branch", clone, "rev-parse", f"refs/heads/{branch}")
    audit.require("git_final_tag_is_annotated", tag_type == "tag", tag_type, "tag")
    audit.require("git_final_tag_object", observed_tag_object == tag_object, observed_tag_object, tag_object)
    audit.require("git_final_tag_commit", observed_commit == commit, observed_commit, commit)
    audit.require("git_final_branch_commit", branch_commit == commit, branch_commit, commit)

    tree_payload = audit.run_bytes(
        "git_ls_tree_selected",
        ["git", "-C", str(clone), "ls-tree", "-rz", "-r", "--full-tree", commit, "--", *ARCHIVE_SELECTED_PATHS],
        cwd=audit.output,
    )
    tree = parse_ls_tree(tree_payload, limits["max_path_bytes"])
    for selected in ARCHIVE_SELECTED_PATHS:
        if not any(path == selected or path.startswith(selected + "/") for path in tree):
            raise VerificationError(f"required selected Git path is absent: {selected!r}")
    if set(tree) != set(archive_files):
        raise VerificationError(
            "archive regular-file set does not equal the selected final Git tree; "
            f"archive_extra={sorted(set(archive_files) - set(tree))} "
            f"archive_missing={sorted(set(tree) - set(archive_files))}"
        )
    mismatched_bytes: list[str] = []
    mismatched_modes: list[str] = []
    for relative, entry in tree.items():
        result = subprocess.run(
            ["git", "-C", str(clone), "cat-file", "blob", entry["object"]],
            cwd=audit.output,
            env=clean_git_environment(),
            capture_output=True,
            timeout=limits["command_timeout_seconds"],
            check=False,
        )
        if result.returncode != 0:
            raise VerificationError(f"git cat-file failed for {relative!r}: {result.stderr!r}")
        if result.stdout != (repo / relative).read_bytes():
            mismatched_bytes.append(relative)
        archive_executable = bool(archive_files[relative]["mode"] & 0o111)
        git_executable = entry["mode"] == "100755"
        if archive_executable != git_executable:
            mismatched_modes.append(relative)
    audit.require("archive_bytes_equal_git_tree", not mismatched_bytes, mismatched_bytes, [])
    audit.require("archive_executable_modes_equal_git_tree", not mismatched_modes, mismatched_modes, [])
    return clone, {
        "commit": commit,
        "tag": tag,
        "tag_object": tag_object,
        "branch": branch,
        "selected_paths": list(ARCHIVE_SELECTED_PATHS),
        "tracked_files_compared": len(tree),
    }


def verify_pins(repo: Path, pins: dict[str, Any], audit: Audit) -> dict[str, str]:
    require_exact_keys(
        pins,
        {"lean_toolchain", "lean_version", "mathlib_revision", "mathlib_input_revision"},
        set(),
        "pins",
    )
    lean_toolchain = require_string(pins["lean_toolchain"], "pins.lean_toolchain")
    lean_version = require_string(pins["lean_version"], "pins.lean_version")
    mathlib_revision = require_git_object(pins["mathlib_revision"], "pins.mathlib_revision")
    mathlib_input_revision = require_string(pins["mathlib_input_revision"], "pins.mathlib_input_revision")

    toolchain_lines = (repo / "lean-toolchain").read_text(encoding="utf-8", errors="strict").splitlines()
    audit.require("lean_toolchain_pin", toolchain_lines == [lean_toolchain], toolchain_lines, [lean_toolchain])

    lake_manifest = require_mapping(read_json_strict(repo / "lake-manifest.json"), "lake-manifest.json")
    packages = require_list(lake_manifest.get("packages"), "lake-manifest.json packages")
    mathlib_rows = [row for row in packages if isinstance(row, dict) and row.get("name") == "mathlib"]
    audit.require("mathlib_manifest_unique", len(mathlib_rows) == 1, len(mathlib_rows), 1)
    audit.require(
        "mathlib_revision_pin",
        mathlib_rows[0].get("rev") == mathlib_revision,
        mathlib_rows[0].get("rev"),
        mathlib_revision,
    )
    try:
        lakefile = tomllib.loads((repo / "lakefile.toml").read_text(encoding="utf-8", errors="strict"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise VerificationError(f"cannot parse lakefile.toml: {error}") from error
    requirements = lakefile.get("require", [])
    mathlib_requires = [row for row in requirements if isinstance(row, dict) and row.get("name") == "mathlib"]
    audit.require("lakefile_mathlib_requirement_unique", len(mathlib_requires) == 1, len(mathlib_requires), 1)
    audit.require(
        "lakefile_mathlib_input_revision",
        mathlib_requires[0].get("rev") == mathlib_input_revision,
        mathlib_requires[0].get("rev"),
        mathlib_input_revision,
    )
    return {
        "lean_toolchain": lean_toolchain,
        "lean_version": lean_version,
        "mathlib_revision": mathlib_revision,
        "mathlib_input_revision": mathlib_input_revision,
    }


def clean_python_environment() -> dict[str, str]:
    environment = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PYTHONHASHSEED": "0",
        "TZ": "UTC",
    }
    return environment


def run_python(
    audit: Audit,
    label: str,
    argv: list[str],
    cwd: Path,
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    sequence = len(audit.commands) + 1
    log = audit.logs / f"{sequence:03d}_{re.sub(r'[^A-Za-z0-9_.-]+', '_', label)}.json"
    started = utc_now()
    before = time.monotonic()
    try:
        result = subprocess.run(
            argv,
            cwd=cwd,
            env=clean_python_environment(),
            text=True,
            encoding="utf-8",
            errors="replace",
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        timed_out = False
    except subprocess.TimeoutExpired as error:
        result = subprocess.CompletedProcess(
            argv,
            124,
            error.stdout.decode("utf-8", "replace") if isinstance(error.stdout, bytes) else (error.stdout or ""),
            error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else (error.stderr or ""),
        )
        timed_out = True
    record = {
        "label": label,
        "argv": argv,
        "cwd": str(cwd),
        "started_utc": started,
        "elapsed_seconds": time.monotonic() - before,
        "exit_code": result.returncode,
        "timed_out": timed_out,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "environment": clean_python_environment(),
    }
    log.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    audit.commands.append(
        {
            key: value for key, value in record.items() if key not in {"stdout", "stderr", "environment"}
        }
        | {"log": str(log), "log_sha256": sha256(log)}
    )
    audit.require(f"command:{label}", result.returncode == 0 and not timed_out, result.returncode, 0)
    return result


def status_lines(text: str) -> list[str]:
    return [line for line in text.splitlines() if line.startswith("VALIDATION_STATUS=")]


def regular_tree_hashes(root: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for current, directory_names, file_names in os.walk(root, topdown=True, followlinks=False):
        current_path = Path(current)
        for directory in directory_names:
            mode = os.lstat(current_path / directory).st_mode
            if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
                raise VerificationError(f"unexpected replay directory type: {current_path / directory}")
        for filename in file_names:
            path = current_path / filename
            mode = os.lstat(path).st_mode
            if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
                raise VerificationError(f"unexpected replay file type: {path}")
            result[path.relative_to(root).as_posix()] = sha256(path)
    return result


def verify_julia_regression(
    extracted_repo: Path,
    replay_repo: Path,
    julia: dict[str, Any],
    audit: Audit,
) -> dict[str, Any]:
    require_exact_keys(
        julia,
        {
            "validator_sha256",
            "certificate_sha256",
            "run_receipt_sha256",
            "regression_driver_sha256",
            "direct_check_count",
            "timeout_seconds",
        },
        set(),
        "julia",
    )
    expected_hashes = {
        "validator": require_sha(julia["validator_sha256"], "julia.validator_sha256"),
        "certificate": require_sha(julia["certificate_sha256"], "julia.certificate_sha256"),
        "run_receipt": require_sha(julia["run_receipt_sha256"], "julia.run_receipt_sha256"),
        "regression_driver": require_sha(julia["regression_driver_sha256"], "julia.regression_driver_sha256"),
    }
    direct_check_count = require_integer(julia["direct_check_count"], "julia.direct_check_count", minimum=1)
    timeout = require_integer(julia["timeout_seconds"], "julia.timeout_seconds", minimum=1, maximum=3_600)
    for role, expected in expected_hashes.items():
        actual = sha256(extracted_repo / JULIA_PATHS[role])
        audit.require(f"julia_frozen_hash:{role}", actual == expected, actual, expected)

    shutil.copytree(extracted_repo, replay_repo, symlinks=True)
    replay_exp = replay_repo / EXP_ROOT
    validator = replay_repo / JULIA_PATHS["validator"]
    certificate = replay_repo / JULIA_PATHS["certificate"]
    run_receipt = replay_repo / JULIA_PATHS["run_receipt"]
    source_root = replay_repo / JULIA_PATHS["source_root"]
    driver = replay_repo / JULIA_PATHS["regression_driver"]
    results_path = replay_repo / JULIA_PATHS["regression_results"]
    regression_log_path = replay_repo / JULIA_PATHS["regression_log"]

    direct_argv = [
        sys.executable,
        "-I",
        str(validator),
        str(certificate),
        "--receipt",
        str(run_receipt),
        "--source-root",
        str(source_root),
    ]
    direct = run_python(audit, "fresh_extracted_validator", direct_argv, replay_exp, timeout)
    audit.require(
        "fresh_validator_status_marker",
        status_lines(direct.stdout) == ["VALIDATION_STATUS=PASS"]
        and not status_lines(direct.stderr)
        and not direct.stderr,
        {"stdout": direct.stdout, "stderr": direct.stderr},
        "PASS marker on stdout and empty stderr",
    )
    audit.require(
        "fresh_validator_exact_check_count",
        f"CHECKS={direct_check_count}\n" in direct.stdout,
        direct.stdout,
        f"CHECKS={direct_check_count}",
    )
    audit.require(
        "fresh_validator_certificate_hash_marker",
        f"CERTIFICATE_SHA256={expected_hashes['certificate']}\n" in direct.stdout,
        direct.stdout,
        expected_hashes["certificate"],
    )

    before_regression = regular_tree_hashes(replay_repo)
    regression = run_python(
        audit,
        "fresh_extracted_validator_regression",
        [sys.executable, "-I", str(driver)],
        replay_exp,
        timeout,
    )
    generated = require_mapping(read_json_strict(results_path), "fresh regression results")
    after_regression = regular_tree_hashes(replay_repo)
    audit.require(
        "fresh_regression_file_set_unchanged",
        set(after_regression) == set(before_regression),
        {
            "added": sorted(set(after_regression) - set(before_regression)),
            "removed": sorted(set(before_regression) - set(after_regression)),
        },
        {"added": [], "removed": []},
    )
    changed = {
        path
        for path in before_regression
        if before_regression[path] != after_regression[path]
    }
    allowed_changes = {JULIA_PATHS["regression_results"], JULIA_PATHS["regression_log"]}
    audit.require(
        "fresh_regression_only_expected_outputs_changed",
        changed <= allowed_changes,
        sorted(changed),
        f"subset of {sorted(allowed_changes)}",
    )
    audit.require(
        "fresh_regression_output_files_present",
        results_path.is_file() and regression_log_path.is_file(),
        {"results": results_path.is_file(), "log": regression_log_path.is_file()},
        {"results": True, "log": True},
    )
    expected_summary = {
        "all_passed": True,
        "valid_configurations": len(VALID_JULIA_CASES),
        "valid_accepted": len(VALID_JULIA_CASES),
        "unique_invalid_cases": len(INVALID_JULIA_CASES),
        "invalid_rejected": len(INVALID_JULIA_CASES),
        "total_process_invocations": len(VALID_JULIA_CASES) + len(INVALID_JULIA_CASES),
    }
    observed_summary = {key: generated.get(key) for key in expected_summary}
    audit.require("fresh_regression_exact_summary", observed_summary == expected_summary, observed_summary, expected_summary)
    audit.require(
        "fresh_regression_stdout_summary",
        regression.stderr == "" and all(f'"{key}": {json.dumps(value)}' in regression.stdout for key, value in expected_summary.items()),
        {"stdout": regression.stdout, "stderr": regression.stderr},
        expected_summary,
    )
    audit.require(
        "fresh_regression_validator_hash",
        generated.get("validator_sha256") == expected_hashes["validator"],
        generated.get("validator_sha256"),
        expected_hashes["validator"],
    )
    rows = require_list(generated.get("results"), "fresh regression results.results")
    by_name: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(rows):
        row = require_mapping(raw, f"fresh regression result {index}")
        name = require_string(row.get("name"), f"fresh regression result {index}.name")
        if name in by_name:
            raise VerificationError(f"duplicate fresh regression case name: {name!r}")
        by_name[name] = row
    expected_names = set(VALID_JULIA_CASES) | set(INVALID_JULIA_CASES)
    audit.require("fresh_regression_exact_case_set", set(by_name) == expected_names, sorted(by_name), sorted(expected_names))
    for name in VALID_JULIA_CASES:
        row = by_name[name]
        audit.require(
            f"fresh_valid_case:{name}",
            row.get("kind") == "valid"
            and row.get("passed") is True
            and row.get("exit_code") == 0
            and status_lines(str(row.get("stdout", ""))) == ["VALIDATION_STATUS=PASS"]
            and not status_lines(str(row.get("stderr", "")))
            and row.get("stderr") == "",
            {key: row.get(key) for key in ("kind", "passed", "exit_code", "stdout", "stderr")},
            "valid / passed / exit 0 / attributable PASS",
        )
    for name, reason in INVALID_JULIA_CASES.items():
        row = by_name[name]
        combined = str(row.get("stdout", "")) + str(row.get("stderr", ""))
        audit.require(
            f"fresh_invalid_case:{name}",
            row.get("kind") == "invalid"
            and row.get("passed") is True
            and row.get("exit_code") == 1
            and row.get("expected_reason_fragment") == reason
            and status_lines(str(row.get("stderr", ""))) == ["VALIDATION_STATUS=FAIL"]
            and not status_lines(str(row.get("stdout", "")))
            and reason in combined,
            {key: row.get(key) for key in ("kind", "passed", "exit_code", "expected_reason_fragment")},
            {"reason": reason, "exit_code": 1, "status": "FAIL"},
        )
    return {
        "direct_check_count": direct_check_count,
        **expected_summary,
        "generated_results": str(results_path),
        "generated_results_sha256": sha256(results_path),
    }


def validate_role_config(role: str, value: dict[str, Any], max_path_bytes: int) -> dict[str, Any]:
    require_exact_keys(
        value,
        {"metadata_path", "metadata_sha256", "hash_bindings", "required_text"},
        {"semantic_result_path"},
        f"lean_evidence.roles.{role}",
    )
    metadata_path = canonical_relative(value["metadata_path"], f"{role}.metadata_path", max_path_bytes)
    metadata_sha = require_sha(value["metadata_sha256"], f"{role}.metadata_sha256")
    bindings = require_mapping(value["hash_bindings"], f"{role}.hash_bindings")
    if not bindings:
        raise VerificationError(f"{role}.hash_bindings cannot be empty")
    normalized_bindings: dict[str, str] = {}
    for field, path in bindings.items():
        field = require_string(field, f"{role}.hash_bindings field")
        normalized_bindings[field] = canonical_relative(path, f"{role}.hash_bindings.{field}", max_path_bytes)
    required_text = require_mapping(value["required_text"], f"{role}.required_text")
    normalized_text: dict[str, dict[str, list[str]]] = {}
    for path, rules_value in required_text.items():
        path = canonical_relative(path, f"{role}.required_text path", max_path_bytes)
        rules = require_mapping(rules_value, f"{role}.required_text.{path}")
        require_exact_keys(rules, {"contains", "absent"}, set(), f"{role}.required_text.{path}")
        contains = require_list(rules["contains"], f"{role}.required_text.{path}.contains")
        absent = require_list(rules["absent"], f"{role}.required_text.{path}.absent")
        if any(not isinstance(item, str) or not item for item in contains + absent):
            raise VerificationError(f"{role}.required_text.{path} contains a non-string or empty needle")
        normalized_text[path] = {"contains": contains, "absent": absent}
    if role in {"production_build", "positive_witness"} and not normalized_text:
        raise VerificationError(f"{role} must have at least one required-text log contract")
    semantic = value.get("semantic_result_path")
    if semantic is not None:
        semantic = canonical_relative(semantic, f"{role}.semantic_result_path", max_path_bytes)
        if semantic not in normalized_bindings.values():
            raise VerificationError(f"{role}.semantic_result_path must be covered by a metadata hash binding")
    return {
        "metadata_path": metadata_path,
        "metadata_sha256": metadata_sha,
        "hash_bindings": normalized_bindings,
        "required_text": normalized_text,
        "semantic_result_path": semantic,
    }


def verify_evidence_roles(
    repo: Path,
    archive_files: dict[str, dict[str, Any]],
    lean: dict[str, Any],
    pins: dict[str, str],
    limits: dict[str, int],
    audit: Audit,
) -> dict[str, dict[str, Any]]:
    require_exact_keys(lean, {"roles", "allowed_axioms", "forbidden_tokens"}, set(), "lean_evidence")
    roles_value = require_mapping(lean["roles"], "lean_evidence.roles")
    audit.require(
        "lean_required_role_set",
        set(roles_value) == set(REQUIRED_LEAN_ROLES),
        sorted(roles_value),
        sorted(REQUIRED_LEAN_ROLES),
    )
    role_records: dict[str, dict[str, Any]] = {}
    required_bound_paths = {
        "production_build": set(PRODUCTION_LEAN_SOURCES),
        "positive_witness": {PRODUCTION_LEAN_SOURCES[1]},
        "axiom_audit": {f"{EXP_ROOT}/assurance/PrintAndAxiomAudit.lean"},
        "negative_controls": {
            f"{EXP_ROOT}/controls/lean/run_negative_controls.py",
            NEGATIVE_BATCHED_SOURCE,
            NEGATIVE_RAW_DIAGNOSTIC,
            *(value["source"] for value in NEGATIVE_LEAN_CASES.values()),
        },
        "forbidden_scan": set(PRODUCTION_LEAN_SOURCES),
    }
    minimum_binding_counts = {
        "production_build": 3,
        "positive_witness": 2,
        "axiom_audit": 3,
        "negative_controls": 13,
        "forbidden_scan": 3,
    }
    for role in REQUIRED_LEAN_ROLES:
        config = validate_role_config(role, require_mapping(roles_value[role], f"role {role}"), limits["max_path_bytes"])
        configured_bound_paths = set(config["hash_bindings"].values())
        if "timing_sha256" not in config["hash_bindings"] or "log_sha256" not in config["hash_bindings"]:
            raise VerificationError(f"Lean role {role!r} must bind its logged-command timing record and full log")
        missing_required_bindings = required_bound_paths[role] - configured_bound_paths
        if missing_required_bindings:
            raise VerificationError(
                f"Lean role {role!r} does not metadata-bind required source paths: "
                f"{sorted(missing_required_bindings)}"
            )
        if len(configured_bound_paths) < minimum_binding_counts[role]:
            raise VerificationError(
                f"Lean role {role!r} has too few distinct metadata-bound artifacts: "
                f"{len(configured_bound_paths)} < {minimum_binding_counts[role]}"
            )
        metadata_path = config["metadata_path"]
        if metadata_path not in archive_files:
            raise VerificationError(f"Lean role metadata is not archive/manifest/Git bound: {metadata_path!r}")
        actual_metadata_hash = sha256(repo / metadata_path)
        audit.require(
            f"lean_role_metadata_hash:{role}",
            actual_metadata_hash == config["metadata_sha256"],
            actual_metadata_hash,
            config["metadata_sha256"],
        )
        metadata = require_mapping(read_json_strict(repo / metadata_path), f"Lean role metadata {role}")
        audit.require(f"lean_role_status:{role}", metadata.get("status") == "PASS", metadata.get("status"), "PASS")
        audit.require(f"lean_role_exit_code:{role}", metadata.get("exit_code") == 0, metadata.get("exit_code"), 0)
        expected_pin_fields = {
            "lean_version": pins["lean_version"],
            "mathlib_revision": pins["mathlib_revision"],
        }
        for field, expected in expected_pin_fields.items():
            audit.require(
                f"lean_role_pin:{role}:{field}", metadata.get(field) == expected, metadata.get(field), expected
            )
        bound_files: dict[str, str] = {}
        for field, relative in config["hash_bindings"].items():
            if relative not in archive_files:
                raise VerificationError(f"Lean role artifact is not archive/manifest/Git bound: {relative!r}")
            expected = dotted_get(metadata, field, f"Lean role metadata {role}")
            expected = require_sha(expected, f"Lean role {role} hash field {field}")
            actual = sha256(repo / relative)
            audit.require(f"lean_role_artifact_hash:{role}:{relative}", actual == expected, actual, expected)
            bound_files[relative] = actual
        timing_relative = config["hash_bindings"]["timing_sha256"]
        timing = require_mapping(read_json_strict(repo / timing_relative), f"Lean role timing {role}")
        audit.require(
            f"lean_role_timing_schema:{role}",
            timing.get("schema") == "ndea.exp002.logged_command.v1",
            timing.get("schema"),
            "ndea.exp002.logged_command.v1",
        )
        timing_contract = {
            "exit_code": 0,
            "argv": metadata.get("argv"),
            "cwd": metadata.get("cwd"),
            "started_utc": metadata.get("started_utc"),
            "finished_utc": metadata.get("finished_utc"),
            "elapsed_seconds": metadata.get("elapsed_seconds"),
            "log_sha256": metadata.get("log_sha256"),
        }
        timing_observed = {field: timing.get(field) for field in timing_contract}
        audit.require(
            f"lean_role_timing_metadata_agreement:{role}",
            timing_observed == timing_contract,
            timing_observed,
            timing_contract,
        )
        configured_log = config["hash_bindings"]["log_sha256"]
        audit.require(
            f"lean_role_timing_log_name:{role}",
            Path(str(timing.get("log", ""))).name == Path(configured_log).name,
            Path(str(timing.get("log", ""))).name,
            Path(configured_log).name,
        )
        for relative, rules in config["required_text"].items():
            if relative not in bound_files:
                raise VerificationError(f"Lean role text contract is not hash-bound by its metadata: {relative!r}")
            try:
                text = (repo / relative).read_text(encoding="utf-8", errors="strict")
            except (OSError, UnicodeError) as error:
                raise VerificationError(f"cannot inspect Lean evidence text {relative!r}: {error}") from error
            missing = [needle for needle in rules["contains"] if needle not in text]
            present = [needle for needle in rules["absent"] if needle in text]
            audit.require(
                f"lean_role_text_contract:{role}:{relative}",
                not missing and not present,
                {"missing_required": missing, "present_forbidden": present},
                {"missing_required": [], "present_forbidden": []},
            )
        role_records[role] = {
            "metadata_path": metadata_path,
            "metadata_sha256": actual_metadata_hash,
            "bound_files": bound_files,
            "log_path": config["hash_bindings"]["log_sha256"],
            "semantic_result_path": config["semantic_result_path"],
        }
    return role_records


def is_axiom_signature_start(line: str, name: str) -> bool:
    return line.startswith(name + " :") or line.startswith("@" + name + " :")


def parse_bound_axiom_log(log_path: Path) -> dict[str, dict[str, Any]]:
    """Independently reconstruct signatures and axiom rows from Lean's output."""
    try:
        lines = log_path.read_text(encoding="utf-8", errors="strict").splitlines()
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot read bound axiom-audit log: {error}") from error

    starts: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        for name in REQUIRED_DECLARATIONS:
            if is_axiom_signature_start(line, name):
                starts.append((index, name))
                break
    observed_signature_order = tuple(name for _, name in starts)
    if observed_signature_order != REQUIRED_DECLARATIONS:
        raise VerificationError(
            "bound axiom-audit log signature sequence mismatch: "
            f"{list(observed_signature_order)!r}"
        )

    first_print = next((index for index, line in enumerate(lines) if line.startswith("theorem ")), len(lines))
    signatures: dict[str, str] = {}
    for offset, (start, name) in enumerate(starts):
        stop = starts[offset + 1][0] if offset + 1 < len(starts) else first_print
        signature = "\n".join(lines[start:stop]).strip()
        if not signature or not is_axiom_signature_start(signature, name):
            raise VerificationError(f"empty or malformed bound-log signature for {name}")
        signatures[name] = signature

    joined = "\n".join(lines)
    axiom_rows: dict[str, list[str]] = {}
    for match in AXIOM_DEPENDENCY_BLOCK.finditer(joined):
        name, payload = match.groups()
        axioms = [] if not payload.strip() else [item.strip() for item in payload.split(",")]
        if name in axiom_rows:
            raise VerificationError(f"duplicate bound-log axiom report for {name}")
        if (
            any(AXIOM_IDENTIFIER.fullmatch(axiom) is None for axiom in axioms)
            or len(axioms) != len(set(axioms))
        ):
            raise VerificationError(f"invalid or duplicate bound-log axiom names for {name}")
        axiom_rows[name] = axioms
    for match in NO_AXIOM_DEPENDENCY_LINE.finditer(joined):
        name = match.group(1)
        if name in axiom_rows:
            raise VerificationError(f"duplicate bound-log axiom report for {name}")
        axiom_rows[name] = []

    if set(axiom_rows) != set(REQUIRED_DECLARATIONS):
        raise VerificationError(
            "bound axiom-audit log declaration mismatch: "
            f"missing={sorted(set(REQUIRED_DECLARATIONS) - set(axiom_rows))!r} "
            f"extra={sorted(set(axiom_rows) - set(REQUIRED_DECLARATIONS))!r}"
        )
    return {
        name: {"signature": signatures[name], "axioms": axiom_rows[name]}
        for name in REQUIRED_DECLARATIONS
    }


def verify_axiom_audit(
    repo: Path,
    result_path: str,
    log_path: str,
    allowed_axioms: list[Any],
    audit: Audit,
) -> dict[str, Any]:
    if not result_path:
        raise VerificationError("axiom_audit role requires semantic_result_path")
    audit_source_path = repo / EXP_ROOT / "assurance" / "PrintAndAxiomAudit.lean"
    try:
        audit_source_lines = audit_source_path.read_text(encoding="utf-8", errors="strict").splitlines()
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot inspect PrintAndAxiomAudit.lean: {error}") from error
    check_lines = [line for line in audit_source_lines if line.lstrip().startswith("#check")]
    expected_check_lines = [f"#check @{name}" for name in REQUIRED_DECLARATIONS]
    audit.require(
        "axiom_audit_source_exact_check_requests",
        check_lines == expected_check_lines,
        check_lines,
        expected_check_lines,
    )
    signature_requests = [
        line.removeprefix("#print ").strip()
        for line in audit_source_lines
        if line.startswith("#print ") and not line.startswith("#print axioms ")
    ]
    axiom_requests = [
        line.removeprefix("#print axioms ").strip()
        for line in audit_source_lines
        if line.startswith("#print axioms ")
    ]
    audit.require(
        "axiom_audit_source_exact_signature_requests",
        tuple(signature_requests) == REQUIRED_DECLARATIONS,
        signature_requests,
        list(REQUIRED_DECLARATIONS),
    )
    audit.require(
        "axiom_audit_source_exact_axiom_requests",
        tuple(axiom_requests) == REQUIRED_DECLARATIONS,
        axiom_requests,
        list(REQUIRED_DECLARATIONS),
    )
    allowed: list[str] = []
    for index, item in enumerate(allowed_axioms):
        allowed.append(require_string(item, f"lean_evidence.allowed_axioms[{index}]"))
    if len(allowed) != len(set(allowed)):
        raise VerificationError("lean_evidence.allowed_axioms contains duplicates")

    bound_log = parse_bound_axiom_log(repo / log_path)
    derived_unexpected = sorted(
        {axiom for row in bound_log.values() for axiom in row["axioms"]} - set(allowed)
    )
    derived_forbidden = sorted(
        {
            axiom
            for row in bound_log.values()
            for axiom in row["axioms"]
            if "sorryAx" in axiom or "unsafe" in axiom or "native_decide" in axiom
        }
    )
    audit.require(
        "axiom_audit_bound_log_unexpected_axioms_empty",
        derived_unexpected == [],
        derived_unexpected,
        [],
    )
    audit.require(
        "axiom_audit_bound_log_forbidden_dependencies_empty",
        derived_forbidden == [],
        derived_forbidden,
        [],
    )

    results = require_mapping(read_json_strict(repo / result_path), "axiom audit results")
    require_exact_keys(
        results,
        {
            "schema",
            "status",
            "source_log",
            "allowed_axioms",
            "unexpected_axioms",
            "forbidden_dependencies",
            "declarations",
        },
        set(),
        "axiom audit results",
    )
    audit.require(
        "axiom_audit_result_schema",
        results.get("schema") == AXIOM_AUDIT_SCHEMA,
        results.get("schema"),
        AXIOM_AUDIT_SCHEMA,
    )
    result_source_log = require_string(results.get("source_log"), "axiom audit results.source_log")
    audit.require(
        "axiom_audit_result_log_basename",
        Path(result_source_log).name == Path(log_path).name,
        Path(result_source_log).name,
        Path(log_path).name,
    )
    result_allowed = require_list(results.get("allowed_axioms"), "axiom audit results.allowed_axioms")
    audit.require(
        "axiom_audit_result_allowed_axioms",
        result_allowed == sorted(allowed),
        result_allowed,
        sorted(allowed),
    )
    audit.require("axiom_audit_semantic_status", results.get("status") == "PASS", results.get("status"), "PASS")
    audit.require(
        "axiom_audit_unexpected_axioms_match_bound_log",
        results.get("unexpected_axioms") == derived_unexpected,
        results.get("unexpected_axioms"),
        derived_unexpected,
    )
    audit.require(
        "axiom_audit_forbidden_dependencies_match_bound_log",
        results.get("forbidden_dependencies") == derived_forbidden,
        results.get("forbidden_dependencies"),
        derived_forbidden,
    )
    declarations = require_list(results.get("declarations"), "axiom audit declarations")
    observed: dict[str, dict[str, Any]] = {}
    observed_order: list[str] = []
    for index, value in enumerate(declarations):
        row = require_mapping(value, f"axiom audit declaration {index}")
        require_exact_keys(row, {"name", "signature", "axioms"}, set(), f"axiom audit declaration {index}")
        name = require_string(row.get("name"), f"axiom audit declaration {index}.name")
        signature = require_string(row.get("signature"), f"axiom audit declaration {index}.signature")
        axioms = require_list(row.get("axioms"), f"axiom audit declaration {index}.axioms")
        if any(not isinstance(item, str) or not item for item in axioms):
            raise VerificationError(f"axiom audit declaration {name!r} has invalid axiom names")
        if len(axioms) != len(set(axioms)):
            raise VerificationError(f"axiom audit declaration {name!r} has duplicate axiom names")
        unexpected = sorted(set(axioms) - set(allowed))
        if unexpected:
            raise VerificationError(f"axiom audit declaration {name!r} has unexpected axioms: {unexpected}")
        if name in observed:
            raise VerificationError(f"duplicate axiom-audit declaration: {name!r}")
        observed[name] = {"signature": signature, "axioms": axioms}
        observed_order.append(name)
    audit.require(
        "axiom_audit_exact_declaration_sequence",
        tuple(observed_order) == REQUIRED_DECLARATIONS,
        observed_order,
        list(REQUIRED_DECLARATIONS),
    )
    audit.require(
        "axiom_audit_result_matches_bound_log",
        observed == bound_log,
        observed,
        bound_log,
    )
    return {
        "path": result_path,
        "log_path": log_path,
        "log_sha256": sha256(repo / log_path),
        "declarations": observed,
        "allowed_axioms": allowed,
    }


def parse_negative_control_diagnostic(
    diagnostic: str,
    case: str,
) -> tuple[dict[str, Any], str, str]:
    harness_header = "=== HARNESS ===\n"
    stdout_header = "\n=== STDOUT ===\n"
    stderr_header = "\n=== STDERR ===\n"
    if not diagnostic.startswith(harness_header):
        raise VerificationError(f"Lean negative-control {case} diagnostic lacks its harness header")
    if diagnostic.count(stdout_header) != 1 or diagnostic.count(stderr_header) != 1:
        raise VerificationError(f"Lean negative-control {case} diagnostic section framing is ambiguous")
    harness_text, process_output = diagnostic[len(harness_header):].split(stdout_header, 1)
    stdout, stderr = process_output.split(stderr_header, 1)
    harness = require_mapping(
        loads_json_strict(harness_text, f"Lean negative-control {case} diagnostic harness"),
        f"Lean negative-control {case} diagnostic harness",
    )
    require_exact_keys(
        harness,
        {
            "argv",
            "cwd",
            "started_utc",
            "finished_utc",
            "elapsed_seconds",
            "timeout_seconds",
            "timed_out",
            "exit_code",
            "fixture_error",
            "spawn_error",
        },
        set(),
        f"Lean negative-control {case} diagnostic harness",
    )
    return harness, stdout, stderr


def classify_negative_control_diagnostic(
    *,
    diagnostic: str,
    source_argument: str,
    witness: str,
    expected_line: int,
    fixture_contract_valid: bool,
    exit_code: int | None,
    timed_out: bool,
    fixture_error: Any,
    spawn_error: Any,
) -> tuple[bool, str, dict[str, bool]]:
    lowered_messages = LEAN_DIAGNOSTIC_HEADER_PREFIX.sub("", diagnostic).lower()
    error_header_count = len(LEAN_ERROR_HEADER.findall(diagnostic))
    intended_header = re.search(
        rf"^{re.escape(source_argument)}:{expected_line}:[0-9]+:[ \t]+error:",
        diagnostic,
        re.MULTILINE,
    )
    type_mismatch_header = re.search(
        rf"^{re.escape(source_argument)}:{expected_line}:[0-9]+:[ \t]+error:[ \t]+"
        r"(?i:type mismatch)\b",
        diagnostic,
        re.MULTILINE,
    )
    checks = {
        "fixture_contract_valid": fixture_contract_valid,
        "diagnostic_utf8": True,
        "exactly_one_error_header": error_header_count == 1,
        "intended_source_line": intended_header is not None,
        "type_mismatch": type_mismatch_header is not None,
        "witness_present": witness in diagnostic,
        "has_actual_and_expected_types": (
            re.search(
                r"\bhas type\b[\s\S]*\bbut is expected to have type\b",
                diagnostic,
                re.IGNORECASE,
            )
            is not None
        ),
        "no_import_or_infrastructure_error": not any(
            marker in lowered_messages
            for marker in NEGATIVE_CONTROL_INFRASTRUCTURE_MARKERS
        ),
        "no_malformed_source_error": not any(
            marker in lowered_messages for marker in NEGATIVE_CONTROL_MALFORMED_MARKERS
        ),
    }
    if fixture_error is not None:
        return False, "FIXTURE_READ_ERROR", checks
    if timed_out:
        return False, "PROCESS_TIMEOUT", checks
    if spawn_error is not None:
        return False, "PROCESS_SPAWN_ERROR", checks
    if exit_code is None:
        return False, "NO_PROCESS_EXIT_CODE", checks
    if type(exit_code) is not int:
        return False, "INVALID_PROCESS_EXIT_CODE", checks
    if exit_code < 0:
        return False, "PROCESS_SIGNAL_TERMINATION", checks
    if exit_code == 0:
        return False, "FALSE_STATEMENT_WAS_ACCEPTED", checks
    if exit_code != 1:
        return False, "UNEXPECTED_PROCESS_EXIT_CODE", checks
    if not fixture_contract_valid:
        return False, "MALFORMED_FIXTURE_CONTRACT", checks
    if not checks["no_import_or_infrastructure_error"]:
        return False, "IMPORT_OR_INFRASTRUCTURE_FAILURE", checks
    if not checks["no_malformed_source_error"]:
        return False, "MALFORMED_SOURCE_FAILURE", checks
    if not all(checks.values()):
        return False, "UNATTRIBUTABLE_REJECTION_DIAGNOSTIC", checks
    return True, NEGATIVE_CONTROL_SUCCESS_REASON, checks


def verify_negative_controls_v2_historical(repo: Path, result_path: str, audit: Audit) -> dict[str, Any]:
    if not result_path:
        raise VerificationError("negative_controls role requires semantic_result_path")
    results = require_mapping(read_json_strict(repo / result_path), "Lean negative-control results")
    require_exact_keys(
        results,
        {
            "schema",
            "started_utc",
            "finished_utc",
            "cwd",
            "timeout_environment_variable",
            "timeout_seconds",
            "unique_cases",
            "total_process_invocations",
            "passed",
            "failed",
            "results",
        },
        set(),
        "Lean negative-control results",
    )
    audit.require(
        "lean_negative_controls_schema",
        results.get("schema") == NEGATIVE_CONTROL_SCHEMA,
        results.get("schema"),
        NEGATIVE_CONTROL_SCHEMA,
    )
    receipt_cwd = require_string(results.get("cwd"), "Lean negative-control results.cwd")
    require_string(results.get("started_utc"), "Lean negative-control results.started_utc")
    require_string(results.get("finished_utc"), "Lean negative-control results.finished_utc")
    timeout_seconds = require_integer(
        results.get("timeout_seconds"),
        "Lean negative-control results.timeout_seconds",
        minimum=1,
        maximum=3_600,
    )
    audit.require(
        "lean_negative_controls_timeout_environment",
        results.get("timeout_environment_variable") == NEGATIVE_CONTROL_TIMEOUT_ENV,
        results.get("timeout_environment_variable"),
        NEGATIVE_CONTROL_TIMEOUT_ENV,
    )
    expected_count = len(NEGATIVE_LEAN_CASES)
    expected_summary = {
        "unique_cases": expected_count,
        "total_process_invocations": expected_count,
        "passed": expected_count,
        "failed": 0,
    }
    for field in expected_summary:
        require_integer(
            results.get(field),
            f"Lean negative-control results.{field}",
            minimum=0,
        )
    observed_summary = {key: results.get(key) for key in expected_summary}
    audit.require("lean_negative_controls_exact_summary", observed_summary == expected_summary, observed_summary, expected_summary)
    rows = require_list(results.get("results"), "Lean negative-control results.results")
    by_case: dict[str, dict[str, Any]] = {}
    observed_order: list[str] = []
    for index, value in enumerate(rows):
        row = require_mapping(value, f"Lean negative-control result {index}")
        require_exact_keys(
            row,
            {
                "case",
                "source",
                "source_sha256",
                "witness_expected_in_diagnostic",
                "argv",
                "cwd",
                "started_utc",
                "finished_utc",
                "exit_code",
                "elapsed_seconds",
                "timeout_seconds",
                "timed_out",
                "fixture_error",
                "spawn_error",
                "expected_exact_line",
                "diagnostic_checks",
                "diagnostic",
                "diagnostic_sha256",
                "attributable_rejection",
                "reason_code",
                "status",
            },
            set(),
            f"Lean negative-control result {index}",
        )
        case = require_string(row.get("case"), f"Lean negative-control result {index}.case")
        require_boolean(row.get("timed_out"), f"Lean negative-control result {index}.timed_out")
        require_boolean(
            row.get("attributable_rejection"),
            f"Lean negative-control result {index}.attributable_rejection",
        )
        if case in by_case:
            raise VerificationError(f"duplicate Lean negative-control case: {case!r}")
        by_case[case] = row
        observed_order.append(case)
    audit.require(
        "lean_negative_controls_exact_case_sequence",
        tuple(observed_order) == tuple(NEGATIVE_LEAN_CASES),
        observed_order,
        list(NEGATIVE_LEAN_CASES),
    )
    for case, expected in NEGATIVE_LEAN_CASES.items():
        row = by_case[case]
        source = row.get("source")
        witness = row.get("witness_expected_in_diagnostic")
        diagnostic = row.get("diagnostic")
        if source != expected["source"]:
            raise VerificationError(f"Lean negative-control source mismatch for {case!r}")
        if witness != expected["witness"]:
            raise VerificationError(f"Lean negative-control witness mismatch for {case!r}")
        diagnostic = require_string(diagnostic, f"Lean negative-control {case}.diagnostic")
        canonical_relative(diagnostic, f"Lean negative-control {case}.diagnostic", 16_384)
        expected_diagnostic = f"{EXP_ROOT}/controls/lean/rejection_diagnostics/{case}.rejection.log"
        if diagnostic != expected_diagnostic:
            raise VerificationError(
                f"Lean negative-control diagnostic path mismatch for {case!r}: {diagnostic!r}"
            )
        source_path = repo / source
        diagnostic_path = repo / diagnostic
        actual_source_hash = sha256(source_path)
        actual_diagnostic_hash = sha256(diagnostic_path)
        try:
            diagnostic_text = diagnostic_path.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeError) as error:
            raise VerificationError(f"cannot inspect Lean negative-control diagnostic {diagnostic!r}: {error}") from error

        source_text = source_path.read_text(encoding="utf-8", errors="strict")
        exact_pattern = re.compile(rf"^\s*exact\s+{re.escape(expected['witness'])}\s*$")
        exact_lines = [
            number
            for number, line in enumerate(source_text.splitlines(), start=1)
            if exact_pattern.fullmatch(line)
        ]
        audit.require(
            f"lean_negative_control_fixture_exact_line:{case}",
            len(exact_lines) == 1,
            exact_lines,
            "exactly one matching exact-witness line",
        )
        expected_line = exact_lines[0]

        harness, stdout, stderr = parse_negative_control_diagnostic(diagnostic_text, case)
        harness_argv = require_list(harness.get("argv"), f"Lean negative-control {case} harness.argv")
        harness_cwd = require_string(harness.get("cwd"), f"Lean negative-control {case} harness.cwd")
        source_argument_valid = (
            len(harness_argv) == 4
            and all(isinstance(item, str) and item for item in harness_argv)
            and Path(harness_argv[0]).name == "lake"
            and harness_argv[1:3] == ["env", "lean"]
            and Path(harness_argv[3]).is_absolute()
            and harness_argv[3] == str(Path(harness_cwd) / PurePosixPath(source))
        )
        audit.require(
            f"lean_negative_control_harness_command:{case}",
            source_argument_valid,
            harness_argv,
            "<lake> env lean <absolute cwd/source>",
        )
        require_string(harness.get("started_utc"), f"Lean negative-control {case} harness.started_utc")
        require_string(harness.get("finished_utc"), f"Lean negative-control {case} harness.finished_utc")
        harness_elapsed = harness.get("elapsed_seconds")
        if type(harness_elapsed) not in {int, float} or harness_elapsed < 0:
            raise VerificationError(f"Lean negative-control {case} has invalid harness elapsed_seconds")
        harness_timeout = require_integer(
            harness.get("timeout_seconds"),
            f"Lean negative-control {case} harness.timeout_seconds",
            minimum=1,
            maximum=3_600,
        )
        harness_timed_out = require_boolean(
            harness.get("timed_out"),
            f"Lean negative-control {case} harness.timed_out",
        )
        harness_exit = harness.get("exit_code")
        natural_nonzero_exit = (
            isinstance(harness_exit, int)
            and not isinstance(harness_exit, bool)
            and harness_exit == 1
            and harness_timed_out is False
            and harness.get("fixture_error") is None
            and harness.get("spawn_error") is None
        )
        audit.require(
            f"lean_negative_control_natural_nonzero_exit:{case}",
            natural_nonzero_exit,
            {
                "exit_code": harness_exit,
                "timed_out": harness.get("timed_out"),
                "fixture_error": harness.get("fixture_error"),
                "spawn_error": harness.get("spawn_error"),
            },
            "exact exit code 1, no timeout, fixture error, or spawn error",
        )
        row_harness_fields = {
            key: row.get(key)
            for key in (
                "argv",
                "cwd",
                "started_utc",
                "finished_utc",
                "exit_code",
                "elapsed_seconds",
                "timeout_seconds",
                "timed_out",
                "fixture_error",
                "spawn_error",
            )
        }
        audit.require(
            f"lean_negative_control_row_matches_harness:{case}",
            row_harness_fields == harness,
            row_harness_fields,
            harness,
        )
        audit.require(
            f"lean_negative_control_receipt_context:{case}",
            row.get("cwd") == receipt_cwd
            and row.get("timeout_seconds") == timeout_seconds
            and harness_timeout == timeout_seconds,
            {"cwd": row.get("cwd"), "timeout_seconds": row.get("timeout_seconds")},
            {"cwd": receipt_cwd, "timeout_seconds": timeout_seconds},
        )

        independently_attributable, independent_reason, independent_checks = (
            classify_negative_control_diagnostic(
                diagnostic=stdout + "\n" + stderr,
                source_argument=harness_argv[3],
                witness=expected["witness"],
                expected_line=expected_line,
                fixture_contract_valid=len(exact_lines) == 1,
                exit_code=harness_exit,
                timed_out=harness_timed_out,
                fixture_error=harness.get("fixture_error"),
                spawn_error=harness.get("spawn_error"),
            )
        )
        reported_checks = require_mapping(
            row.get("diagnostic_checks"),
            f"Lean negative-control {case}.diagnostic_checks",
        )
        require_exact_keys(
            reported_checks,
            set(NEGATIVE_CONTROL_DIAGNOSTIC_CHECKS),
            set(),
            f"Lean negative-control {case}.diagnostic_checks",
        )
        for check_name in NEGATIVE_CONTROL_DIAGNOSTIC_CHECKS:
            require_boolean(
                reported_checks.get(check_name),
                f"Lean negative-control {case}.diagnostic_checks.{check_name}",
            )
        attributable = (
            independently_attributable
            and independent_reason == NEGATIVE_CONTROL_SUCCESS_REASON
            and all(independent_checks.values())
            and row.get("diagnostic_checks") == independent_checks
            and row.get("reason_code") == independent_reason
            and row.get("expected_exact_line") == expected_line
            and row.get("status") == "PASS"
            and row.get("attributable_rejection") is True
            and row.get("source_sha256") == actual_source_hash
            and row.get("diagnostic_sha256") == actual_diagnostic_hash
        )
        audit.require(
            f"lean_negative_control_attributable:{case}",
            attributable,
            {
                "exit_code": harness_exit,
                "status": row.get("status"),
                "attributable_rejection": row.get("attributable_rejection"),
                "reason_code": row.get("reason_code"),
                "expected_exact_line": row.get("expected_exact_line"),
                "source_sha256": row.get("source_sha256"),
                "diagnostic_sha256": row.get("diagnostic_sha256"),
                "diagnostic_checks": row.get("diagnostic_checks"),
            },
            "v2 exact exit 1 and independently reclassified attributable type mismatch",
        )
    return {"path": result_path, **expected_summary}


def reconstruct_negative_batched_source(
    repo: Path,
) -> tuple[str, dict[str, dict[str, Any]]]:
    """Independently reconstruct the batch from the seven frozen fixtures."""

    payloads: list[str] = []
    contracts: dict[str, dict[str, Any]] = {}
    for case, expected in NEGATIVE_LEAN_CASES.items():
        source_path = repo / expected["source"]
        actual_hash = sha256(source_path)
        if actual_hash != expected["sha256"]:
            raise VerificationError(
                f"frozen Lean negative-control fixture hash mismatch for {case!r}: "
                f"observed={actual_hash!r} expected={expected['sha256']!r}"
            )
        try:
            text = source_path.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeError) as error:
            raise VerificationError(
                f"cannot read frozen Lean negative-control fixture {case!r}: {error}"
            ) from error
        if not text.startswith(NEGATIVE_FIXTURE_PREAMBLE) or not text.endswith(
            NEGATIVE_SOURCE_EPILOGUE
        ):
            raise VerificationError(f"Lean negative-control fixture wrapper mismatch: {case!r}")
        payload = text[
            len(NEGATIVE_FIXTURE_PREAMBLE) : -len(NEGATIVE_SOURCE_EPILOGUE)
        ]
        original = f"theorem {expected['theorem']}"
        renamed = f"theorem {expected['batched_theorem']}"
        if payload.count(original) != 1:
            raise VerificationError(f"Lean negative-control theorem mismatch: {case!r}")
        exact_lines = [
            number
            for number, line in enumerate(text.splitlines(), start=1)
            if line.strip() == f"exact {expected['witness']}"
        ]
        if len(exact_lines) != 1:
            raise VerificationError(f"Lean negative-control witness-line mismatch: {case!r}")
        payloads.append(payload.replace(original, renamed, 1))
        contracts[case] = {**expected, "fixture_exact_line": exact_lines[0]}

    reconstructed = (
        NEGATIVE_BATCHED_PREAMBLE
        + "\n\n".join(payloads)
        + NEGATIVE_SOURCE_EPILOGUE
    )
    batched_path = repo / NEGATIVE_BATCHED_SOURCE
    try:
        observed = batched_path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot read batched Lean negative controls: {error}") from error
    if observed != reconstructed:
        raise VerificationError(
            "batched Lean source is not the exact reconstruction of the seven frozen "
            "fixtures with only the declared theorem-identifier renames"
        )
    for case, contract in contracts.items():
        lines = [
            number
            for number, line in enumerate(observed.splitlines(), start=1)
            if line.strip() == f"exact {contract['witness']}"
        ]
        if len(lines) != 1:
            raise VerificationError(f"batched Lean witness-line mismatch: {case!r}")
        contract["combined_exact_line"] = lines[0]
    return observed, contracts


def parse_batched_raw_diagnostic(text: str) -> tuple[dict[str, Any], str]:
    harness_header = "=== SHARED PROCESS HARNESS ===\n"
    output_header = "\n=== MERGED STDOUT+STDERR ===\n"
    if not text.startswith(harness_header) or text.count(output_header) != 1:
        raise VerificationError("batched negative-control raw diagnostic framing mismatch")
    harness_text, output = text[len(harness_header) :].split(output_header, 1)
    harness = require_mapping(
        loads_json_strict(harness_text, "batched negative-control raw harness"),
        "batched negative-control raw harness",
    )
    require_exact_keys(
        harness,
        {
            "process_invocation_id",
            "argv",
            "cwd",
            "started_utc",
            "finished_utc",
            "elapsed_seconds",
            "timeout_seconds",
            "timed_out",
            "exit_code",
            "spawn_error",
            "stderr_mode",
            "capture_limit_bytes",
            "output_limit_exceeded",
        },
        set(),
        "batched negative-control raw harness",
    )
    return harness, output


def split_batched_diagnostics(output: str) -> tuple[str, list[dict[str, Any]]]:
    matches = list(LEAN_ANY_DIAGNOSTIC_HEADER.finditer(output))
    preamble = output[: matches[0].start()] if matches else output
    blocks: list[dict[str, Any]] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(output)
        blocks.append(
            {
                "path": match.group("path"),
                "line": int(match.group("line")),
                "column": int(match.group("column")),
                "severity": match.group("severity").lower(),
                "message": match.group("message"),
                "text": output[match.start() : end],
            }
        )
    return preamble, blocks


def parse_batched_case_log(text: str, case: str) -> tuple[dict[str, Any], str]:
    reference_header = "=== SHARED PROCESS REFERENCE ===\n"
    block_header = "\n=== LEAN DIAGNOSTIC BLOCK ===\n"
    if not text.startswith(reference_header) or text.count(block_header) != 1:
        raise VerificationError(f"batched negative-control case-log framing mismatch: {case!r}")
    reference_text, block = text[len(reference_header) :].split(block_header, 1)
    reference = require_mapping(
        loads_json_strict(reference_text, f"batched negative-control reference {case}"),
        f"batched negative-control reference {case}",
    )
    require_exact_keys(
        reference,
        {"case", "process_invocation_id", "raw_diagnostic", "raw_diagnostic_sha256"},
        set(),
        f"batched negative-control reference {case}",
    )
    return reference, block


def independent_batched_case_checks(
    block: dict[str, Any] | None,
    contract: dict[str, Any],
    source_argument: str,
    witnesses: tuple[str, ...],
    global_checks: dict[str, bool],
) -> dict[str, bool]:
    text = "" if block is None else str(block["text"])
    lowered = LEAN_DIAGNOSTIC_HEADER_PREFIX.sub("", text).lower()
    return {
        "fixture_contract_valid": True,
        "diagnostic_utf8": global_checks["diagnostic_utf8"],
        "exactly_seven_diagnostic_headers": global_checks[
            "exactly_seven_diagnostic_headers"
        ],
        "all_headers_are_errors": global_checks["all_headers_are_errors"],
        "no_unframed_output": global_checks["no_unframed_output"],
        "exactly_one_case_error": block is not None,
        "intended_combined_source_line": (
            block is not None
            and block["path"] == source_argument
            and block["line"] == contract["combined_exact_line"]
        ),
        "type_mismatch": (
            block is not None
            and str(block["message"]).lower().startswith("type mismatch")
        ),
        "own_witness_present_only": (
            {witness for witness in witnesses if witness in text}
            == {contract["witness"]}
        ),
        "has_actual_and_expected_types": (
            re.search(
                r"\bhas type\b[\s\S]*\bbut is expected to have type\b",
                text,
                re.IGNORECASE,
            )
            is not None
        ),
        "no_import_or_infrastructure_error": not any(
            marker in lowered for marker in NEGATIVE_CONTROL_INFRASTRUCTURE_MARKERS
        ),
        "no_malformed_source_error": not any(
            marker in lowered for marker in NEGATIVE_CONTROL_MALFORMED_MARKERS
        ),
    }


def verify_negative_controls(repo: Path, result_path: str, audit: Audit) -> dict[str, Any]:
    """Independently reclassify all seven errors from one shared Lean process."""

    if not result_path:
        raise VerificationError("negative_controls role requires semantic_result_path")
    _, contracts = reconstruct_negative_batched_source(repo)
    results = require_mapping(read_json_strict(repo / result_path), "Lean negative-control results")
    require_exact_keys(
        results,
        {
            "schema",
            "started_utc",
            "finished_utc",
            "cwd",
            "timeout_environment_variable",
            "timeout_seconds",
            "unique_cases",
            "total_process_invocations",
            "passed",
            "failed",
            "combined_source",
            "combined_source_sha256",
            "raw_diagnostic",
            "raw_diagnostic_sha256",
            "global_diagnostic_checks",
            "shared_process",
            "results",
        },
        set(),
        "Lean negative-control results",
    )
    audit.require(
        "lean_negative_controls_schema",
        results.get("schema") == NEGATIVE_CONTROL_SCHEMA,
        results.get("schema"),
        NEGATIVE_CONTROL_SCHEMA,
    )
    receipt_cwd = require_string(results.get("cwd"), "Lean negative controls.cwd")
    require_string(results.get("started_utc"), "Lean negative controls.started_utc")
    require_string(results.get("finished_utc"), "Lean negative controls.finished_utc")
    timeout_seconds = require_integer(
        results.get("timeout_seconds"), "Lean negative controls.timeout_seconds", minimum=1, maximum=3_600
    )
    audit.require(
        "lean_negative_controls_timeout_environment",
        results.get("timeout_environment_variable") == NEGATIVE_CONTROL_TIMEOUT_ENV,
        results.get("timeout_environment_variable"),
        NEGATIVE_CONTROL_TIMEOUT_ENV,
    )
    expected_summary = {
        "unique_cases": len(NEGATIVE_LEAN_CASES),
        "total_process_invocations": 1,
        "passed": len(NEGATIVE_LEAN_CASES),
        "failed": 0,
    }
    for field in expected_summary:
        require_integer(results.get(field), f"Lean negative controls.{field}", minimum=0)
    observed_summary = {field: results.get(field) for field in expected_summary}
    audit.require(
        "lean_negative_controls_exact_summary",
        observed_summary == expected_summary,
        observed_summary,
        expected_summary,
    )

    audit.require(
        "lean_negative_controls_batched_source_path",
        results.get("combined_source") == NEGATIVE_BATCHED_SOURCE,
        results.get("combined_source"),
        NEGATIVE_BATCHED_SOURCE,
    )
    actual_batched_hash = sha256(repo / NEGATIVE_BATCHED_SOURCE)
    audit.require(
        "lean_negative_controls_batched_source_hash",
        results.get("combined_source_sha256") == actual_batched_hash,
        results.get("combined_source_sha256"),
        actual_batched_hash,
    )
    audit.require(
        "lean_negative_controls_raw_path",
        results.get("raw_diagnostic") == NEGATIVE_RAW_DIAGNOSTIC,
        results.get("raw_diagnostic"),
        NEGATIVE_RAW_DIAGNOSTIC,
    )
    raw_path = repo / NEGATIVE_RAW_DIAGNOSTIC
    actual_raw_hash = sha256(raw_path)
    audit.require(
        "lean_negative_controls_raw_hash",
        results.get("raw_diagnostic_sha256") == actual_raw_hash,
        results.get("raw_diagnostic_sha256"),
        actual_raw_hash,
    )
    try:
        raw_text = raw_path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise VerificationError(f"cannot read batched raw diagnostic: {error}") from error
    raw_harness, output = parse_batched_raw_diagnostic(raw_text)
    shared_process = require_mapping(results.get("shared_process"), "shared_process")
    audit.require(
        "lean_negative_controls_shared_process_matches_raw",
        shared_process == raw_harness,
        shared_process,
        raw_harness,
    )
    argv = require_list(raw_harness.get("argv"), "shared_process.argv")
    expected_source_argument = str(Path(receipt_cwd) / PurePosixPath(NEGATIVE_BATCHED_SOURCE))
    valid_command = (
        len(argv) == 4
        and all(isinstance(item, str) and item for item in argv)
        and Path(argv[0]).name == "lake"
        and argv[1:3] == ["env", "lean"]
        and argv[3] == expected_source_argument
        and Path(argv[3]).is_absolute()
    )
    audit.require(
        "lean_negative_controls_shared_command",
        valid_command,
        argv,
        "<lake> env lean <absolute cwd/BatchedNegativeControls.lean>",
    )
    process_ok = (
        raw_harness.get("process_invocation_id") == NEGATIVE_PROCESS_INVOCATION_ID
        and raw_harness.get("cwd") == receipt_cwd
        and raw_harness.get("timeout_seconds") == timeout_seconds
        and raw_harness.get("timed_out") is False
        and type(raw_harness.get("exit_code")) is int
        and raw_harness.get("exit_code") == 1
        and raw_harness.get("spawn_error") is None
        and raw_harness.get("stderr_mode") == "STDOUT"
        and type(raw_harness.get("capture_limit_bytes")) is int
        and raw_harness.get("capture_limit_bytes") == NEGATIVE_MAX_CAPTURE_BYTES
        and raw_harness.get("output_limit_exceeded") is False
    )
    require_boolean(raw_harness.get("timed_out"), "shared_process.timed_out")
    require_boolean(
        raw_harness.get("output_limit_exceeded"),
        "shared_process.output_limit_exceeded",
    )
    require_string(raw_harness.get("started_utc"), "shared_process.started_utc")
    require_string(raw_harness.get("finished_utc"), "shared_process.finished_utc")
    elapsed = raw_harness.get("elapsed_seconds")
    if type(elapsed) not in {int, float} or elapsed < 0:
        raise VerificationError("shared_process.elapsed_seconds is invalid")
    audit.require(
        "lean_negative_controls_natural_shared_exit",
        process_ok,
        raw_harness,
        "one exact exit-1 process without timeout, truncation, or spawn failure",
    )

    preamble, blocks = split_batched_diagnostics(output)
    expected_lines = [int(value["combined_exact_line"]) for value in contracts.values()]
    stripped = LEAN_DIAGNOSTIC_HEADER_PREFIX.sub("", output).lower()
    independent_global_checks = {
        "diagnostic_utf8": True,
        "exactly_seven_diagnostic_headers": len(blocks) == len(contracts),
        "all_headers_are_errors": all(block["severity"] == "error" for block in blocks),
        "no_unframed_output": preamble.strip() == "",
        "exact_source_path_and_line_sequence": (
            [block["line"] for block in blocks] == expected_lines
            and all(block["path"] == expected_source_argument for block in blocks)
        ),
        "no_global_import_or_infrastructure_error": not any(
            marker in stripped for marker in NEGATIVE_CONTROL_INFRASTRUCTURE_MARKERS
        ),
        "no_global_malformed_source_error": not any(
            marker in stripped for marker in NEGATIVE_CONTROL_MALFORMED_MARKERS
        ),
    }
    reported_global_checks = require_mapping(
        results.get("global_diagnostic_checks"), "global_diagnostic_checks"
    )
    require_exact_keys(
        reported_global_checks,
        set(independent_global_checks),
        set(),
        "global_diagnostic_checks",
    )
    for check_name in independent_global_checks:
        require_boolean(
            reported_global_checks.get(check_name),
            f"global_diagnostic_checks.{check_name}",
        )
    audit.require(
        "lean_negative_controls_global_diagnostics",
        reported_global_checks == independent_global_checks
        and all(independent_global_checks.values()),
        reported_global_checks,
        independent_global_checks,
    )

    rows = require_list(results.get("results"), "Lean negative controls.results")
    observed_cases = [
        require_string(require_mapping(row, f"negative row {index}").get("case"), f"negative row {index}.case")
        for index, row in enumerate(rows)
    ]
    audit.require(
        "lean_negative_controls_exact_case_sequence",
        observed_cases == list(NEGATIVE_LEAN_CASES),
        observed_cases,
        list(NEGATIVE_LEAN_CASES),
    )
    blocks_by_line: dict[int, list[dict[str, Any]]] = {}
    for block in blocks:
        blocks_by_line.setdefault(int(block["line"]), []).append(block)
    witnesses = tuple(value["witness"] for value in NEGATIVE_LEAN_CASES.values())
    for index, case in enumerate(NEGATIVE_LEAN_CASES):
        row = require_mapping(rows[index], f"Lean negative-control result {case}")
        require_exact_keys(
            row,
            {
                "case",
                "source",
                "source_sha256",
                "fixture_theorem",
                "batched_theorem",
                "witness_expected_in_diagnostic",
                "fixture_exact_line",
                "combined_exact_line",
                "process_invocation_id",
                "diagnostic",
                "diagnostic_sha256",
                "diagnostic_checks",
                "attributable_rejection",
                "reason_code",
                "status",
            },
            set(),
            f"Lean negative-control result {case}",
        )
        contract = contracts[case]
        expected_row_identity = {
            "case": case,
            "source": contract["source"],
            "source_sha256": contract["sha256"],
            "fixture_theorem": contract["theorem"],
            "batched_theorem": contract["batched_theorem"],
            "witness_expected_in_diagnostic": contract["witness"],
            "fixture_exact_line": contract["fixture_exact_line"],
            "combined_exact_line": contract["combined_exact_line"],
            "process_invocation_id": NEGATIVE_PROCESS_INVOCATION_ID,
        }
        observed_row_identity = {key: row.get(key) for key in expected_row_identity}
        audit.require(
            f"lean_negative_control_identity:{case}",
            observed_row_identity == expected_row_identity,
            observed_row_identity,
            expected_row_identity,
        )
        matching = blocks_by_line.get(int(contract["combined_exact_line"]), [])
        block = matching[0] if len(matching) == 1 else None
        checks = independent_batched_case_checks(
            block,
            contract,
            expected_source_argument,
            witnesses,
            independent_global_checks,
        )
        reported_checks = require_mapping(row.get("diagnostic_checks"), f"checks {case}")
        require_exact_keys(
            reported_checks,
            set(NEGATIVE_CONTROL_DIAGNOSTIC_CHECKS),
            set(),
            f"checks {case}",
        )
        for check_name in NEGATIVE_CONTROL_DIAGNOSTIC_CHECKS:
            require_boolean(
                reported_checks.get(check_name),
                f"checks {case}.{check_name}",
            )
        diagnostic_path_expected = (
            f"{EXP_ROOT}/controls/lean/rejection_diagnostics/{case}.rejection.log"
        )
        audit.require(
            f"lean_negative_control_diagnostic_path:{case}",
            row.get("diagnostic") == diagnostic_path_expected,
            row.get("diagnostic"),
            diagnostic_path_expected,
        )
        case_log_path = repo / diagnostic_path_expected
        case_hash = sha256(case_log_path)
        try:
            case_text = case_log_path.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeError) as error:
            raise VerificationError(f"cannot read case diagnostic {case!r}: {error}") from error
        reference, derived_block = parse_batched_case_log(case_text, case)
        expected_reference = {
            "case": case,
            "process_invocation_id": NEGATIVE_PROCESS_INVOCATION_ID,
            "raw_diagnostic": NEGATIVE_RAW_DIAGNOSTIC,
            "raw_diagnostic_sha256": actual_raw_hash,
        }
        independently_attributable = (
            process_ok
            and all(independent_global_checks.values())
            and all(checks.values())
            and reported_checks == checks
            and block is not None
            and derived_block == block["text"]
            and reference == expected_reference
            and row.get("diagnostic_sha256") == case_hash
            and row.get("reason_code") == NEGATIVE_CONTROL_SUCCESS_REASON
            and row.get("status") == "PASS"
            and row.get("attributable_rejection") is True
        )
        audit.require(
            f"lean_negative_control_attributable:{case}",
            independently_attributable,
            {
                "checks": reported_checks,
                "reference": reference,
                "diagnostic_sha256": row.get("diagnostic_sha256"),
                "reason_code": row.get("reason_code"),
                "status": row.get("status"),
            },
            "one exact independently reclassified type mismatch from shared exit-1 process",
        )
    return {"path": result_path, **expected_summary}


def verify_production_forbidden_tokens(
    repo: Path,
    archive_files: dict[str, dict[str, Any]],
    tokens_value: list[Any],
    audit: Audit,
) -> dict[str, Any]:
    tokens: list[str] = []
    for index, value in enumerate(tokens_value):
        token = require_string(value, f"lean_evidence.forbidden_tokens[{index}]")
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", token) is None:
            raise VerificationError(f"unsupported forbidden token spelling: {token!r}")
        tokens.append(token)
    if tuple(tokens) != DEFAULT_FORBIDDEN_TOKENS:
        raise VerificationError(
            f"forbidden token contract must remain exactly {list(DEFAULT_FORBIDDEN_TOKENS)!r}"
        )
    matches: list[dict[str, Any]] = []
    for relative in PRODUCTION_LEAN_SOURCES:
        if relative not in archive_files:
            raise VerificationError(f"production Lean source missing from archive/tree/manifest: {relative!r}")
        text = (repo / relative).read_text(encoding="utf-8", errors="strict")
        for token in tokens:
            pattern = re.compile(rf"(?<![A-Za-z0-9_.]){re.escape(token)}(?![A-Za-z0-9_.])")
            for match in pattern.finditer(text):
                matches.append(
                    {
                        "path": relative,
                        "token": token,
                        "line": text.count("\n", 0, match.start()) + 1,
                    }
                )
    audit.require("production_forbidden_token_scan", not matches, matches, [])
    return {"files": list(PRODUCTION_LEAN_SOURCES), "tokens": tokens, "matches": matches}


def verify_receipt_contract(
    receipt: dict[str, Any],
    contract: dict[str, Any],
    context: dict[str, Any],
    audit: Audit,
) -> dict[str, Any]:
    require_exact_keys(
        contract,
        {
            "schema_field",
            "schema_value",
            "status_field",
            "external_review_field",
            "bindings",
            "expectations",
        },
        set(),
        "receipt_contract",
    )
    schema_field = require_string(contract["schema_field"], "receipt_contract.schema_field")
    schema_value = require_string(contract["schema_value"], "receipt_contract.schema_value")
    status_field = require_string(contract["status_field"], "receipt_contract.status_field")
    external_review_field = require_string(
        contract["external_review_field"], "receipt_contract.external_review_field"
    )
    audit.require("remote_receipt_schema", dotted_get(receipt, schema_field, "remote receipt") == schema_value,
                  dotted_get(receipt, schema_field, "remote receipt"), schema_value)
    audit.require("remote_receipt_status", dotted_get(receipt, status_field, "remote receipt") == "PASS",
                  dotted_get(receipt, status_field, "remote receipt"), "PASS")
    audit.require(
        "remote_receipt_external_review_pending",
        dotted_get(receipt, external_review_field, "remote receipt") == "PENDING",
        dotted_get(receipt, external_review_field, "remote receipt"),
        "PENDING",
    )
    expectations = require_mapping(contract["expectations"], "receipt_contract.expectations")
    for field, expected in expectations.items():
        observed = dotted_get(receipt, field, "remote receipt")
        audit.require(f"remote_receipt_expectation:{field}", observed == expected, observed, expected)
    bindings = require_mapping(contract["bindings"], "receipt_contract.bindings")
    required_sources = {
        "archive_sha256",
        "bundle_sha256",
        "commit",
        "tag",
        "tag_object",
        "manifest_sha256",
        "manifest_entries",
    }
    observed_sources = set(bindings.values())
    audit.require(
        "remote_receipt_required_binding_sources",
        required_sources <= observed_sources,
        sorted(observed_sources),
        sorted(required_sources),
    )
    for field, source in bindings.items():
        source = require_string(source, f"receipt binding source for {field}")
        if source not in context:
            raise VerificationError(f"receipt binding {field!r} names unknown context value {source!r}")
        observed = dotted_get(receipt, field, "remote receipt")
        expected = context[source]
        audit.require(f"remote_receipt_binding:{field}", observed == expected, observed, expected)
    return {"schema": schema_value, "binding_count": len(bindings), "expectation_count": len(expectations)}


def verify_exp001(
    exp001: dict[str, Any],
    final_clone: Path,
    final_commit: str,
    audit: Audit,
) -> dict[str, Any]:
    require_exact_keys(
        exp001,
        {"archive", "bundle", "tag", "tag_object", "commit", "subtree_ids", "pin_blob_ids", "additional_files"},
        set(),
        "exp001",
    )
    external: dict[str, dict[str, Any]] = {}
    for role in ("archive", "bundle"):
        descriptor = require_mapping(exp001[role], f"exp001.{role}")
        require_exact_keys(descriptor, {"path", "sha256"}, set(), f"exp001.{role}")
        path = ensure_regular_no_links(Path(require_string(descriptor["path"], f"exp001.{role}.path")), f"Exp001 {role}")
        expected = require_sha(descriptor["sha256"], f"exp001.{role}.sha256")
        actual = sha256(path)
        audit.require(f"exp001_external_hash:{role}", actual == expected, actual, expected)
        external[role] = {"path": str(path), "sha256": actual, "size_bytes": path.stat().st_size}
    auxiliary = require_list(exp001["additional_files"], "exp001.additional_files")
    for index, value in enumerate(auxiliary):
        descriptor = require_mapping(value, f"exp001.additional_files[{index}]")
        require_exact_keys(descriptor, {"label", "path", "sha256"}, set(), f"exp001.additional_files[{index}]")
        label = require_string(descriptor["label"], f"exp001.additional_files[{index}].label")
        if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", label) is None:
            raise VerificationError(f"unsafe Exp001 additional-file label: {label!r}")
        path = ensure_regular_no_links(Path(require_string(descriptor["path"], f"{label}.path")), label)
        expected = require_sha(descriptor["sha256"], f"{label}.sha256")
        actual = sha256(path)
        audit.require(f"exp001_additional_hash:{label}", actual == expected, actual, expected)
        external[label] = {"path": str(path), "sha256": actual, "size_bytes": path.stat().st_size}

    original_bundle_verify = audit.output / "exp001_bundle_verify.git"
    audit.run("exp001_git_init_bare", ["git", "init", "--bare", str(original_bundle_verify)], cwd=audit.output)
    audit.run(
        "exp001_git_bundle_verify",
        ["git", "-C", str(original_bundle_verify), "bundle", "verify", external["bundle"]["path"]],
        cwd=audit.output,
    )

    tag = require_string(exp001["tag"], "exp001.tag")
    if SAFE_REF.fullmatch(tag) is None or tag.startswith("-") or ".." in tag or "//" in tag:
        raise VerificationError("exp001.tag is not a restricted safe ref name")
    tag_object = require_git_object(exp001["tag_object"], "exp001.tag_object")
    commit = require_git_object(exp001["commit"], "exp001.commit")
    observed_tag = git_text(audit, "exp001_resolve_tag_object", final_clone, "rev-parse", tag)
    observed_commit = git_text(audit, "exp001_resolve_tag_commit", final_clone, "rev-parse", f"{tag}^{{commit}}")
    observed_type = git_text(audit, "exp001_tag_type", final_clone, "cat-file", "-t", tag)
    audit.require("exp001_tag_is_annotated", observed_type == "tag", observed_type, "tag")
    audit.require("exp001_tag_object", observed_tag == tag_object, observed_tag, tag_object)
    audit.require("exp001_tag_commit", observed_commit == commit, observed_commit, commit)

    subtree_ids = require_mapping(exp001["subtree_ids"], "exp001.subtree_ids")
    pin_blob_ids = require_mapping(exp001["pin_blob_ids"], "exp001.pin_blob_ids")
    if not subtree_ids or not pin_blob_ids:
        raise VerificationError("Exp001 subtree_ids and pin_blob_ids must both be nonempty")
    verified_objects: dict[str, str] = {}
    for expected_type, mapping in (("tree", subtree_ids), ("blob", pin_blob_ids)):
        for raw_path, raw_object in mapping.items():
            path = canonical_relative(raw_path, f"exp001 {expected_type} path", 16_384)
            expected_object = require_git_object(raw_object, f"exp001 object {path}")
            at_exp001 = git_text(
                audit,
                f"exp001_{expected_type}_at_original_{path}",
                final_clone,
                "rev-parse",
                f"{commit}:{path}",
            )
            at_final = git_text(
                audit,
                f"exp001_{expected_type}_at_final_{path}",
                final_clone,
                "rev-parse",
                f"{final_commit}:{path}",
            )
            object_type = git_text(
                audit,
                f"exp001_{expected_type}_type_{path}",
                final_clone,
                "cat-file",
                "-t",
                expected_object,
            )
            audit.require(f"exp001_object_original:{path}", at_exp001 == expected_object, at_exp001, expected_object)
            audit.require(f"exp001_object_final:{path}", at_final == expected_object, at_final, expected_object)
            audit.require(f"exp001_object_type:{path}", object_type == expected_type, object_type, expected_type)
            verified_objects[path] = expected_object
    return {
        "external_files": external,
        "tag": tag,
        "tag_object": tag_object,
        "commit": commit,
        "immutable_objects": verified_objects,
    }


def example_spec() -> dict[str, Any]:
    placeholder = "0" * 64
    role = lambda metadata, bindings, *, semantic=None, text=None: {
        "metadata_path": metadata,
        "metadata_sha256": placeholder,
        "hash_bindings": bindings,
        "required_text": text or {},
        **({"semantic_result_path": semantic} if semantic else {}),
    }
    return {
        "schema": SPEC_SCHEMA,
        "delivery": {
            "archive_path": "/ABS/PATH/NDEA_Evolve_exp002_final.tar.gz",
            "bundle_path": "/ABS/PATH/NDEA_Evolve_exp002_final.bundle",
            "receipt_path": "/ABS/PATH/remote_exp002_final_receipt.json",
            "output_directory": "/ABS/PATH/local_verification_UNIQUE",
            "archive_sha256": placeholder,
            "bundle_sha256": placeholder,
            "receipt_sha256": placeholder,
            "archive_root": "NDEA_Evolve",
        },
        "repository": {
            "commit": "0" * 40,
            "tag": "exp002-operator-cayley-unitarity-verified-final-YYYYMMDD",
            "tag_object": "0" * 40,
            "branch": "exp002-operator-cayley-unitarity",
        },
        "manifest": {
            "path": f"{EXP_ROOT}/FINAL_SHA256SUMS",
            "expected_sha256": placeholder,
            "expected_entries": 1,
        },
        "pins": {
            "lean_toolchain": "leanprover/lean4:v4.31.0",
            "lean_version": "4.31.0",
            "mathlib_revision": "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
            "mathlib_input_revision": "v4.31.0",
        },
        "julia": {
            "validator_sha256": "216caca1a473a6edcabe6d8df6d6f9677ca180d2d634152b2c89a0fea41c6ba2",
            "certificate_sha256": "a80cfd44b43e69131c7e5e63576362767b8ca6a4406e1c7c4ccc83edfa0c4120",
            "run_receipt_sha256": "789b42b88016f50c056fb38934c9a02e702eb4680cd577fd550351a5357bb5b8",
            "regression_driver_sha256": "a533860179f3c32f62564199a4805f54036856e7188fd34a26929c1f3c0508d0",
            "direct_check_count": 530,
            "timeout_seconds": 300,
        },
        "lean_evidence": {
            "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "forbidden_tokens": list(DEFAULT_FORBIDDEN_TOKENS),
            "roles": {
                "production_build": role(
                    f"{EXP_ROOT}/metadata/final_production_build.json",
                    {
                        "timing_sha256": f"{EXP_ROOT}/metadata/final_production_build_command.json",
                        "log_sha256": f"{EXP_ROOT}/logs/final_verbose_production_build.log",
                        "operator_source_sha256": PRODUCTION_LEAN_SOURCES[0],
                        "witness_source_sha256": PRODUCTION_LEAN_SOURCES[1],
                    },
                    text={
                        f"{EXP_ROOT}/logs/final_verbose_production_build.log": {
                            "contains": ["Build completed successfully"],
                            "absent": ["error:", "warning:", "SIGINT", "interrupted"],
                        }
                    },
                ),
                "positive_witness": role(
                    f"{EXP_ROOT}/metadata/final_positive_witness.json",
                    {
                        "timing_sha256": f"{EXP_ROOT}/metadata/final_positive_witness_command.json",
                        "log_sha256": f"{EXP_ROOT}/logs/final_positive_witness.log",
                        "witness_source_sha256": PRODUCTION_LEAN_SOURCES[1],
                    },
                    text={
                        f"{EXP_ROOT}/logs/final_positive_witness.log": {
                            "contains": ["Build completed successfully"],
                            "absent": ["error:", "SIGINT", "interrupted"],
                        }
                    },
                ),
                "axiom_audit": role(
                    f"{EXP_ROOT}/metadata/final_axiom_audit.json",
                    {
                        "timing_sha256": f"{EXP_ROOT}/metadata/final_axiom_audit_command.json",
                        "audit_source_sha256": f"{EXP_ROOT}/assurance/PrintAndAxiomAudit.lean",
                        "log_sha256": f"{EXP_ROOT}/logs/final_axiom_audit.log",
                        "result_sha256": f"{EXP_ROOT}/assurance/final_axiom_audit_results.json",
                    },
                    semantic=f"{EXP_ROOT}/assurance/final_axiom_audit_results.json",
                ),
                "negative_controls": role(
                    f"{EXP_ROOT}/metadata/final_negative_controls.json",
                    {
                        "timing_sha256": f"{EXP_ROOT}/metadata/final_negative_controls_command.json",
                        "log_sha256": f"{EXP_ROOT}/logs/final_negative_controls.log",
                        "runner_sha256": f"{EXP_ROOT}/controls/lean/run_negative_controls.py",
                        "batched_source_sha256": NEGATIVE_BATCHED_SOURCE,
                        "raw_diagnostic_sha256": NEGATIVE_RAW_DIAGNOSTIC,
                        "result_sha256": f"{EXP_ROOT}/controls/lean/rejection_diagnostics/results.json",
                        **{
                            f"source_hashes.{index}.sha256": value["source"]
                            for index, value in enumerate(NEGATIVE_LEAN_CASES.values(), 1)
                        },
                    },
                    semantic=f"{EXP_ROOT}/controls/lean/rejection_diagnostics/results.json",
                ),
                "forbidden_scan": role(
                    f"{EXP_ROOT}/metadata/final_forbidden_scan.json",
                    {
                        "timing_sha256": f"{EXP_ROOT}/metadata/final_forbidden_scan_command.json",
                        "log_sha256": f"{EXP_ROOT}/logs/final_forbidden_scan.log",
                        "result_sha256": f"{EXP_ROOT}/assurance/final_forbidden_scan.json",
                        "operator_source_sha256": PRODUCTION_LEAN_SOURCES[0],
                        "witness_source_sha256": PRODUCTION_LEAN_SOURCES[1],
                    },
                ),
            },
        },
        "receipt_contract": {
            "schema_field": "schema",
            "schema_value": "ndea.exp002.final_delivery.v1",
            "status_field": "overall_status",
            "external_review_field": "external_review",
            "expectations": {},
            "bindings": {
                "artifacts.archive.sha256": "archive_sha256",
                "artifacts.bundle.sha256": "bundle_sha256",
                "repository.commit": "commit",
                "repository.tag": "tag",
                "repository.tag_object": "tag_object",
                "internal_manifest.sha256": "manifest_sha256",
                "internal_manifest.entries": "manifest_entries",
            },
        },
        "exp001": {
            "archive": {
                "path": "/home/richman954/NDEA_Evolve_offruntime/exp001/final/NDEA_Evolve_exp001_final_evidence.tar.gz",
                "sha256": "131a89fc12a0f7ae71011c50af7e359fd9c3f8ebbb974c982f77f9309c4127aa",
            },
            "bundle": {
                "path": "/home/richman954/NDEA_Evolve_offruntime/exp001/final/NDEA_Evolve_exp001_final.bundle",
                "sha256": "10dc27fd1046a419358a92565fe59e1ae40414c9c5692c9afd3b016bce7540c1",
            },
            "tag": "exp001-fourier-stability-verified-final-20260905",
            "tag_object": "6526b9414207c3becc2b01db7ebce1f5ee482494",
            "commit": "a88a3fb141d63b460a5d19d2e33f2a76f05101f2",
            "subtree_ids": {
                "NDEAEvolve/Experiments/Exp001": "c3f74e21f1882e0aa73fbe71a985aca9f2794cab",
                "experiments/exp001_fourier_stability": "0e6e91fa06a526d654d040b182abf0b1435d7f07",
            },
            "pin_blob_ids": {
                "lean-toolchain": "18640c8b066b182147f324d3aefd8ee48ee45238",
                "lakefile.toml": "a62e22edd1ccbf3eda0514bc3c4c8901c29411b5",
                "lake-manifest.json": "9d7e58f96268bd595a19b05dc0da88b35edaa2b6",
            },
            "additional_files": [
                {
                    "label": "exp001_assurance_v2_archive",
                    "path": "/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/Exp001_Assurance_Hardening_v2_evidence.tar.gz",
                    "sha256": "3f460ecd7f88de93bc403ae2371601686a083dcba911b05f6784464114f719be",
                },
                {
                    "label": "exp001_assurance_v2_bundle",
                    "path": "/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/Exp001_Assurance_Hardening_v2.bundle",
                    "sha256": "fb8cb79fc574522fdb142b348b50637087c75e582f437ed19531260546ad5257",
                },
                {
                    "label": "exp001_assurance_v2_local_receipt",
                    "path": "/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/local_v2_delivery_verification.json",
                    "sha256": "62a02d08b0dcb873ffba905622803e2e27ce7dd6695bf8a4f426391d8e466556",
                },
            ],
        },
        "limits": {
            "max_archive_bytes": 2_147_483_648,
            "max_members": 10_000,
            "max_file_bytes": 268_435_456,
            "max_total_bytes": 1_073_741_824,
            "max_path_bytes": 4_096,
            "command_timeout_seconds": 600,
        },
    }


def perform_verification(spec_path: Path, spec_sha256: str, spec: dict[str, Any]) -> int:
    validate_spec(spec)
    limits = parse_limits(spec)
    delivery = require_mapping(spec["delivery"], "delivery")
    require_exact_keys(
        delivery,
        {
            "archive_path",
            "bundle_path",
            "receipt_path",
            "output_directory",
            "archive_sha256",
            "bundle_sha256",
            "receipt_sha256",
            "archive_root",
        },
        set(),
        "delivery",
    )
    archive = ensure_regular_no_links(Path(require_string(delivery["archive_path"], "delivery.archive_path")), "final archive")
    bundle = ensure_regular_no_links(Path(require_string(delivery["bundle_path"], "delivery.bundle_path")), "final bundle")
    remote_receipt_path = ensure_regular_no_links(
        Path(require_string(delivery["receipt_path"], "delivery.receipt_path")), "remote final receipt"
    )
    repository_spec = require_mapping(spec["repository"], "repository")
    expected_git_commit = require_git_object(repository_spec.get("commit"), "repository.commit")
    output = Path(require_string(delivery["output_directory"], "delivery.output_directory"))
    if not output.is_absolute() or output.exists():
        raise VerificationError("delivery.output_directory must be an absolute path that does not exist")
    parent = output.parent
    if not parent.is_dir() or parent.resolve(strict=True) != Path(os.path.abspath(parent)):
        raise VerificationError("delivery.output_directory parent must be an existing canonical non-link directory")
    output.mkdir(parents=False, exist_ok=False)
    os.chmod(output, 0o700)
    audit = Audit(output, limits["command_timeout_seconds"])
    failure: dict[str, Any] | None = None
    details: dict[str, Any] = {}
    try:
        audit.require(
            "spec_hash_stable_at_start",
            sha256(spec_path) == spec_sha256,
            sha256(spec_path),
            spec_sha256,
        )
        audit.require(
            "compressed_archive_size_bound",
            archive.stat().st_size <= limits["max_archive_bytes"],
            archive.stat().st_size,
            f"<= {limits['max_archive_bytes']}",
        )
        expected_outer = {
            "archive": require_sha(delivery["archive_sha256"], "delivery.archive_sha256"),
            "bundle": require_sha(delivery["bundle_sha256"], "delivery.bundle_sha256"),
            "receipt": require_sha(delivery["receipt_sha256"], "delivery.receipt_sha256"),
        }
        actual_outer = {
            "archive": sha256(archive),
            "bundle": sha256(bundle),
            "receipt": sha256(remote_receipt_path),
        }
        for role in expected_outer:
            audit.require(f"outer_hash:{role}", actual_outer[role] == expected_outer[role], actual_outer[role], expected_outer[role])
        details["outer_artifacts"] = {
            "archive": {"path": str(archive), "sha256": actual_outer["archive"], "size_bytes": archive.stat().st_size},
            "bundle": {"path": str(bundle), "sha256": actual_outer["bundle"], "size_bytes": bundle.stat().st_size},
            "remote_receipt": {"path": str(remote_receipt_path), "sha256": actual_outer["receipt"], "size_bytes": remote_receipt_path.stat().st_size},
        }

        archive_root = require_string(delivery["archive_root"], "delivery.archive_root")
        canonical_relative(archive_root, "delivery.archive_root", limits["max_path_bytes"])
        if "/" in archive_root:
            raise VerificationError("delivery.archive_root must be exactly one path component")
        scanned = scan_tar(archive, archive_root, expected_git_commit, limits)
        audit.require("archive_safe_bounded_member_scan", True, len(scanned), f"<= {limits['max_members']}")
        extraction = output / "extracted"
        extracted_members = extract_tar_safely(archive, extraction, scanned)
        repo = extraction / archive_root
        archive_files = {
            name[len(archive_root) + 1 :]: metadata
            for name, metadata in extracted_members.items()
            if name.startswith(archive_root + "/")
        }
        audit.require("archive_safe_extraction_file_count", len(archive_files) == len(extracted_members), len(archive_files), len(extracted_members))
        audit.require("archive_hash_stable_after_extraction", sha256(archive) == actual_outer["archive"], sha256(archive), actual_outer["archive"])
        details["safe_extraction"] = {
            "root": str(repo),
            "member_count": len(scanned),
            "regular_file_count": len(archive_files),
            "expanded_regular_bytes": sum(value["size"] for value in archive_files.values()),
            "links_or_special_entries": 0,
        }

        manifest = verify_manifest(
            repo,
            archive_files,
            require_mapping(spec["manifest"], "manifest"),
            limits["max_path_bytes"],
            audit,
        )
        details["manifest"] = manifest
        details["historical_manifests"] = verify_historical_manifests(
            repo,
            archive_files,
            limits["max_path_bytes"],
            audit,
        )

        final_clone, repository = verify_git_bundle_and_tree(
            bundle,
            repo,
            archive_files,
            repository_spec,
            limits,
            audit,
        )
        details["repository"] = repository
        pins = verify_pins(repo, require_mapping(spec["pins"], "pins"), audit)
        details["pins"] = pins

        role_records = verify_evidence_roles(
            repo,
            archive_files,
            require_mapping(spec["lean_evidence"], "lean_evidence"),
            pins,
            limits,
            audit,
        )
        lean_spec = require_mapping(spec["lean_evidence"], "lean_evidence")
        axiom = verify_axiom_audit(
            repo,
            role_records["axiom_audit"]["semantic_result_path"],
            role_records["axiom_audit"]["log_path"],
            require_list(lean_spec["allowed_axioms"], "lean_evidence.allowed_axioms"),
            audit,
        )
        negative = verify_negative_controls(
            repo,
            role_records["negative_controls"]["semantic_result_path"],
            audit,
        )
        forbidden = verify_production_forbidden_tokens(
            repo,
            archive_files,
            require_list(lean_spec["forbidden_tokens"], "lean_evidence.forbidden_tokens"),
            audit,
        )
        details["lean_evidence"] = {
            "roles": role_records,
            "axiom_audit": axiom,
            "negative_controls": negative,
            "forbidden_scan": forbidden,
            "boundary": "Evidence bytes and recorded results verified; Lean kernel replay is not performed by this verifier.",
        }

        replay_repo = output / "fresh_python_replay" / archive_root
        replay_repo.parent.mkdir(parents=True, exist_ok=False)
        julia_result = verify_julia_regression(
            repo,
            replay_repo,
            require_mapping(spec["julia"], "julia"),
            audit,
        )
        details["julia_validator_replay"] = julia_result

        exp001 = verify_exp001(
            require_mapping(spec["exp001"], "exp001"),
            final_clone,
            repository["commit"],
            audit,
        )
        details["exp001_sentinels"] = exp001

        receipt = require_mapping(read_json_strict(remote_receipt_path), "remote final receipt")
        receipt_context = {
            "archive_sha256": actual_outer["archive"],
            "bundle_sha256": actual_outer["bundle"],
            "commit": repository["commit"],
            "tag": repository["tag"],
            "tag_object": repository["tag_object"],
            "manifest_sha256": manifest["sha256"],
            "manifest_entries": manifest["entries"],
        }
        details["remote_receipt_contract"] = verify_receipt_contract(
            receipt,
            require_mapping(spec["receipt_contract"], "receipt_contract"),
            receipt_context,
            audit,
        )

        # Verify the immutable extraction one final time after all replay work.
        for relative, expected in archive_files.items():
            if sha256(repo / relative) != expected["sha256"]:
                raise VerificationError(f"verified extraction changed during audit: {relative!r}")
        audit.require("verified_extraction_remained_immutable", True, len(archive_files), len(archive_files))
        audit.require("outer_archive_hash_stable", sha256(archive) == actual_outer["archive"], sha256(archive), actual_outer["archive"])
        audit.require("outer_bundle_hash_stable", sha256(bundle) == actual_outer["bundle"], sha256(bundle), actual_outer["bundle"])
        audit.require("outer_receipt_hash_stable", sha256(remote_receipt_path) == actual_outer["receipt"], sha256(remote_receipt_path), actual_outer["receipt"])
        audit.require("spec_hash_stable_at_end", sha256(spec_path) == spec_sha256, sha256(spec_path), spec_sha256)
    except Exception as error:  # Preserve attributable failure evidence in the new output directory.
        failure = {
            "type": type(error).__name__,
            "message": str(error),
            "traceback": traceback.format_exc(),
        }

    overall = failure is None and all(item["pass"] for item in audit.checks)
    verifier_path = Path(__file__).resolve()
    local_receipt = {
        "schema": RECEIPT_SCHEMA,
        "created_utc": utc_now(),
        "overall_status": "PASS" if overall else "FAIL",
        "verification_host_role": "local off-runtime fresh-extraction verifier",
        "spec": {"path": str(spec_path), "sha256": spec_sha256},
        "verifier": {"path": str(verifier_path), "sha256": sha256(verifier_path)},
        "checks_passed": sum(item["pass"] for item in audit.checks),
        "checks_total": len(audit.checks),
        "checks": audit.checks,
        "commands": audit.commands,
        "details": details,
        "failure": failure,
        "external_review": "PENDING",
        "causal_boundary": "This receipt is adjacent to, not inside, the frozen archive and bundle.",
        "limitations": [
            "This verifier does not rerun Lean; it verifies Git/manifest-bound Lean sources, logs, metadata, controls, signatures, and axiom reports.",
            "The exact Julia certificate is checked by the independent Python validator; Julia itself is not rerun.",
            "Authenticity ultimately depends on independently preserving and reviewing the JSON specification and its expected hashes/revision.",
            "Python replay is process-bounded and environment-isolated but is not an operating-system sandbox.",
            "Captured child-process output is timeout-bounded but does not currently have an independent byte ceiling.",
            "Outer files are re-hashed after use, but this draft does not hold one O_NOFOLLOW file descriptor across hash, parse, and replay; it is not hardened against a concurrent swap-and-restore attacker.",
        ],
    }
    receipt_path = output / "local_final_delivery_verification.json"
    receipt_path.write_text(json.dumps(local_receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"LOCAL_RECEIPT={receipt_path}")
    print(f"LOCAL_RECEIPT_SHA256={sha256(receipt_path)}")
    print(f"EXP002_FINAL_LOCAL_VERIFICATION_STATUS={'PASS' if overall else 'FAIL'}")
    return 0 if overall else 1


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--spec", type=Path, help="absolute path to the independently frozen JSON specification")
    group.add_argument(
        "--print-example-spec",
        action="store_true",
        help="print a complete specification template to stdout and exit",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.print_example_spec:
        print(json.dumps(example_spec(), indent=2, sort_keys=True))
        return 0
    require_linux_posix()
    raw_spec = args.spec
    if not raw_spec.is_absolute():
        raise VerificationError("--spec must be an absolute path")
    spec_path = ensure_regular_no_links(raw_spec, "verification specification")
    spec_hash = sha256(spec_path)
    spec = require_mapping(read_json_strict(spec_path), "verification specification")
    return perform_verification(spec_path, spec_hash, spec)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except VerificationError as error:
        print(f"EXP002_FINAL_LOCAL_VERIFICATION_STATUS=FAIL\nERROR={error}", file=sys.stderr)
        raise SystemExit(2)
