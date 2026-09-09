#!/usr/bin/env python3
"""Run the two frozen false Exp003 Lean controls in one strict process.

The runner is deliberately fail closed. It reconstructs the batch from two
hash-pinned fixtures, refuses to overwrite evidence, invokes Lean exactly once,
and accepts only two proposition-level type mismatches on the corresponding
``exact`` lines. Import, syntax, elaboration, tactic, timeout, truncation, and
source-race failures are never classified as mathematical rejections.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
SOURCES = HERE / "rejected_sources"
BATCHED_SOURCE = HERE / "BatchedNegativeControls.lean"
DIAGNOSTICS = HERE / "rejection_diagnostics"
RAW_DIAGNOSTIC = DIAGNOSTICS / "batched_negative_controls.raw.log"
RESULTS_PATH = DIAGNOSTICS / "results.json"
RECEIPT_PATH = DIAGNOSTICS / "execution_receipt.json"
RUNNER_PATH = Path(__file__).resolve()

LAKE = os.environ.get("NDEA_LAKE") or shutil.which("lake")
TIMEOUT_ENV = "NDEA_EXP003_NEGATIVE_CONTROL_TIMEOUT_SECONDS"
DEFAULT_TIMEOUT_SECONDS = 900
MAX_TIMEOUT_SECONDS = 3_600
TIMEOUT_TERMINATION_GRACE_SECONDS = 5
MAX_CAPTURE_BYTES = 16 * 1024 * 1024
PROCESS_INVOCATION_ID = "exp003-lean-batched-negative-controls-001"

IMPORT_LINE = "import NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction"
OPEN_LINES = (
    "open NDEAEvolve.Exp002",
    "open NDEAEvolve.Exp003.AdversarialWitnesses",
)
NAMESPACE_LINE = "namespace NDEAEvolve.Exp003.NegativeControls"
FIXTURE_PREAMBLE = IMPORT_LINE + "\n\n" + "\n".join(OPEN_LINES) + "\n\n"
BATCHED_PREAMBLE = f"""{IMPORT_LINE}

/-!
Resource-bounded execution driver for the two frozen false controls.

Each theorem body and target below is reconstructed byte-for-byte from a
hash-pinned rejected fixture, apart from the theorem-name suffix. Keeping both
commands in one Lean process shares the large `Mathlib` import while still
requiring two distinct, attributable type-mismatch diagnostics. This file is
assurance input and is never a production module.
-/

{NAMESPACE_LINE}

{OPEN_LINES[0]}
{OPEN_LINES[1]}

"""
BATCHED_EPILOGUE = f"\nend {NAMESPACE_LINE.removeprefix('namespace ')}\n"

# filename, frozen SHA-256, fixture theorem, batched theorem, negation witness
CASES = (
    (
        "01_strict_bound_false.lean",
        "e7ac7dc50842eb2930702589d800f1e682a0de6c246e7efdab7e0a5f044adefe",
        "false_strict_resolvent_contraction",
        "false_strict_resolvent_contraction_batched",
        "zero_generator_not_strict_contraction",
    ),
    (
        "02_dropped_hermiticity_false.lean",
        "a21c79c5faf2346023143659df34c892f7e786eec716432cba3781bbc6f0ed8b",
        "false_resolvent_nonexpansive_without_hermiticity",
        "false_resolvent_nonexpansive_without_hermiticity_batched",
        "nonhermitian_resolvent_not_nonexpansive",
    ),
)

# These are not hard-coded to development hashes. Their exact identities are
# captured before and after Lean so the receipt binds the positive source that
# generated the rejection while rejecting a concurrent source change.
BOUND_INPUTS = (
    REPO / "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean",
    REPO / "lean-toolchain",
    REPO / "lake-manifest.json",
)
CONTROL_INPUTS = (
    RUNNER_PATH,
    BATCHED_SOURCE,
    *(SOURCES / case[0] for case in CASES),
)

DIAGNOSTIC_HEADER = re.compile(
    r"^(?P<path>.+):(?P<line>[0-9]+):(?P<column>[0-9]+):[ \t]+"
    r"(?P<severity>error|warning|information):[ \t]*(?P<message>.*)$",
    re.IGNORECASE | re.MULTILINE,
)
DIAGNOSTIC_HEADER_PREFIX = re.compile(
    r"^.+:[0-9]+:[0-9]+:[ \t]+(?:error|warning|information):[ \t]*",
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
TACTIC_OR_ELABORATION_MARKERS = (
    "tactic '",
    "tactic failed",
    "unsolved goals",
    "no goals to be solved",
    "failed to synthesize",
    "invalid field notation",
    "declaration uses 'sorry'",
)
FORBIDDEN_FIXTURE_TOKENS = re.compile(
    r"(?m)^\s*(?:sorry|admit|axiom|unsafe\b)|\bnative_decide\b"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def file_identity(path: Path) -> dict[str, object]:
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"required bound input is not a regular file: {path}")
    return {
        "path": str(path.relative_to(REPO)),
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    }


def snapshot_bound_inputs() -> list[dict[str, object]]:
    return [file_identity(path) for path in BOUND_INPUTS]


def snapshot_control_inputs() -> list[dict[str, object]]:
    return [file_identity(path) for path in CONTROL_INPUTS]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def timeout_seconds() -> int:
    raw = os.environ.get(TIMEOUT_ENV)
    if raw is None:
        return DEFAULT_TIMEOUT_SECONDS
    if re.fullmatch(r"[1-9][0-9]*", raw) is None or int(raw) > MAX_TIMEOUT_SECONDS:
        raise SystemExit(
            f"{TIMEOUT_ENV} must be a canonical integer from 1 to "
            f"{MAX_TIMEOUT_SECONDS}"
        )
    return int(raw)


def write_exclusive(path: Path, text: str) -> None:
    """Atomically create ``path`` and refuse every pre-existing target."""

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent, prefix=f".{path.name}.", suffix=".tmp"
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError as error:
            raise RuntimeError(f"refusing to overwrite pre-existing evidence: {path}") from error
    finally:
        temporary.unlink(missing_ok=True)


def make_acceptance_contract(
    *,
    exit_code: int,
    process_invocations: int,
    passed: int,
    failed: int,
    global_checks: dict[str, bool],
) -> dict[str, bool]:
    """Return scalar, fail-closed predicates for the execution receipt.

    The full named diagnostic-predicate mapping is preserved in the semantic
    results. Receipt predicates are booleans so both release verifiers can
    enforce the contract uniformly.
    """

    return {
        "natural_lean_exit_code": exit_code == 1,
        "one_lean_invocation": process_invocations == 1,
        "two_attributable_type_mismatches": failed == 0 and passed == 2,
        "global_diagnostic_checks": all(global_checks.values()),
        "exclusive_create_no_overwrite": True,
    }


def reconstruct() -> list[dict[str, object]]:
    """Verify fixtures and require the checked-in batch to be their exact image."""

    payloads: list[str] = []
    contracts: list[dict[str, object]] = []
    for filename, expected_hash, theorem, batched_theorem, witness in CASES:
        source = SOURCES / filename
        text = source.read_text(encoding="utf-8", errors="strict")
        observed_hash = sha256(source)
        if observed_hash != expected_hash:
            raise RuntimeError(
                f"frozen fixture hash mismatch: {source}: "
                f"expected {expected_hash}, observed {observed_hash}"
            )
        if not text.startswith(FIXTURE_PREAMBLE) or not text.endswith("\n"):
            raise RuntimeError(f"frozen fixture wrapper mismatch: {source}")
        payload = text[len(FIXTURE_PREAMBLE) :]
        old, new = f"theorem {theorem}", f"theorem {batched_theorem}"
        if payload.count(old) != 1 or payload.count("theorem ") != 1:
            raise RuntimeError(f"fixture theorem mismatch: {source}")
        if FORBIDDEN_FIXTURE_TOKENS.search(payload):
            raise RuntimeError(f"forbidden proof token in fixture: {source}")
        fixture_lines = [
            number
            for number, line in enumerate(text.splitlines(), 1)
            if line.strip() == f"exact {witness}"
        ]
        if len(fixture_lines) != 1:
            raise RuntimeError(f"fixture witness mismatch: {source}")
        payloads.append(payload.replace(old, new, 1))
        contracts.append(
            {
                "filename": filename,
                "sha256": expected_hash,
                "bytes": source.stat().st_size,
                "theorem": theorem,
                "batched_theorem": batched_theorem,
                "witness": witness,
                "source": str(source.relative_to(REPO)),
                "fixture_exact_line": fixture_lines[0],
            }
        )

    expected = BATCHED_PREAMBLE + "\n".join(payloads) + BATCHED_EPILOGUE
    observed = BATCHED_SOURCE.read_text(encoding="utf-8", errors="strict")
    if observed != expected:
        raise RuntimeError("batched source differs from exact frozen-fixture reconstruction")

    for contract in contracts:
        lines = [
            number
            for number, line in enumerate(observed.splitlines(), 1)
            if line.strip() == f"exact {contract['witness']}"
        ]
        if len(lines) != 1:
            raise RuntimeError(f"batched witness mismatch: {contract['filename']}")
        contract["combined_exact_line"] = lines[0]
        contract["combined_exact_text"] = f"  exact {contract['witness']}"
    return contracts


def terminate(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=TIMEOUT_TERMINATION_GRACE_SECONDS)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait(timeout=TIMEOUT_TERMINATION_GRACE_SECONDS)


def child_limit() -> None:
    resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_CAPTURE_BYTES, MAX_CAPTURE_BYTES))


def split_diagnostics(output: str) -> tuple[str, list[dict[str, object]]]:
    matches = list(DIAGNOSTIC_HEADER.finditer(output))
    preamble = output[: matches[0].start()] if matches else output
    blocks: list[dict[str, object]] = []
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


def contains_any(text: str, markers: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return any(marker in lowered for marker in markers)


def main() -> int:
    if os.name != "posix" or sys.platform != "linux":
        raise SystemExit("batched negative controls require Linux process isolation")
    if LAKE is None:
        raise SystemExit("lake NOT FOUND: set NDEA_LAKE or put pinned lake on PATH")
    lake_path = Path(LAKE).resolve()
    if not lake_path.is_file() or not os.access(lake_path, os.X_OK):
        raise SystemExit(f"lake is not an executable regular file: {lake_path}")

    limit = timeout_seconds()
    contracts = reconstruct()
    case_logs = [
        DIAGNOSTICS / f"{Path(case[0]).stem}.rejection.log" for case in CASES
    ]
    planned = [RAW_DIAGNOSTIC, RESULTS_PATH, RECEIPT_PATH, *case_logs]
    collisions = [str(path) for path in planned if path.exists()]
    if collisions:
        raise SystemExit("refusing to overwrite evidence:\n" + "\n".join(collisions))
    DIAGNOSTICS.mkdir(parents=True, exist_ok=True)

    bound_before = snapshot_bound_inputs()
    control_before = snapshot_control_inputs()
    source_argument = str(BATCHED_SOURCE)
    argv = [str(lake_path), "env", "lean", source_argument]
    environment_overrides = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "NO_COLOR": "1"}
    child_environment = os.environ.copy()
    child_environment.update(environment_overrides)

    started_utc = utc_now()
    started_monotonic = time.monotonic()
    timed_out = False
    spawn_error: str | None = None
    exit_code: int | None = None
    process_invocations = 0
    output_bytes = b""
    try:
        with tempfile.TemporaryFile() as capture:
            process = subprocess.Popen(
                argv,
                cwd=REPO,
                env=child_environment,
                stdin=subprocess.DEVNULL,
                stdout=capture,
                stderr=subprocess.STDOUT,
                start_new_session=True,
                preexec_fn=child_limit,
            )
            process_invocations = 1
            try:
                process.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                timed_out = True
                terminate(process)
            exit_code = process.returncode
            capture.seek(0)
            output_bytes = capture.read(MAX_CAPTURE_BYTES + 1)
    except (OSError, subprocess.SubprocessError) as error:
        spawn_error = f"{type(error).__name__}: {error}"

    elapsed_seconds = time.monotonic() - started_monotonic
    finished_utc = utc_now()
    bound_after = snapshot_bound_inputs()
    control_after = snapshot_control_inputs()
    output_limit_exceeded = len(output_bytes) > MAX_CAPTURE_BYTES
    output_bytes = output_bytes[:MAX_CAPTURE_BYTES]
    try:
        output = output_bytes.decode("utf-8", errors="strict")
        output_is_utf8 = True
    except UnicodeDecodeError:
        output = output_bytes.decode("utf-8", errors="backslashreplace")
        output_is_utf8 = False

    harness = {
        "process_invocation_id": PROCESS_INVOCATION_ID,
        "argv": argv,
        "cwd": str(REPO),
        "environment_overrides": environment_overrides,
        "started_utc": started_utc,
        "finished_utc": finished_utc,
        "elapsed_seconds": elapsed_seconds,
        "timeout_environment_variable": TIMEOUT_ENV,
        "timeout_seconds": limit,
        "timed_out": timed_out,
        "natural_exit_code_required": 1,
        "exit_code": exit_code,
        "spawn_error": spawn_error,
        "stderr_mode": "STDOUT",
        "capture_limit_bytes": MAX_CAPTURE_BYTES,
        "output_limit_exceeded": output_limit_exceeded,
        "total_process_invocations": process_invocations,
    }
    raw_text = (
        "=== SHARED PROCESS HARNESS ===\n"
        + json.dumps(harness, indent=2, sort_keys=True)
        + "\n=== MERGED STDOUT+STDERR ===\n"
        + output
    )
    write_exclusive(RAW_DIAGNOSTIC, raw_text)
    raw_hash = sha256(RAW_DIAGNOSTIC)

    preamble, blocks = split_diagnostics(output)
    expected_lines = [int(contract["combined_exact_line"]) for contract in contracts]
    framed_output = DIAGNOSTIC_HEADER_PREFIX.sub("", output)
    global_checks = {
        "diagnostic_utf8": output_is_utf8,
        "exactly_two_diagnostic_headers": len(blocks) == len(CASES) == 2,
        "all_headers_are_errors": all(block["severity"] == "error" for block in blocks),
        "no_unframed_output": preamble.strip() == "",
        "exact_source_path_and_line_sequence": (
            [block["line"] for block in blocks] == expected_lines
            and all(block["path"] == source_argument for block in blocks)
        ),
        "no_import_or_infrastructure_error": not contains_any(
            framed_output, INFRA_MARKERS
        ),
        "no_syntax_error": not contains_any(framed_output, SYNTAX_MARKERS),
        "no_tactic_or_elaboration_error": not contains_any(
            framed_output, TACTIC_OR_ELABORATION_MARKERS
        ),
        "bound_inputs_unchanged_during_run": bound_before == bound_after,
        "control_inputs_unchanged_during_run": control_before == control_after,
    }
    by_line: dict[int, list[dict[str, object]]] = {}
    for block in blocks:
        by_line.setdefault(int(block["line"]), []).append(block)

    witnesses = tuple(str(contract["witness"]) for contract in contracts)
    process_ok = (
        process_invocations == 1
        and spawn_error is None
        and not timed_out
        and not output_limit_exceeded
        and exit_code == 1
    )
    rows: list[dict[str, object]] = []
    for contract in contracts:
        matching = by_line.get(int(contract["combined_exact_line"]), [])
        block = matching[0] if len(matching) == 1 else None
        diagnostic_text = "" if block is None else str(block["text"])
        diagnostic_body = DIAGNOSTIC_HEADER_PREFIX.sub("", diagnostic_text)
        checks = {
            "fixture_hash_and_reconstruction_valid": True,
            "exactly_one_case_diagnostic": block is not None,
            "intended_combined_source_path": (
                block is not None and block["path"] == source_argument
            ),
            "intended_combined_exact_line": (
                block is not None and block["line"] == contract["combined_exact_line"]
            ),
            "diagnostic_column_is_positive": block is not None and block["column"] > 0,
            "type_mismatch_header": (
                block is not None
                and str(block["message"]).strip().lower() == "type mismatch"
            ),
            "own_witness_present_only": (
                {witness for witness in witnesses if witness in diagnostic_text}
                == {contract["witness"]}
            ),
            "has_actual_and_expected_types": (
                re.search(
                    r"\bhas type\b[\s\S]*\bbut is expected to have type\b",
                    diagnostic_text,
                    re.IGNORECASE,
                )
                is not None
            ),
            "no_import_or_infrastructure_error": not contains_any(
                diagnostic_body, INFRA_MARKERS
            ),
            "no_syntax_error": not contains_any(diagnostic_body, SYNTAX_MARKERS),
            "no_tactic_or_elaboration_error": not contains_any(
                diagnostic_body, TACTIC_OR_ELABORATION_MARKERS
            ),
        }
        attributable = process_ok and all(global_checks.values()) and all(checks.values())
        case_name = Path(str(contract["filename"])).stem
        case_log = DIAGNOSTICS / f"{case_name}.rejection.log"
        reference = {
            "case": case_name,
            "process_invocation_id": PROCESS_INVOCATION_ID,
            "raw_diagnostic": str(RAW_DIAGNOSTIC.relative_to(REPO)),
            "raw_diagnostic_sha256": raw_hash,
            "combined_source": str(BATCHED_SOURCE.relative_to(REPO)),
            "combined_exact_line": contract["combined_exact_line"],
            "witness": contract["witness"],
        }
        write_exclusive(
            case_log,
            "=== SHARED PROCESS REFERENCE ===\n"
            + json.dumps(reference, indent=2, sort_keys=True)
            + "\n=== LEAN DIAGNOSTIC BLOCK ===\n"
            + diagnostic_text,
        )
        rows.append(
            {
                "case": case_name,
                "source": contract["source"],
                "source_bytes": contract["bytes"],
                "source_sha256": contract["sha256"],
                "fixture_theorem": contract["theorem"],
                "batched_theorem": contract["batched_theorem"],
                "witness_expected_in_diagnostic": contract["witness"],
                "fixture_exact_line": contract["fixture_exact_line"],
                "combined_exact_line": contract["combined_exact_line"],
                "process_invocation_id": PROCESS_INVOCATION_ID,
                "diagnostic": str(case_log.relative_to(REPO)),
                "diagnostic_sha256": sha256(case_log),
                "diagnostic_checks": checks,
                "attributable_rejection": attributable,
                "reason_code": (
                    "EXPECTED_FALSE_STATEMENT_TYPE_MISMATCH"
                    if attributable
                    else "BATCHED_REJECTION_CONTRACT_FAILED"
                ),
                "status": "PASS" if attributable else "FAIL",
            }
        )

    passed = sum(row["status"] == "PASS" for row in rows)
    failed = len(rows) - passed
    results = {
        "schema": "ndea.exp003.lean_negative_controls.v1",
        "status": "PASS" if failed == 0 else "FAIL",
        "started_utc": started_utc,
        "finished_utc": finished_utc,
        "elapsed_seconds": elapsed_seconds,
        "cwd": str(REPO),
        "unique_cases": len(CASES),
        "total_process_invocations": process_invocations,
        "passed_unique_cases": passed,
        "failed_unique_cases": failed,
        "combined_source": str(BATCHED_SOURCE.relative_to(REPO)),
        "combined_source_sha256": sha256(BATCHED_SOURCE),
        "raw_diagnostic": str(RAW_DIAGNOSTIC.relative_to(REPO)),
        "raw_diagnostic_sha256": raw_hash,
        "global_diagnostic_checks": global_checks,
        "shared_process": harness,
        "bound_inputs_before": bound_before,
        "bound_inputs_after": bound_after,
        "control_inputs_before": control_before,
        "control_inputs_after": control_after,
        "results": rows,
    }
    write_exclusive(RESULTS_PATH, json.dumps(results, indent=2, sort_keys=True) + "\n")

    receipt = {
        "schema": "ndea.exp003.lean_negative_controls.execution_receipt.v1",
        "status": results["status"],
        "process_invocation_id": PROCESS_INVOCATION_ID,
        "command_and_timing": harness,
        "counts": {
            "unique_cases": len(CASES),
            "total_process_invocations": process_invocations,
            "passed_unique_cases": passed,
            "failed_unique_cases": failed,
        },
        "source_identities": {
            "control_inputs_before": control_before,
            "control_inputs_after": control_after,
            "bound_inputs_before": bound_before,
            "bound_inputs_after": bound_after,
        },
        "evidence": {
            "raw_diagnostic": file_identity(RAW_DIAGNOSTIC),
            "semantic_results": file_identity(RESULTS_PATH),
            "case_diagnostics": [
                file_identity(DIAGNOSTICS / f"{Path(case[0]).stem}.rejection.log")
                for case in CASES
            ],
        },
        "acceptance_contract": make_acceptance_contract(
            exit_code=exit_code,
            process_invocations=process_invocations,
            passed=passed,
            failed=failed,
            global_checks=global_checks,
        ),
    }
    rendered_receipt = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    write_exclusive(RECEIPT_PATH, rendered_receipt)
    print(rendered_receipt, end="")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
