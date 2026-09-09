#!/usr/bin/env python3
"""Run all seven false Lean controls in one bounded, attributable process."""

from __future__ import annotations

import hashlib
import json
import os
import re
import resource
import signal
import shutil
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
LAKE = os.environ.get("NDEA_LAKE") or shutil.which("lake")
TIMEOUT_ENV = "NDEA_EXP002_NEGATIVE_CONTROL_TIMEOUT_SECONDS"
DEFAULT_TIMEOUT_SECONDS = 900
MAX_TIMEOUT_SECONDS = 3_600
TIMEOUT_TERMINATION_GRACE_SECONDS = 5
MAX_CAPTURE_BYTES = 16 * 1024 * 1024
PROCESS_INVOCATION_ID = "lean-batched-negative-controls-001"

IMPORT_LINE = "import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses"
NAMESPACE_LINE = "namespace NDEAEvolve.Exp002.NegativeControls"
OPEN_LINE = "open AdversarialWitnesses"
FIXTURE_PREAMBLE = f"{IMPORT_LINE}\n\n{NAMESPACE_LINE}\n\n{OPEN_LINE}\n\n"
SOURCE_EPILOGUE = f"\n\nend NDEAEvolve.Exp002.NegativeControls\n"
BATCHED_PREAMBLE = f"""{IMPORT_LINE}

/-!
Resource-bounded execution driver for the seven existing false controls.

Each theorem body and target below is the corresponding rejected fixture's
mathematical content.  Keeping all seven commands in one Lean process shares the
large `Mathlib` import while still requiring Lean to emit seven distinct errors.
This file is assurance input, never a production module.
-/

{NAMESPACE_LINE}

{OPEN_LINE}

"""

# Frozen hashes prevent a changed fixture from being smuggled into the batch.
CASES = (
    ("01_dropped_hermiticity_false.lean", "a6c852867b4f60d096a2ca3152b9245bc89b8c119c6fa3d69c48155ed6adaa87", "false_dropped_hermiticity", "false_dropped_hermiticity_batched", "nonhermitian_cayley_not_unitary"),
    ("02_complex_step_false.lean", "cbb25c83dce30f802a6d3dcdf3e81d0b08a63d2061f72fa822759e3423a8cc98", "false_complex_step_unitarity", "false_complex_step_unitarity_batched", "complex_step_half_not_unitary"),
    ("03_order_independence_false.lean", "313cd9b2d2fc3a6e9382303d0a79dd6ba69f515ca2a22c6d3888f3eade452d94", "false_order_independence", "false_order_independence_batched", "pauli_cayley_factors_order_sensitive"),
    ("04_wrong_defect_sign_false.lean", "e5ca2260fc1b4d28717c14ae51ec7631e9b0c8c214517eb3bae00b0d878eb24d", "false_wrong_defect_sign", "false_wrong_defect_sign_batched", "pauli_cayley_commutator_wrong_sign"),
    ("05_one_sided_inverse_permutation_false.lean", "d381fd57a494431ca248f11a786d50968f020175d89dc3b76da5e5c027ff2990", "false_one_sided_inverse_permutation", "false_one_sided_inverse_permutation_batched", "cayleyR_one_sided_inverse_permutation_detected"),
    ("06_zero_step_iff_false.lean", "3c5e5ae8a9213d3d337c3fe78971d30a8bfa3723edebdccbf39e904833bd87c1", "false_zero_step_commutation_equivalence", "false_zero_step_commutation_equivalence_batched", "zero_step_breaks_commutation_iff"),
    ("07_semigroup_merging_false.lean", "5f04d971605f46e22b21146513297a3434141953a5fca2df540ac06943a8eb81", "false_scalar_semigroup_merging", "false_scalar_semigroup_merging_batched", "false_semigroup_merging_witness"),
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
INFRA_MARKERS = ("unknown module prefix", "unknown package", "object file", "does not exist in the search path", "no such file or directory", "failed to build", "build failed", "invalid import")
MALFORMED_MARKERS = ("unexpected token", "unexpected end of input", "invalid syntax", "invalid 'end'", "unterminated")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def timeout_seconds() -> int:
    raw = os.environ.get(TIMEOUT_ENV)
    if raw is None:
        return DEFAULT_TIMEOUT_SECONDS
    if re.fullmatch(r"[1-9][0-9]*", raw) is None or int(raw) > MAX_TIMEOUT_SECONDS:
        raise SystemExit(f"{TIMEOUT_ENV} must be a canonical integer from 1 to {MAX_TIMEOUT_SECONDS}")
    return int(raw)


def write_exclusive(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.", suffix=".tmp")
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


def reconstruct() -> list[dict[str, object]]:
    payloads: list[str] = []
    contracts: list[dict[str, object]] = []
    for filename, expected_hash, theorem, batched_theorem, witness in CASES:
        source = SOURCES / filename
        text = source.read_text(encoding="utf-8", errors="strict")
        if sha256(source) != expected_hash:
            raise RuntimeError(f"frozen fixture hash mismatch: {source}")
        if not text.startswith(FIXTURE_PREAMBLE) or not text.endswith(SOURCE_EPILOGUE):
            raise RuntimeError(f"frozen fixture wrapper mismatch: {source}")
        payload = text[len(FIXTURE_PREAMBLE) : -len(SOURCE_EPILOGUE)]
        old, new = f"theorem {theorem}", f"theorem {batched_theorem}"
        if payload.count(old) != 1:
            raise RuntimeError(f"fixture theorem mismatch: {source}")
        fixture_lines = [n for n, line in enumerate(text.splitlines(), 1) if line.strip() == f"exact {witness}"]
        if len(fixture_lines) != 1:
            raise RuntimeError(f"fixture witness mismatch: {source}")
        payloads.append(payload.replace(old, new, 1))
        contracts.append({"filename": filename, "sha256": expected_hash, "theorem": theorem, "batched_theorem": batched_theorem, "witness": witness, "source": str(source.relative_to(REPO)), "fixture_exact_line": fixture_lines[0]})
    expected = BATCHED_PREAMBLE + "\n\n".join(payloads) + SOURCE_EPILOGUE
    observed = BATCHED_SOURCE.read_text(encoding="utf-8", errors="strict")
    if observed != expected:
        raise RuntimeError("batched source differs from the exact fixture reconstruction")
    for contract in contracts:
        lines = [n for n, line in enumerate(observed.splitlines(), 1) if line.strip() == f"exact {contract['witness']}"]
        if len(lines) != 1:
            raise RuntimeError(f"batched witness mismatch: {contract['filename']}")
        contract["combined_exact_line"] = lines[0]
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
    blocks = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(output)
        blocks.append({"path": match.group("path"), "line": int(match.group("line")), "column": int(match.group("column")), "severity": match.group("severity").lower(), "message": match.group("message"), "text": output[match.start():end]})
    return preamble, blocks


def main() -> int:
    if os.name != "posix" or sys.platform != "linux":
        raise SystemExit("batched negative controls require Linux process isolation")
    if LAKE is None:
        raise SystemExit("lake NOT FOUND: set NDEA_LAKE or put pinned lake on PATH")
    limit = timeout_seconds()
    contracts = reconstruct()
    planned = [RAW_DIAGNOSTIC, RESULTS_PATH, *(DIAGNOSTICS / f"{Path(c[0]).stem}.rejection.log" for c in CASES)]
    collisions = [str(path) for path in planned if path.exists()]
    if collisions:
        raise SystemExit("refusing to overwrite evidence:\n" + "\n".join(collisions))
    DIAGNOSTICS.mkdir(parents=True, exist_ok=True)

    source_argument = str(BATCHED_SOURCE)
    argv = [str(Path(LAKE).resolve()), "env", "lean", source_argument]
    started, before = utc_now(), time.monotonic()
    timed_out, spawn_error, exit_code, invocations = False, None, None, 0
    output_bytes = b""
    try:
        with tempfile.TemporaryFile() as capture:
            process = subprocess.Popen(argv, cwd=REPO, stdin=subprocess.DEVNULL, stdout=capture, stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=child_limit)
            invocations = 1
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
    elapsed, finished = time.monotonic() - before, utc_now()
    output_limit_exceeded = len(output_bytes) >= MAX_CAPTURE_BYTES
    output_bytes = output_bytes[:MAX_CAPTURE_BYTES]
    try:
        output, output_is_utf8 = output_bytes.decode("utf-8", errors="strict"), True
    except UnicodeDecodeError:
        output, output_is_utf8 = output_bytes.decode("utf-8", errors="backslashreplace"), False
    harness = {"process_invocation_id": PROCESS_INVOCATION_ID, "argv": argv, "cwd": str(REPO), "started_utc": started, "finished_utc": finished, "elapsed_seconds": elapsed, "timeout_seconds": limit, "timed_out": timed_out, "exit_code": exit_code, "spawn_error": spawn_error, "stderr_mode": "STDOUT", "capture_limit_bytes": MAX_CAPTURE_BYTES, "output_limit_exceeded": output_limit_exceeded}
    raw_text = "=== SHARED PROCESS HARNESS ===\n" + json.dumps(harness, indent=2, sort_keys=True) + "\n=== MERGED STDOUT+STDERR ===\n" + output
    write_exclusive(RAW_DIAGNOSTIC, raw_text)
    raw_hash = sha256(RAW_DIAGNOSTIC)

    preamble, blocks = split_diagnostics(output)
    expected_lines = [int(c["combined_exact_line"]) for c in contracts]
    stripped = DIAGNOSTIC_HEADER_PREFIX.sub("", output).lower()
    global_checks = {"diagnostic_utf8": output_is_utf8, "exactly_seven_diagnostic_headers": len(blocks) == 7, "all_headers_are_errors": all(b["severity"] == "error" for b in blocks), "no_unframed_output": preamble.strip() == "", "exact_source_path_and_line_sequence": [b["line"] for b in blocks] == expected_lines and all(b["path"] == source_argument for b in blocks), "no_global_import_or_infrastructure_error": not any(x in stripped for x in INFRA_MARKERS), "no_global_malformed_source_error": not any(x in stripped for x in MALFORMED_MARKERS)}
    by_line: dict[int, list[dict[str, object]]] = {}
    for block in blocks:
        by_line.setdefault(int(block["line"]), []).append(block)
    witnesses = tuple(c[4] for c in CASES)
    rows = []
    process_ok = invocations == 1 and spawn_error is None and not timed_out and not output_limit_exceeded and exit_code == 1
    for contract in contracts:
        matching = by_line.get(int(contract["combined_exact_line"]), [])
        block = matching[0] if len(matching) == 1 else None
        text = "" if block is None else str(block["text"])
        lowered = DIAGNOSTIC_HEADER_PREFIX.sub("", text).lower()
        checks = {"fixture_contract_valid": True, "diagnostic_utf8": output_is_utf8, "exactly_seven_diagnostic_headers": global_checks["exactly_seven_diagnostic_headers"], "all_headers_are_errors": global_checks["all_headers_are_errors"], "no_unframed_output": global_checks["no_unframed_output"], "exactly_one_case_error": block is not None, "intended_combined_source_line": block is not None and block["path"] == source_argument and block["line"] == contract["combined_exact_line"], "type_mismatch": block is not None and str(block["message"]).lower().startswith("type mismatch"), "own_witness_present_only": {w for w in witnesses if w in text} == {contract["witness"]}, "has_actual_and_expected_types": re.search(r"\bhas type\b[\s\S]*\bbut is expected to have type\b", text, re.I) is not None, "no_import_or_infrastructure_error": not any(x in lowered for x in INFRA_MARKERS), "no_malformed_source_error": not any(x in lowered for x in MALFORMED_MARKERS)}
        attributable = process_ok and all(global_checks.values()) and all(checks.values())
        case_name = Path(str(contract["filename"])).stem
        case_log = DIAGNOSTICS / f"{case_name}.rejection.log"
        reference = {"case": case_name, "process_invocation_id": PROCESS_INVOCATION_ID, "raw_diagnostic": str(RAW_DIAGNOSTIC.relative_to(REPO)), "raw_diagnostic_sha256": raw_hash}
        write_exclusive(case_log, "=== SHARED PROCESS REFERENCE ===\n" + json.dumps(reference, indent=2, sort_keys=True) + "\n=== LEAN DIAGNOSTIC BLOCK ===\n" + text)
        rows.append({"case": case_name, "source": contract["source"], "source_sha256": contract["sha256"], "fixture_theorem": contract["theorem"], "batched_theorem": contract["batched_theorem"], "witness_expected_in_diagnostic": contract["witness"], "fixture_exact_line": contract["fixture_exact_line"], "combined_exact_line": contract["combined_exact_line"], "process_invocation_id": PROCESS_INVOCATION_ID, "diagnostic": str(case_log.relative_to(REPO)), "diagnostic_sha256": sha256(case_log), "diagnostic_checks": checks, "attributable_rejection": attributable, "reason_code": "EXPECTED_FALSE_STATEMENT_TYPE_MISMATCH" if attributable else "BATCHED_REJECTION_CONTRACT_FAILED", "status": "PASS" if attributable else "FAIL"})

    receipt = {"schema": "ndea.exp002.lean_negative_controls.v3", "started_utc": started, "finished_utc": finished, "cwd": str(REPO), "timeout_environment_variable": TIMEOUT_ENV, "timeout_seconds": limit, "unique_cases": 7, "total_process_invocations": invocations, "passed": sum(r["status"] == "PASS" for r in rows), "failed": sum(r["status"] != "PASS" for r in rows), "combined_source": str(BATCHED_SOURCE.relative_to(REPO)), "combined_source_sha256": sha256(BATCHED_SOURCE), "raw_diagnostic": str(RAW_DIAGNOSTIC.relative_to(REPO)), "raw_diagnostic_sha256": raw_hash, "global_diagnostic_checks": global_checks, "shared_process": harness, "results": rows}
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    write_exclusive(RESULTS_PATH, rendered)
    print(rendered, end="")
    return 0 if receipt["failed"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
