#!/usr/bin/env python3
"""Bounded, Python-only self-check of the Experiment 003 assurance tools.

The check deliberately performs no Lean, Lake, Julia, Git, network, packaging,
or delivery operation.  Python sources are compiled in memory, selected modules
are loaded with ``exec`` (so no bytecode cache is written), and every synthetic
artifact is confined to a temporary directory.
"""

from __future__ import annotations

import ast
import contextlib
import hashlib
import io
import json
import sys
import tempfile
import types
from pathlib import Path
from typing import Any, Callable


HERE = Path(__file__).resolve().parent
EXP_ROOT = HERE.parent
REPO = EXP_ROOT.parents[1]
ASSURANCE = EXP_ROOT / "assurance"
CONTROLS = EXP_ROOT / "controls"
PRODUCTION = (
    REPO / "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"
)
SIGNATURE_PARSER = ASSURANCE / "parse_signature_axiom_audit.py"
FORBIDDEN_SCANNER = ASSURANCE / "run_forbidden_scan.py"
NEGATIVE_RUNNER = CONTROLS / "lean/run_negative_controls.py"
PACKAGER = ASSURANCE / "package_exp003_step1.py"
VERIFIER = ASSURANCE / "verify_exp003_step1_delivery.py"


class SelfCheckFailure(RuntimeError):
    """A failed self-check assertion."""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SelfCheckFailure(message)


def source_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="strict")


def compile_memory(path: Path) -> Any:
    """Compile a UTF-8 Python source without importing or writing a ``.pyc``."""

    return compile(source_text(path), str(path), "exec", dont_inherit=True)


def load_memory(path: Path, name: str) -> types.ModuleType:
    """Load a module exclusively from an in-memory code object."""

    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    exec(compile_memory(path), module.__dict__)
    return module


def python_sources() -> list[Path]:
    paths = {
        path.resolve()
        for root in (ASSURANCE, CONTROLS)
        for path in root.rglob("*.py")
        if path.is_file() and not path.is_symlink()
    }
    return sorted(paths)


def bytecode_inventory() -> dict[str, str]:
    """Record pre-existing bytecode without creating or removing any."""

    return {
        str(path.relative_to(EXP_ROOT)): sha256(path)
        for path in sorted(EXP_ROOT.rglob("*.pyc"))
        if path.is_file() and not path.is_symlink()
    }


def call_parser(module: types.ModuleType, log: Path, output: Path) -> tuple[int, str]:
    previous = sys.argv
    capture = io.StringIO()
    try:
        sys.argv = [str(SIGNATURE_PARSER), "--log", str(log), "--output", str(output)]
        with contextlib.redirect_stdout(capture):
            code = module.main()
    finally:
        sys.argv = previous
    return code, capture.getvalue()


def audit_log(*, unexpected: bool = False, include_end: bool = True) -> str:
    declarations = (
        "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_eq_average",
        "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_apply_norm_le",
        "NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_opNorm_le_one",
    )
    source = "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"

    def info(line: int, payload: str) -> str:
        return f"info: {source}:{line}:0: {payload}"

    lines = ["synthetic preamble", info(100, '"NDEA_EXP003_AUDIT_BEGIN" : String')]
    for index, name in enumerate(declarations, 1):
        lines.extend((info(100 + index, f"@{name} :"), f"  SyntheticSignature{index}"))
    for index, name in enumerate(declarations, 1):
        lines.append(info(110 + index, f"theorem {name} : SyntheticPrintedType{index} := by trivial"))
    dependency = "Unexpected.syntheticAxiom" if unexpected else "propext"
    lines.extend(
        (
            info(121, f"'{declarations[0]}' depends on axioms: [{dependency}]"),
            info(122, f"'{declarations[1]}' depends on axioms: [Classical.choice]"),
            info(123, f"'{declarations[2]}' depends on axioms: [Quot.sound]"),
        )
    )
    if include_end:
        lines.append(info(124, '"NDEA_EXP003_AUDIT_END" : String'))
    lines.append("synthetic epilogue")
    return "\n".join(lines) + "\n"


def main() -> int:
    tests: list[dict[str, Any]] = []
    bytecode_before = bytecode_inventory()
    modules: dict[str, types.ModuleType] = {}

    def record(name: str, operation: Callable[[], Any]) -> None:
        try:
            detail = operation()
            tests.append({"name": name, "status": "PASS", "detail": detail})
        except Exception as error:  # keep the complete bounded suite fail-closed
            tests.append(
                {
                    "name": name,
                    "status": "FAIL",
                    "detail": f"{type(error).__name__}: {error}",
                }
            )

    def check_all_compile() -> dict[str, Any]:
        paths = python_sources()
        require(paths, "no Experiment 003 Python scripts found")
        for path in paths:
            compile_memory(path)
        return {
            "compiled_source_count": len(paths),
            "sources": [str(path.relative_to(REPO)) for path in paths],
        }

    record("all_assurance_and_control_python_compiles_in_memory", check_all_compile)

    def check_explicit_compile(path: Path) -> dict[str, Any]:
        require(path.is_file() and not path.is_symlink(), f"missing regular source: {path}")
        compile_memory(path)
        return {
            "source": str(path.relative_to(REPO)),
            "sha256": sha256(path),
        }

    record("package_tool_compiles_in_memory", lambda: check_explicit_compile(PACKAGER))
    record("delivery_verifier_compiles_in_memory", lambda: check_explicit_compile(VERIFIER))

    def check_pinned_control_command_contract() -> dict[str, Any]:
        package = load_memory(PACKAGER, "exp003_selfcheck_package_contract")
        verifier = load_memory(VERIFIER, "exp003_selfcheck_verifier_contract")
        expected_lake = "/home/richman954/.elan/bin/lake"
        expected_batch = (
            "experiments/exp003_euclidean_resolvent_contraction/"
            "controls/lean/BatchedNegativeControls.lean"
        )
        require(package.PINNED_LAKE == expected_lake, "packager Lake pin mismatch")
        require(verifier.PINNED_LAKE == expected_lake, "verifier Lake pin mismatch")
        require(
            package.NEGATIVE_BATCH_SOURCE == expected_batch,
            "packager negative-control path mismatch",
        )
        require(
            verifier.NEGATIVE_BATCH_SOURCE == expected_batch,
            "verifier negative-control path mismatch",
        )
        predecessor_evidence = "experiments/exp002_operator_cayley_unitarity"
        require(
            predecessor_evidence in package.PREDECESSOR_IMMUTABLE_PATHS,
            "packager omits immutable Experiment 002 evidence tree",
        )
        require(
            tuple(package.PREDECESSOR_IMMUTABLE_PATHS)
            == tuple(verifier.PREDECESSOR_IMMUTABLE_PATHS),
            "packager/verifier immutable predecessor path sets differ",
        )
        expected_acceptance_keys = {
            "natural_lean_exit_code",
            "one_lean_invocation",
            "two_attributable_type_mismatches",
            "global_diagnostic_checks",
            "exclusive_create_no_overwrite",
        }
        require(
            package.NEGATIVE_ACCEPTANCE_KEYS == expected_acceptance_keys,
            "packager negative acceptance-key contract mismatch",
        )
        require(
            verifier.NEGATIVE_ACCEPTANCE_KEYS == expected_acceptance_keys,
            "verifier negative acceptance-key contract mismatch",
        )
        expected_process_id = "exp003-lean-batched-negative-controls-001"
        require(
            package.NEGATIVE_PROCESS_ID == expected_process_id,
            "packager negative process-ID contract mismatch",
        )
        require(
            verifier.NEGATIVE_PROCESS_ID == expected_process_id,
            "verifier negative process-ID contract mismatch",
        )
        return {
            "pinned_lake": expected_lake,
            "negative_batch_source": expected_batch,
            "immutable_predecessor_evidence_tree": predecessor_evidence,
            "negative_acceptance_keys": sorted(expected_acceptance_keys),
            "negative_process_id": expected_process_id,
            "packager_verifier_agree": True,
        }

    record(
        "packager_and_verifier_pin_negative_control_command",
        check_pinned_control_command_contract,
    )

    def check_reconstruction() -> dict[str, Any]:
        module = load_memory(NEGATIVE_RUNNER, "exp003_selfcheck_negative_runner")
        modules["negative"] = module
        contracts = module.reconstruct()
        require(len(contracts) == len(module.CASES) == 2, "expected exactly two controls")
        require(
            all(row.get("combined_exact_line", 0) > 0 for row in contracts),
            "reconstruction did not bind both exact lines",
        )
        return {
            "unique_control_count": len(contracts),
            "batched_source": str(module.BATCHED_SOURCE.relative_to(REPO)),
            "batched_source_sha256": sha256(module.BATCHED_SOURCE),
        }

    record("batched_negative_controls_reconstruct_exactly", check_reconstruction)

    def check_negative_receipt_acceptance_shape() -> dict[str, Any]:
        module = modules.get("negative") or load_memory(
            NEGATIVE_RUNNER, "exp003_selfcheck_negative_runner_contract"
        )
        valid = module.make_acceptance_contract(
            exit_code=1,
            process_invocations=1,
            passed=2,
            failed=0,
            global_checks={"first": True, "second": True},
        )
        require(valid, "valid acceptance contract is empty")
        require(
            set(valid)
            == {
                "natural_lean_exit_code",
                "one_lean_invocation",
                "two_attributable_type_mismatches",
                "global_diagnostic_checks",
                "exclusive_create_no_overwrite",
            },
            f"valid acceptance contract has unexpected keys: {sorted(valid)!r}",
        )
        require(
            all(value is True for value in valid.values()),
            f"valid acceptance contract is not scalar/all true: {valid!r}",
        )
        require(
            isinstance(valid.get("global_diagnostic_checks"), bool),
            "global diagnostic acceptance is not a Boolean",
        )
        altered = module.make_acceptance_contract(
            exit_code=1,
            process_invocations=1,
            passed=2,
            failed=0,
            global_checks={"first": True, "second": False},
        )
        require(
            altered.get("global_diagnostic_checks") is False,
            "false global diagnostic predicate was not propagated",
        )
        return {
            "valid_values_all_true": True,
            "all_values_are_boolean": all(isinstance(value, bool) for value in valid.values()),
            "altered_global_predicate_rejected": True,
        }

    record(
        "negative_receipt_acceptance_contract_is_scalar_and_fail_closed",
        check_negative_receipt_acceptance_shape,
    )

    with tempfile.TemporaryDirectory(prefix="ndea_exp003_assurance_selfcheck_") as raw:
        temporary = Path(raw)
        parser = load_memory(SIGNATURE_PARSER, "exp003_selfcheck_signature_parser")
        modules["parser"] = parser

        def valid_parser() -> dict[str, Any]:
            log, output = temporary / "valid.log", temporary / "valid.json"
            log.write_text(audit_log(), encoding="utf-8", newline="\n")
            code, stdout = call_parser(parser, log, output)
            result = json.loads(output.read_text(encoding="utf-8", errors="strict"))
            require(code == 0, f"valid audit returned {code}")
            require(result.get("status") == "PASS", "valid audit was not PASS")
            require(len(result.get("declarations", [])) == 3, "valid declaration count")
            require('"status": "PASS"' in stdout, "valid parser stdout missing PASS")
            return {"exit_code": code, "status": result["status"], "declarations": 3}

        record("signature_parser_accepts_synthetic_valid_audit", valid_parser)

        def unexpected_parser() -> dict[str, Any]:
            log, output = temporary / "unexpected.log", temporary / "unexpected.json"
            log.write_text(audit_log(unexpected=True), encoding="utf-8", newline="\n")
            code, _ = call_parser(parser, log, output)
            result = json.loads(output.read_text(encoding="utf-8", errors="strict"))
            require(code == 1, f"unexpected-dependency audit returned {code}")
            require(result.get("status") == "FAIL", "unexpected dependency was accepted")
            require(
                result.get("unexpected_dependencies") == ["Unexpected.syntheticAxiom"],
                "unexpected dependency was not attributed exactly",
            )
            return {
                "exit_code": code,
                "status": result["status"],
                "unexpected_dependencies": result["unexpected_dependencies"],
            }

        record("signature_parser_rejects_unexpected_dependency", unexpected_parser)

        def missing_marker_parser() -> dict[str, Any]:
            log, output = temporary / "missing-marker.log", temporary / "missing-marker.json"
            log.write_text(
                audit_log(include_end=False), encoding="utf-8", newline="\n"
            )
            try:
                call_parser(parser, log, output)
            except SystemExit as error:
                message = str(error)
                require(
                    "expected exactly one source-prefixed audit marker pair" in message,
                    message,
                )
                require(not output.exists(), "failed marker audit unexpectedly wrote output")
                return {"rejected": True, "diagnostic": message}
            raise SelfCheckFailure("missing audit marker was accepted")

        record("signature_parser_rejects_missing_marker", missing_marker_parser)

        scanner = load_memory(FORBIDDEN_SCANNER, "exp003_selfcheck_forbidden_scanner")
        modules["scanner"] = scanner

        def current_source_clean() -> dict[str, Any]:
            require(
                tuple(scanner.FILES)
                == (Path("NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"),),
                "scanner is not bound to exactly the single production source",
            )
            text = source_text(PRODUCTION)
            matches = [match.group(0) for match in scanner.PATTERN.finditer(text)]
            require(matches == [], f"production forbidden-token matches: {matches!r}")
            return {
                "production_source": str(PRODUCTION.relative_to(REPO)),
                "source_sha256": sha256(PRODUCTION),
                "match_count": 0,
            }

        record("forbidden_regex_finds_zero_in_single_production_source", current_source_clean)

        def synthetic_tokens_detected() -> dict[str, Any]:
            synthetic = "\n".join(scanner.TOKENS) + "\n"
            matches = [match.group(0) for match in scanner.PATTERN.finditer(synthetic)]
            require(matches == list(scanner.TOKENS), f"synthetic matches differ: {matches!r}")
            return {"expected_tokens": list(scanner.TOKENS), "detected_tokens": matches}

        record("forbidden_regex_detects_all_synthetic_tokens", synthetic_tokens_detected)

        def one_popen_site() -> dict[str, Any]:
            tree = ast.parse(source_text(NEGATIVE_RUNNER), filename=str(NEGATIVE_RUNNER))
            calls = [
                node
                for node in ast.walk(tree)
                if isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id == "subprocess"
                and node.func.attr == "Popen"
            ]
            require(len(calls) == 1, f"expected one subprocess.Popen site, found {len(calls)}")
            call = calls[0]
            keywords = {item.arg for item in call.keywords if item.arg is not None}
            required = {"cwd", "env", "stdin", "stdout", "stderr", "start_new_session", "preexec_fn"}
            require(required <= keywords, f"Popen site missing keywords: {sorted(required-keywords)}")
            return {"popen_site_count": 1, "line": call.lineno, "keywords": sorted(keywords)}

        record("negative_runner_has_one_bounded_popen_site", one_popen_site)

    def no_bytecode_side_effect() -> dict[str, Any]:
        after = bytecode_inventory()
        require(after == bytecode_before, "repository Python bytecode inventory changed")
        return {"preexisting_bytecode_file_count": len(after), "unchanged": True}

    record("selfcheck_creates_no_repository_bytecode", no_bytecode_side_effect)

    failed = [row for row in tests if row["status"] != "PASS"]
    result = {
        "schema": "ndea.exp003.assurance_selfcheck.v1",
        "status": "PASS" if not failed else "FAIL",
        "unique_test_count": len(tests),
        "passed_unique_test_count": len(tests) - len(failed),
        "failed_unique_test_count": len(failed),
        "execution_boundary": {
            "python_only": True,
            "lean_or_lake_invocations": 0,
            "persistent_outputs_created": 0,
            "synthetic_outputs_location": "temporary_directory_removed_before_report",
        },
        "tests": tests,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
