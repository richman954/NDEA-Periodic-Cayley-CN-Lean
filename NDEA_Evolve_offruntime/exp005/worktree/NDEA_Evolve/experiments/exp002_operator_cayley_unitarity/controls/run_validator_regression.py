#!/usr/bin/env python3
"""Generate bounded adversarial fixtures and exercise the strict Exp002 validator."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
VALIDATOR = ROOT / "validator" / "validate_operator_cayley.py"
CERT = ROOT / "certificates" / "operator_cayley_core.json"
RECEIPT = ROOT / "metadata" / "operator_cayley_run_receipt.json"
SOURCE = ROOT / "source" / "julia"
FIXTURES = HERE / "fixtures"
LOGS = ROOT / "logs"


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def resign(cert):
    digest = hashlib.sha256(canonical(cert["core"])).hexdigest()
    cert["core_sha256"] = digest
    cert["run_id"] = "exp002-" + digest[:24]


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def cert_case(name, transform, expected, resign_core=True):
    value = copy.deepcopy(ORIGINAL_CERT)
    transform(value)
    if resign_core:
        resign(value)
    path = FIXTURES / f"{name}.json"
    write_json(path, value)
    return {"name": name, "certificate": path, "expected": expected, "full": False}


def receipt_case(name, transform, expected):
    value = copy.deepcopy(ORIGINAL_RECEIPT)
    transform(value)
    path = FIXTURES / f"{name}.receipt.json"
    write_json(path, value)
    return {"name": name, "certificate": CERT, "receipt": path, "expected": expected, "full": True}


def set_num(cell, num, den="1"):
    cell["re"] = {"num": str(num), "den": str(den)}


ORIGINAL_CERT = json.loads(CERT.read_text(encoding="utf-8"))
ORIGINAL_RECEIPT = json.loads(RECEIPT.read_text(encoding="utf-8"))
FIXTURES.mkdir(parents=True, exist_ok=True)
LOGS.mkdir(parents=True, exist_ok=True)

cases = []

# JSON and envelope attacks.
malformed = FIXTURES / "malformed_json.json"
malformed.write_text('{"schema":', encoding="utf-8")
cases.append({"name": "malformed_json", "certificate": malformed, "expected": "cannot parse", "full": False})
duplicate = FIXTURES / "duplicate_top_key.json"
duplicate.write_text('{"schema":"x","schema":"y"}\n', encoding="utf-8")
cases.append({"name": "duplicate_top_key", "certificate": duplicate, "expected": "duplicate JSON key", "full": False})
cases += [
    cert_case("missing_top_key", lambda x: x.pop("run_id"), "key set mismatch", False),
    cert_case("extra_top_key", lambda x: x.__setitem__("verdict", True), "key set mismatch", False),
    cert_case("wrong_certificate_schema", lambda x: x.__setitem__("schema", "ndea.exp001.certificate.v1"), "certificate.schema", False),
    cert_case("wrong_core_hash", lambda x: x.__setitem__("core_sha256", "0" * 64), "certificate.core_sha256", False),
    cert_case("wrong_run_id", lambda x: x.__setitem__("run_id", "exp002-forged"), "certificate.run_id", False),
]

# Re-signed semantic attacks exercise reconstruction rather than only the hash gate.
cases += [
    cert_case("wrong_core_schema", lambda x: x["core"].__setitem__("schema", "ndea.exp002.operator_cayley_core.v0"), "core.schema"),
    cert_case("weakened_assumption", lambda x: x["core"]["assumptions"].__setitem__("unitarity", ["finite square complex matrix"]), "core.metadata.assumptions"),
    cert_case("changed_commutator_convention", lambda x: x["core"]["conventions"].__setitem__("commutator", "[X,Y]=YX-XY"), "core.metadata.conventions"),
    cert_case("noncanonical_rational", lambda x: x["core"]["exact_instances"][0]["a"].update({"num": "2", "den": "4"}), "rational must be normalized"),
    cert_case("zero_denominator", lambda x: x["core"]["exact_instances"][0]["a"].__setitem__("den", "0"), "noncanonical positive denominator"),
    cert_case("altered_generator_entry", lambda x: set_num(x["core"]["exact_instances"][0]["H"][0][0], 1), "exact_instances[0].D"),
    cert_case("altered_inverse_entry", lambda x: set_num(x["core"]["exact_instances"][0]["D_inverse"][0][0], 99), "D_inverse"),
    cert_case("altered_unitarity_residual", lambda x: set_num(x["core"]["exact_instances"][0]["residuals"]["Udagger_U_minus_I"][0][0], 1), "residuals.Udagger_U_minus_I"),
    cert_case("swapped_composition", lambda x: x["core"]["composition"].__setitem__("P21", x["core"]["composition"]["P12"]), "composition.P21"),
    cert_case("order_defect_sign", lambda x: x["core"]["order_defect"].__setitem__("coefficient", {"num": "4", "den": "3"}), "order_defect.coefficient"),
    cert_case("order_defect_residual_nonzero", lambda x: set_num(x["core"]["order_defect"]["residual"][0][0], 1), "order_defect.residual"),
    cert_case("remove_adversarial_case", lambda x: x["core"]["adversarial_witnesses"].pop(), "adversarial witness IDs/order mismatch"),
    cert_case("semigroup_false_claim_zeroed", lambda x: x["core"]["adversarial_witnesses"][5].__setitem__("C_a_plus_b", x["core"]["adversarial_witnesses"][5]["C_a_times_C_b"]), "adversarial.semigroup.C_a_plus_b"),
    cert_case("wrong_order_control_zeroed", lambda x: x["core"]["adversarial_witnesses"][8].__setitem__("wrong_rhs", x["core"]["order_defect"]["cayley_commutator"]), "adversarial.wrong_left.rhs"),
    cert_case("search_count_forged", lambda x: x["core"]["exhaustive_counterexample_search"].__setitem__("singular_denominator", 0), "search.singular_denominator"),
    cert_case("symbolic_coefficient_forged", lambda x: set_num(x["core"]["symbolic_star_polynomial_derivation"]["X"][1]["coefficient"], 1), "symbolic.X"),
    cert_case("source_hash_forged", lambda x: x["core"]["source_sha256"].__setitem__("discover_operator_cayley.jl", "0" * 64), "core.source.discover_operator_cayley.jl"),
]

# Run-receipt and independently fixed numerical-gate attacks.
cases += [
    receipt_case("receipt_false_pass", lambda x: x.__setitem__("exact_status", "FAIL"), "receipt.statuses"),
    receipt_case("numeric_limit_weakened", lambda x: x["numeric_nonproof"].__setitem__("acceptance_limit", "1e-2"), "numeric.independent_limit"),
    receipt_case("numeric_single_above_limit", lambda x: x["numeric_nonproof"].__setitem__("max_single_factor_unitarity_residual", "1.1e-10"), "numeric.single_accepted"),
    receipt_case("numeric_product_nan", lambda x: x["numeric_nonproof"].__setitem__("max_three_factor_unitarity_residual", "NaN"), "numeric.product_finite"),
    receipt_case("numeric_count_forged", lambda x: x["numeric_nonproof"].__setitem__("ordered_product_checks", 1), "numeric.counts"),
    receipt_case("numeric_norm_substituted", lambda x: x["numeric_nonproof"].__setitem__("residual_norm", "entrywise max norm"), "numeric.norm"),
    receipt_case("receipt_certificate_hash_forged", lambda x: x.__setitem__("certificate_sha256", "0" * 64), "receipt.certificate_sha256"),
]

valid_runs = [
    {"name": "valid_full_absolute", "cwd": ROOT, "argv": [sys.executable, str(VALIDATOR), str(CERT), "--receipt", str(RECEIPT), "--source-root", str(SOURCE)]},
    {"name": "valid_certificate_and_source", "cwd": ROOT, "argv": [sys.executable, str(VALIDATOR), str(CERT), "--source-root", str(SOURCE)]},
    {"name": "valid_certificate_only", "cwd": Path("/tmp"), "argv": [sys.executable, str(VALIDATOR), str(CERT)]},
]

results = []
for run in valid_runs:
    proc = subprocess.run(run["argv"], cwd=run["cwd"], text=True, capture_output=True)
    passed = proc.returncode == 0 and "VALIDATION_STATUS=PASS" in proc.stdout
    results.append({"name": run["name"], "kind": "valid", "exit_code": proc.returncode,
                    "passed": passed, "stdout": proc.stdout, "stderr": proc.stderr})

for case in cases:
    argv = [sys.executable, str(VALIDATOR), str(case["certificate"])]
    if case["full"]:
        argv += ["--receipt", str(case["receipt"]), "--source-root", str(SOURCE)]
    else:
        argv += ["--source-root", str(SOURCE)]
    proc = subprocess.run(argv, cwd=ROOT, text=True, capture_output=True)
    combined = proc.stdout + proc.stderr
    passed = proc.returncode == 1 and "VALIDATION_STATUS=FAIL" in proc.stderr and case["expected"] in combined
    results.append({"name": case["name"], "kind": "invalid", "expected_reason_fragment": case["expected"],
                    "exit_code": proc.returncode, "passed": passed, "stdout": proc.stdout, "stderr": proc.stderr})

summary = {
    "schema": "ndea.exp002.validator_regression.v1",
    "validator": str(VALIDATOR),
    "validator_sha256": hashlib.sha256(VALIDATOR.read_bytes()).hexdigest(),
    "valid_configurations": len(valid_runs),
    "valid_accepted": sum(item["passed"] for item in results if item["kind"] == "valid"),
    "unique_invalid_cases": len(cases),
    "invalid_rejected": sum(item["passed"] for item in results if item["kind"] == "invalid"),
    "total_process_invocations": len(results),
    "all_passed": all(item["passed"] for item in results),
    "results": results,
}
write_json(LOGS / "validator_regression_results.json", summary)
with (LOGS / "validator_regression.log").open("w", encoding="utf-8") as stream:
    for item in results:
        stream.write(f"CASE={item['name']} KIND={item['kind']} EXIT={item['exit_code']} RESULT={'PASS' if item['passed'] else 'FAIL'}\n")
        stream.write(item["stdout"])
        stream.write(item["stderr"])
        stream.write("\n")
    stream.write(f"UNIQUE_INVALID_CASES={len(cases)}\n")
    stream.write(f"TOTAL_PROCESS_INVOCATIONS={len(results)}\n")
    stream.write(f"REGRESSION_STATUS={'PASS' if summary['all_passed'] else 'FAIL'}\n")

print(json.dumps({key: summary[key] for key in (
    "valid_configurations", "valid_accepted", "unique_invalid_cases", "invalid_rejected",
    "total_process_invocations", "all_passed")}, indent=2, sort_keys=True))
raise SystemExit(0 if summary["all_passed"] else 1)
