"""Validate completed Exp008 evidence and write final verification receipts.

Run only after both combined checks and remote_check/check_export.py finish:
    python3 -B exp008/finalize_verification.py
This does not run Lean, modify proof inputs, write reports, or seal a packet.
"""
import ast
import datetime
import hashlib
import importlib.util
import json
import math
from pathlib import Path, PurePosixPath
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
MODULES = ("FrequencyBounds", "ContinuumModes", "FourierGrid", "Orthogonality",
           "SuperpositionClosure", "StageBridge", "Controls")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPILER_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
MATHLIB_COMMIT = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
PINS = {
    "run_lean.py": "7d0a5000900d202327a4425e825ba915468436b4e26d92bea3f3975d596f40ad",
    "verify_combined.py": "c9f0ee95367aa08129ad401b9e638707dfa85cd26058fbe8c38655ff4706231a",
    "make_combined.py": "9b6b9edbe615c9ffb7afe878d6d876a596073024e15155b62ee92ae8d1d8be99",
    "remote_check/start_modules.py": "dce4e2de237982e5dd12d18cd313d6fefc6a8a3c5ab1295e9438f055b14bc66f",
    "remote_check/bootstrap_inputs/lake-manifest.json": "8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158",
    "verification_tools/verify_exp005.py": "fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb",
    "verification_tools/lean_import_closure.py": "12d648a6fca9b35c69d400d4695a97b5957fe50cb0a96038ef813ad6fba58057",
}
PREDECESSORS = {
    "exp005_frozen": (889, "8a6dddcfdd6f29034397bd950b3098399177ee1eb892edfa91656d0fb11c692a"),
    "exp006_local_verified": (21, "30a0eeb371b1d525944427cb310814ba7907f33b7d7d09f75437281f02ecae9b"),
    "exp006_final_packet": (99, "1c11c0a1523ef5a56a9fa72b6a150246c232b831ec15acef9f172d8d9d47a678"),
    "exp007_final_packet": (217, "5bd1178ebd2df92579092a3de17383f6b4097214d7a12b1442bcaa07185eda5a"),
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    require(path.is_file() and not path.is_symlink(), "Missing or symlinked file: " + str(path))
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    sha(path)
    return json.loads(path.read_text(), object_pairs_hook=unique_object,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          RuntimeError("Non-finite JSON constant: " + value)))


def child(base, name):
    require(isinstance(name, str), "Non-string evidence path")
    relative = PurePosixPath(name)
    require(name and not relative.is_absolute() and ".." not in relative.parts
            and str(relative) == name, "Unsafe or non-normalized evidence path: " + name)
    path = base / name
    require(path.resolve().is_relative_to(base.resolve()), "Evidence escapes root: " + name)
    return path


def hash_map(value, label):
    require(isinstance(value, dict) and bool(value), "Empty or invalid hash map: " + label)
    for name, digest in value.items():
        child(ROOT, name)
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest),
                "Invalid SHA-256 in " + label + ": " + name)
    return value


def check_hash(path, expected):
    require(sha(path) == expected, "Hash mismatch: " + str(path))


def relative(path):
    return str(path.relative_to(ROOT))


def receipt(path):
    return {"path": relative(path), "sha256": sha(path)}


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "Cannot load checker: " + str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def elapsed(row, label):
    value = row.get("elapsed_seconds")
    require(type(value) in (int, float) and math.isfinite(value) and value > 0,
            "Invalid elapsed time: " + label)
    return value


def timestamp(row):
    value = datetime.datetime.fromisoformat(row["start_utc"])
    require(value.tzinfo is not None, "Timestamp lacks timezone")
    return value


def declared_audits(source, audit):
    stack, names = [], []
    for line in audit.code_only(source).splitlines():
        if match := re.match(r"^namespace (\S+)", line):
            stack.append(("namespace", match[1]))
        elif re.match(r"^(?:noncomputable )?section(?: \S+)?\s*$", line):
            stack.append(("section", ""))
        elif re.match(r"^end(?: \S+)?\s*$", line):
            require(bool(stack), "Unmatched namespace end while reading modular audits")
            stack.pop()
        elif match := re.match(r"^#print axioms (\S+)", line):
            name = match[1]
            if not name.startswith("NDEAEvolve."):
                name = ".".join([name for kind, name in stack if kind == "namespace"] + [name])
            names.append(name)
    require(len(names) == len(set(names)), "Duplicate modular audit declaration")
    return set(names)


def check_log(path, digest, expected, audit):
    check_hash(path, digest)
    text = path.read_text()
    if expected:
        return {key: sorted(value) for key, value in audit.validate_axiom_log(text, expected).items()}
    require(not re.search(r"\berror:|\bsorryAx\b|declaration uses .sorry.|depends on axioms|does not depend on any axioms", text),
            "Unexpected audit or failure in module without audit declarations: " + str(path))
    return {}


def main():
    for name, digest in PINS.items():
        check_hash(ROOT / name, digest)
    inputs_path = ROOT / "evidence/FINAL_INPUTS.json"
    inputs = read_json(inputs_path)
    sources = hash_map(inputs["source_hashes"], "project sources")
    require(set(sources) == {"lean/Exp007Foundation.lean"} |
            {"lean/" + name + ".lean" for name in MODULES}, "Unexpected project source catalog")
    for name, digest in sources.items():
        check_hash(child(ROOT, name), digest)
    combined = ROOT / "lean/Exp008Combined.lean"
    check_hash(combined, inputs["source_sha256"])
    require(inputs["generator_sha256"] == PINS["make_combined.py"], "Generator pin mismatch")
    generator = load_module("exp008_final_generator", ROOT / "make_combined.py")
    reconstructed, reconstructed_inputs = generator.build(ROOT)
    require(reconstructed == combined.read_text() and reconstructed_inputs == inputs,
            "Combined source or complete audit catalog does not reconstruct exactly")
    names = inputs["expected_audits"]
    require(isinstance(names, list) and len(names) == len(set(names)) == 90, "Expected exactly 90 unique audits")
    controls = [name for name in names if name.startswith("NDEAEvolve.Exp008.Controls.")]
    require(len(controls) == 7 and len(names) - len(controls) == 83, "Production/control count mismatch")
    require(all(name.startswith("NDEAEvolve.Exp008.") for name in names), "Unexpected audit namespace")
    audit = load_module("exp008_final_audit", ROOT / "verification_tools/verify_exp005.py")
    require(audit.ALLOWED_AXIOMS == STANDARD_AXIOMS, "Audit checker allowed-axiom mismatch")
    audit.scan_proof_policy(combined.read_text())
    module_audits = {name: declared_audits((ROOT / "lean" / (name + ".lean")).read_text(), audit)
                     for name in MODULES}
    lock = read_json(ROOT / "remote_check/bootstrap_inputs/lake-manifest.json")

    # Revalidate every downloaded byte covered by the successful transfer receipt.
    transfer_path = ROOT / "remote_check/FINAL_TRANSFER_CHECK.json"
    transfer = read_json(transfer_path)
    require(transfer.get("passed") is True and transfer["audits_checked"] == 90
            and transfer["source_sha256"] == inputs["source_sha256"], "Transfer has not passed for current source")
    remote_root = ROOT / "remote_check/downloaded_evidence/exp008_independent_evidence"
    export_path = ROOT / "remote_check/EXPORT_RECEIPT.json"
    export = read_json(export_path)
    require(export.get("passed") is True and export["combined_sha256"] == inputs["source_sha256"],
            "Export receipt mismatch")
    check_hash(ROOT / "remote_check" / Path(export["archive"]).name, export["archive_sha256"])
    manifest_path = remote_root / "EVIDENCE_SHA256.json"
    check_hash(manifest_path, export["manifest_sha256"])
    transferred = hash_map(read_json(manifest_path), "transferred evidence")
    require(len(transferred) == export["files"] == transfer["evidence_files_checked"]
            and transfer["archive_sha256"] == export["archive_sha256"], "Transfer receipt counts/identity mismatch")
    actual = {str(path.relative_to(remote_root)) for path in remote_root.rglob("*") if path.is_file()}
    require(actual == set(transferred) | {"EVIDENCE_SHA256.json"}, "Downloaded evidence coverage mismatch")
    for name, digest in transferred.items():
        check_hash(child(remote_root, name), digest)
    upload = read_json(ROOT / "remote_check/FINAL_UPLOAD.json")
    check_hash(ROOT / "remote_check" / Path(upload["archive"]).name, upload["sha256"])
    require(read_json(remote_root / "final_source/FINAL_TRANSFER_INPUTS.json") == upload["files"],
            "Returned uploaded-input catalog mismatch")
    for name, digest in hash_map(upload["files"], "uploaded verifier inputs").items():
        check_hash(child(ROOT, name), digest)
        check_hash(child(remote_root / "final_source", name), digest)
    require(read_json(remote_root / "final_source/evidence/FINAL_INPUTS.json") == inputs,
            "Independent input catalog differs from current inputs")
    launch = read_json(remote_root / "FINAL_LAUNCH.json")
    require(launch["runner_sha256"] == PINS["verify_combined.py"] and
            launch["source_archive_sha256"] == upload["sha256"] and
            launch["combined_sha256"] == inputs["source_sha256"], "Independent launch mismatch")

    result_paths = [ROOT / "evidence/local_combined/RESULT.json",
                    remote_root / "final_verification/RESULT.json"]
    results, dependency_maps = [], []
    for path in result_paths:
        row = read_json(path)
        require(row.get("passed") is True and row.get("exit_code") == 0
                and row.get("reconstruction_verified") is True, "Combined check incomplete: " + str(path))
        require(row["source_sha256_before"] == row["source_sha256_after"] == inputs["source_sha256"]
                and row["source_hashes"] == sources, "Combined source identity mismatch")
        require(row["runner_sha256"] == PINS["verify_combined.py"] and row["compiler_sha256"] == COMPILER_SHA,
                "Combined verifier/compiler pin mismatch")
        require(row["dependency_pins"] == lock["packages"], "Dependency source pins mismatch")
        logs = check_log(path.parent / "combined.log", row["log_sha256"], set(names), audit)
        require(logs == row["axiom_audits"] and len(logs) == 90, "Combined log/report audit mismatch")
        require(all(set(value) <= STANDARD_AXIOMS for value in logs.values()), "Nonstandard combined axiom")
        manifest = path.parent / "DEPENDENCY_ARTIFACTS.json"
        check_hash(manifest, row["dependency_manifest_sha256"])
        dependencies = hash_map(read_json(manifest), "external dependency artifacts")
        require(len(dependencies) == row["dependency_artifacts"] == 9868, "Dependency artifact count mismatch")
        require(not any(name.startswith("NDEAEvolve/") or PurePosixPath(name).name.startswith(
            ("Exp007Foundation.", "Exp008Combined.", "CombinedVerification.")) for name in dependencies),
            "Project artifact in isolated dependencies")
        timestamp(row)
        require(datetime.datetime.fromisoformat(row["end_utc"]) >= timestamp(row), "Invalid combined end timestamp")
        elapsed(row, str(path))
        results.append(row)
        dependency_maps.append(dependencies)
    local, remote = results
    require(local["axiom_audits"] == remote["axiom_audits"], "Cross-environment axiom disagreement")
    require(transfer["result_sha256"] == sha(result_paths[1]), "Transfer/result identity mismatch")
    require(dependency_maps[0] == dependency_maps[1], "Cross-environment dependency paths or hashes differ")
    check_hash(Path(local["command"][0]), COMPILER_SHA)

    local_modules = {}
    for name in MODULES:
        digest = sources["lean/" + name + ".lean"]
        candidates = []
        for path in sorted((ROOT / "evidence").glob("20*_*" + name + ".json")):
            row = read_json(path)
            if row.get("source_sha256_before") == digest or row.get("source_sha256_after") == digest:
                candidates.append((timestamp(row), str(path), path, row))
        require(bool(candidates), "No matching local module receipt: " + name)
        _, _, path, row = max(candidates)
        require(row.get("exit_code") == 0 and row.get("sources_unchanged") is True and
                row["source_sha256_before"] == row["source_sha256_after"] == digest,
                "Latest matching local module has not passed: " + name)
        require(row["runner_sha256"] == PINS["run_lean.py"] and
                row["lean_binary_sha256"] == COMPILER_SHA and row["mathlib_commit"] == MATHLIB_COMMIT,
                "Local modular runner/compiler/source pin mismatch: " + name)
        require(Path(row["source"]).name == name + ".lean" and
                Path(row["log"]).name == path.with_suffix(".log").name, "Local module path mismatch: " + name)
        logged = check_log(path.with_suffix(".log"), row["log_sha256"], module_audits[name], audit)
        local_modules[name] = {**receipt(path), "source_sha256": digest,
                               "log": receipt(path.with_suffix(".log")),
                               "axiom_audits": logged, "elapsed_seconds": elapsed(row, name)}

    # A successful module row remains evidence even if a later module in its batch failed.
    starter = ROOT / "remote_check/start_modules.py"
    templates = [node.value.func.value.value for node in ast.parse(starter.read_text()).body
                 if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "code" for t in node.targets)
                 and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
                 and isinstance(node.value.func.value, ast.Constant)]
    require(len(templates) == 1 and isinstance(templates[0], str), "Cannot identify pinned modular runner template")
    remote_candidates = {name: [] for name in MODULES}
    for path in sorted((remote_root / "development/batches").glob("*/RESULT.json")):
        batch = read_json(path)
        for row in batch["modules"]:
            name = row["module"]
            if name in remote_candidates:
                digest = sources["lean/" + name + ".lean"]
                if row.get("source_sha256_before") == digest or row.get("source_sha256_after") == digest:
                    remote_candidates[name].append((timestamp(batch), str(path), path, batch, row))
    remote_modules = {}
    for name in MODULES:
        require(bool(remote_candidates[name]), "No matching independent module row: " + name)
        _, _, path, batch, row = max(remote_candidates[name], key=lambda item: item[:2])
        digest = sources["lean/" + name + ".lean"]
        require(row.get("exit_code") == 0 and row["source_sha256_before"] == row["source_sha256_after"] == digest,
                "Latest matching independent module row has not passed: " + name)
        require(batch["compiler_sha256"] == COMPILER_SHA, "Independent modular compiler mismatch")
        request = batch["request"]
        require(request["batch"] == path.parent.name and request["modules"].count(name) == 1 and
                request["source_hashes"][name + ".lean"] == digest, "Independent module request mismatch")
        require(read_json(ROOT / "remote_check" / (request["batch"] + "_REQUEST.json")) == request,
                "Independent/local saved modular requests differ")
        check_hash(ROOT / "remote_check" / Path(request["archive"]).name, request["sha256"])
        job = remote_root / ("run_modules_" + request["batch"] + ".py")
        require(job.read_text() == templates[0].replace("REQUEST", repr(request)),
                "Independent modular runner differs from pinned template")
        src = path.parent / "source" / (name + ".lean")
        log = path.parent / (name + ".log")
        check_hash(src, digest)
        logged = check_log(log, row["log_sha256"], module_audits[name], audit)
        remote_modules[name] = {**receipt(path), "batch": request["batch"],
                                "batch_passed": batch.get("passed") is True,
                                "module_exit_code": 0, "source": receipt(src), "log": receipt(log),
                                "runner": receipt(job), "axiom_audits": logged,
                                "elapsed_seconds": elapsed(row, name)}

    numeric_path = ROOT / "evidence/numerical_checks.json"
    numeric = read_json(numeric_path)
    require(numeric.get("passed") is True, "Numerical diagnostics have not passed")
    check_hash(ROOT / "numerical_checks.py", numeric["source_sha256"])
    preserve_path = ROOT / "evidence/PREDECESSOR_PRESERVATION.json"
    preserve = read_json(preserve_path)
    require(preserve.get("passed") is True, "Predecessor preservation has not passed")
    require(len(preserve["checks"]) == len(PREDECESSORS) and
            {row["name"] for row in preserve["checks"]} == set(PREDECESSORS), "Predecessor check coverage mismatch")
    for row in preserve["checks"]:
        count, digest = PREDECESSORS[row["name"]]
        require(row.get("passed") is True and row["failures"] == [] and
                row["expected_entry_count"] == row["entry_count"] == row["matched_entry_count"] == count and
                row["expected_manifest_sha256"] == row["manifest_sha256_before"] == row["manifest_sha256_after"] == digest,
                "Predecessor preservation receipt mismatch: " + row["name"])
        check_hash(Path(row["manifest_path"]), digest)

    # Recheck current inputs after reading all evidence; write no success receipt on failure.
    for name, digest in sources.items():
        check_hash(child(ROOT, name), digest)
    check_hash(combined, inputs["source_sha256"])
    require(read_json(inputs_path) == inputs, "Final inputs changed during finalization")
    completed = datetime.datetime.now(datetime.timezone.utc).isoformat()
    cross = {"passed": True, "completed_utc": completed, "same_module_artifact_paths": True,
             "local_artifact_count": len(dependency_maps[0]), "independent_artifact_count": len(dependency_maps[1]),
             "identical_artifact_hashes": len(dependency_maps[0]), "mismatches": [],
             "local_manifest": receipt(result_paths[0].parent / "DEPENDENCY_ARTIFACTS.json"),
             "independent_manifest": receipt(result_paths[1].parent / "DEPENDENCY_ARTIFACTS.json")}
    cross_path = ROOT / "evidence/CROSS_ENVIRONMENT_DEPENDENCIES.json"
    record = {"passed": True, "completed_utc": completed, "source_sha256": inputs["source_sha256"],
              "production_theorems": 83, "controls": 7, "total_audits": len(names),
              "allowed_axioms": sorted(STANDARD_AXIOMS), "reconstruction_verified": True,
              "local_result": relative(result_paths[0]), "local_result_sha256": sha(result_paths[0]),
              "independent_result": relative(result_paths[1]), "independent_result_sha256": sha(result_paths[1]),
              "local_elapsed_seconds": local["elapsed_seconds"], "independent_elapsed_seconds": remote["elapsed_seconds"],
              "local_modular_receipts": local_modules, "independent_modular_receipts": remote_modules,
              "local_modular_total_seconds": sum(row["elapsed_seconds"] for row in local_modules.values()),
              "independent_modular_total_seconds": sum(row["elapsed_seconds"] for row in remote_modules.values()),
              "independent_transfer_checked": True, "transfer": receipt(transfer_path),
              "transferred_evidence_files": len(transferred), "final_inputs": receipt(inputs_path),
              "compiler_sha256": COMPILER_SHA, "verifier_pins": PINS, "finalizer_sha256": sha(Path(__file__)),
              "dependency_artifacts_per_combined_run": len(dependency_maps[0]),
              "identical_cross_environment_dependency_hashes": len(dependency_maps[0]),
              "numeric_receipt": receipt(numeric_path), "predecessor_receipt": receipt(preserve_path),
              "numerical_stage_cases": len(numeric["stage_checks"]),
              "numerical_stage_equations": 3 * len(numeric["stage_checks"]),
              "numerical_global_checks": len(numeric["global_checks"]),
              "predecessor_manifest_entries": {row["name"]: row["entry_count"] for row in preserve["checks"]},
              "qualification": "All project source re-elaborated in both combined runs. Pinned compatible external artifacts reused; compiler and libraries were not rebuilt from source.",
              "scope": "Fixed finite signed Fourier spectrum for constant noncommuting spinor matrices; alias-free periodic grids; arbitrary numerical initial error retained."}
    cross_bytes = (json.dumps(cross, indent=2) + "\n").encode()
    record["cross_environment_dependencies"] = {"path": relative(cross_path),
        "sha256": hashlib.sha256(cross_bytes).hexdigest()}
    final_path = ROOT / "evidence/FINAL_VERIFICATION.json"
    require(not cross_path.exists() and not final_path.exists(), "Refusing to overwrite final verification receipts")
    with cross_path.open("xb") as stream:
        stream.write(cross_bytes)
    with final_path.open("x") as stream:
        stream.write(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"passed": True, "total_audits": len(names), "production_theorems": 83,
                      "controls": 7, "dependency_artifacts": len(dependency_maps[0]),
                      "final_verification": str(final_path)}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print("Exp008 finalization refused: " + str(error), file=sys.stderr)
        raise SystemExit(1)
