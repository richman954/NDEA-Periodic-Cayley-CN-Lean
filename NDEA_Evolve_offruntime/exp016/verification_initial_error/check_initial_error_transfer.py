#!/usr/bin/env python3
"""Source-only, fail-closed development check; NOT the Exp016 release gate.

Prepare resolves the actual local import closure without a Lean installation.
Run compiles every local dependency from the recorded sources, then audits the
candidate's public declarations. Outputs must be outside the checkout. External
Lean/Mathlib artifacts remain trusted dependencies, explicitly recorded below.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

TARGET = "InitialErrorTransfer"
SOURCE = "NDEA_Evolve_offruntime/exp016/lean/InitialErrorTransfer.lean"
BASELINE_BLOB = "32e149dda788b429d77db9fe15ef4cd07543cde3"
LEAN_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
MATHLIB_REV = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
PINS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
EXTERNAL = {"Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph"}
DECLARATIONS = (
    "sampledInitialState_sub", "initialCutoffDifference_coefficientNorm_sum",
    "synth_norm_le_coefficientSum", "synth_spatialL2_le_coefficientSum",
    "synth_initialCutoff_spatialL2_le_tail", "sampledInitialCutoff_weighted_norm_le_tail",
    "solution_initialCutoff_spatialL2_le_tail", "sampledCayley_initialCutoff_error_transfer",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def code_only(text: str) -> str:
    """Mask nested comments and strings while preserving lines for import parsing."""
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out[i] = " "; i += 1
        elif text[i] == '"':
            out[i] = " "; i += 1
            closed = False
            while i < len(text):
                char = text[i]
                if char != "\n": out[i] = " "
                i += 1
                if char == "\\" and i < len(text):
                    if text[i] != "\n": out[i] = " "
                    i += 1
                elif char == '"':
                    closed = True; break
            if not closed: raise ValueError("Unterminated Lean string")
        else:
            i += 1
    if depth: raise ValueError("Unterminated Lean comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    code = code_only(text)
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
        raise ValueError("Forbidden proof escape in project source")
    result = []
    for line in code.splitlines():
        if re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\b", line):
            words = re.sub(r"^\s*(?:(?:public|private|meta)\s+)*import\s+", "", line).split()
            if not words or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", x) for x in words):
                raise ValueError("Unsupported import syntax: " + line)
            result.extend(words)
    return result


def resolve(repo: Path) -> list[dict[str, str]]:
    candidates: dict[str, list[Path]] = {}
    roots = []
    for n in range(8, 17):
        exp = repo / "NDEA_Evolve_offruntime" / f"exp{n:03}"
        roots.extend([exp / "lean", exp / "predecessor_sources"])
    for root in roots:
        if root.is_dir():
            for path in root.rglob("*.lean"):
                if path.is_symlink(): raise ValueError("Source symlink: " + str(path))
                name = ".".join(path.relative_to(root).with_suffix("").parts)
                candidates.setdefault(name, []).append(path)
    ordered, visiting, done = [], set(), set()

    def visit(name: str, parent: str) -> None:
        if name.split(".")[0] in EXTERNAL: return
        if name in done: return
        if name in visiting: raise ValueError("Import cycle: " + name)
        paths = candidates.get(name, [])
        if not paths: raise ValueError(f"Missing project source {name!r}, imported by {parent}")
        hashes = {sha(p) for p in paths}
        if len(hashes) != 1:
            raise ValueError("Conflicting project module " + name + ": " + ", ".join(str(p.relative_to(repo)) for p in paths))
        path = sorted(paths)[0]
        visiting.add(name)
        for dep in imports(path.read_text()): visit(dep, str(path.relative_to(repo)))
        visiting.remove(name)
        done.add(name)
        ordered.append({"module": name, "path": str(path.relative_to(repo)), "sha256": sha(path)})

    visit(TARGET, "requested target")
    return ordered


def save(out: Path, name: str, data: dict) -> None:
    (out / name).write_text(json.dumps(data, indent=2) + "\n")


def unchanged(repo: Path, plan: dict) -> None:
    if git(repo, "rev-parse", "HEAD") != plan["commit"]: raise ValueError("Checkout moved after preparation")
    for p, digest in plan["pins"].items():
        if sha(repo / p) != digest: raise ValueError("Changed pin: " + p)
    for item in plan["sources"]:
        if sha(repo / item["path"]) != item["sha256"]: raise ValueError("Changed source: " + item["path"])


def prepare(repo: Path, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=False)
    data = (repo / SOURCE).read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if blob != BASELINE_BLOB: raise ValueError("Candidate is not the inspected unchanged draft; review before repinning")
    plan = {"commit": git(repo, "rev-parse", "HEAD"), "candidate_blob": blob,
            "pins": {p: sha(repo / p) for p in PINS}, "sources": resolve(repo),
            "scope": "InitialErrorTransfer only; not Exp016 qualification"}
    if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.31.0":
        raise ValueError("Unexpected Lean toolchain")
    lock = json.loads((repo / "lake-manifest.json").read_text())
    mathlib = [p for p in lock["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_REV: raise ValueError("Unexpected Mathlib pin")
    deps = out / "deps"; deps.mkdir()
    for p in PINS: shutil.copyfile(repo / p, deps / p)
    source_dir = out / "sources"; source_dir.mkdir()
    for item in plan["sources"]:
        target = source_dir.joinpath(*item["module"].split(".")).with_suffix(".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(repo / item["path"], target)
    save(out, "plan.json", plan)
    save(out, "result.json", {"status": "PREPARED_NOT_VERIFIED", "independent_qualification": False})
    print(f"Prepared {len(plan['sources'])} source modules; no theorem check claimed.")


def checked_command(command: list[str], cwd: Path, env: dict, log: Path, timeout: int = 900) -> None:
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
    print(log.read_text(errors="replace"), end="", flush=True)
    if result.returncode: raise RuntimeError(f"Command failed ({result.returncode}); see {log.name}")


def run(repo: Path, out: Path) -> None:
    plan = json.loads((out / "plan.json").read_text()); unchanged(repo, plan)
    deps = out / "deps"
    for p, digest in plan["pins"].items():
        if sha(deps / p) != digest: raise ValueError("Dependency bootstrap changed pin: " + p)
    lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=deps, text=True).strip()).resolve()
    if sha(lean) != LEAN_SHA256: raise ValueError("Pinned Lean executable SHA-256 mismatch")
    packages = deps / ".lake/packages"
    lock = json.loads((deps / "lake-manifest.json").read_text())
    external_paths, revisions = [], {}
    for p in lock["packages"]:
        if p["type"] != "git": raise ValueError("Unexpected dependency kind")
        package = packages / p["name"]
        rev = git(package, "rev-parse", "HEAD")
        if rev != p["rev"]: raise ValueError("Dependency revision mismatch: " + p["name"])
        revisions[p["name"]] = rev
        external_paths.append(package / ".lake/build/lib/lean")
    build = out / "olean"; build.mkdir(exist_ok=False)
    source_dir = out / "sources"
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"): env.pop(name, None)
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = os.pathsep.join(map(str, [build, *external_paths, lean.parent.parent / "lib/lean"]))
    receipts = []
    for i, item in enumerate(plan["sources"]):
        module = item["module"]
        source = source_dir.joinpath(*module.split(".")).with_suffix(".lean")
        if sha(source) != item["sha256"]: raise ValueError("Staged source changed: " + module)
        target = build.joinpath(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        log = out / f"{i:03}_{module}.log"
        print("Checking", module, flush=True)
        command = [str(lean), "-j", "1", "-R", str(source_dir), "-o", str(target), str(source)]
        checked_command(command, source_dir, env, log)
        if not target.is_file(): raise RuntimeError("Compiler produced no object: " + module)
        receipts.append({**item, "command": command, "log_sha256": sha(log), "olean_sha256": sha(target)})
        save(out, "compiled.json", {"modules": receipts, "complete": False})
    audit = source_dir / "InitialErrorTransferAudit.lean"
    audit.write_text("import InitialErrorTransfer\n" + "\n".join(
        "#print axioms NDEAEvolve.Exp016." + d for d in DECLARATIONS) + "\n")
    log = out / "axioms.log"
    checked_command([str(lean), "-j", "1", str(audit)], source_dir, env, log)
    text = log.read_text()
    for decl in DECLARATIONS:
        name = "NDEAEvolve.Exp016." + decl
        match = re.search(re.escape(name) + r"'?\s+depends on axioms:\s*\[([^\]]*)\]", text, re.S)
        if match:
            axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
            if not axioms <= ALLOWED_AXIOMS: raise ValueError(f"Disallowed axioms for {name}: {axioms}")
        elif not re.search(re.escape(name) + r"'?\s+does not depend on any axioms", text):
            raise ValueError("Missing axiom report: " + name)
    unchanged(repo, plan)
    for item in plan["sources"]:
        if sha(source_dir.joinpath(*item["module"].split(".")).with_suffix(".lean")) != item["sha256"]:
            raise ValueError("Source changed during compilation: " + item["module"])
    save(out, "compiled.json", {"modules": receipts, "complete": True})
    save(out, "result.json", {
        "status": "TARGET_COMPILE_AND_AXIOM_AUDIT_PASS", "commit": plan["commit"],
        "source_count": len(receipts), "target_source_sha256": sha(repo / SOURCE),
        "lean_sha256": sha(lean), "external_revisions": revisions, "axioms_log_sha256": sha(log),
        "checked_declarations": list(DECLARATIONS), "independent_qualification": False,
        "scope_limit": "No Exp016 combined/fresh qualification, external source-artifact proof, or sealed milestone acceptance.",
        "finished_utc": datetime.now(timezone.utc).isoformat()})
    print("TARGET_COMPILE_AND_AXIOM_AUDIT_PASS; Exp016 remains unsealed.", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "run"])
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    if out == repo or repo in out.parents: parser.error("Output must be outside the checkout")
    if args.mode == "prepare" and out.exists(): parser.error("Output already exists; refusing to overwrite")
    try:
        (prepare if args.mode == "prepare" else run)(repo, out)
        return 0
    except Exception as exc:
        print(f"CHECK_BLOCKED_OR_FAILED: {exc}", file=sys.stderr, flush=True)
        if out.is_dir(): save(out, "result.json", {"status": "BLOCKED_OR_FAILED", "error": str(exc), "independent_qualification": False})
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
