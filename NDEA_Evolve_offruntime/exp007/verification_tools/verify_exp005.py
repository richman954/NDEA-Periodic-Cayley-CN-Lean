#!/usr/bin/env python3
"""Portable, fail-closed integrity and fresh-proof checker for frozen Exp005.

Python 3.10+, Git, and a POSIX host (Linux/macOS/WSL). No installation or
network access is initiated. Proof mode requires pinned Lean and a compatible
package cache; see README.md. All outputs go into a NEW work directory.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time

sys.dont_write_bytecode = True


COMMIT = "1cb91755d0c8a6c681334907785de58b0bf53d6c"
TAG = "exp005-mesh-weighted-residual-bridge-verified-final-20260907"
TAG_OBJECT = "f2e696607209c2a071af99858d0212f6f969e632"
PREDECESSOR = "956ce8acac594c45cf576b66972a082c89190bf8"
PREDECESSOR_TAG = "exp004-symmetric-cayley-second-order-verified-final-20260907"
EXP = "experiments/exp005_mesh_weighted_residual_bridge"
MANIFEST = f"{EXP}/evidence/FINAL_SHA256SUMS"
MANIFEST_SHA = "8a6dddcfdd6f29034397bd950b3098399177ee1eb892edfa91656d0fb11c692a"
LEAN_COMMIT = "68218e876d2a38b1985b8590fff244a83c321783"
ARTIFACTS = {
    "exp005_verified_final_source.tar.gz":
        "308fa3cc3feebc7273c394446d953bc523bdc4d54ac13f5b232063af628b727f",
    "exp005_verified_final.bundle":
        "b63b89b0437ba6efb2550a929f69a0786b728ed704cb6c6a1538297dce72d5c7",
    "DELIVERY_RECEIPT.json":
        "a4d8991dc8a01ae96f08e60cc376eec52bb88dba540917ce896f223e02e5a91a",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_COUNTS = {"MeshWeightedStability.lean": 15, "SymmetricStageResidual.lean": 11,
                "MeshFamilyConvergence.lean": 3, "NegativeControls.lean": 11}
REQUIRED_ENDPOINTS = {
    "NDEAEvolve.Exp005.symmetric_stage_residual_identity",
    "NDEAEvolve.Exp005.symmetric_stage_residual_fixed_time_error",
    "NDEAEvolve.Exp005.symmetric_stage_mesh_family_error_tendsto_zero",
}


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def safe_relative(name: str) -> str:
    path = PurePosixPath(name)
    require(bool(name) and name != "." and not path.is_absolute() and path.as_posix() == name
            and ".." not in path.parts and "\\" not in name
            and not re.match(r"^[A-Za-z]:", name)
            and all(ord(c) >= 32 and ord(c) != 127 for c in name),
            f"Unsafe/noncanonical relative path: {name!r}")
    return name


def regular_under(root: Path, path: Path) -> None:
    require(root.is_dir() and not root.is_symlink(), f"Invalid root: {root}")
    try:
        relative = path.absolute().relative_to(root.absolute())
    except ValueError as error:
        raise VerificationError(f"Path is outside root: {path}") from error
    current = root
    for component in relative.parts:
        require(component not in ("", ".", ".."), f"Unsafe component: {path}")
        current = current / component
        require(not current.is_symlink(), f"Symlinks are not permitted: {current}")
    require(path.is_file() and stat.S_ISREG(path.stat().st_mode),
            f"Missing/nonregular file: {path}")


def verify_sha256(path: Path, expected: str) -> None:
    require(re.fullmatch(r"[0-9a-f]{64}", expected) is not None, "Invalid expected SHA-256")
    require(path.is_file() and not path.is_symlink(), f"Missing/nonregular artifact: {path}")
    require(stat.S_ISREG(path.stat().st_mode), f"Not a regular artifact: {path}")
    require(sha256(path) == expected, f"SHA-256 mismatch: {path}")


def parse_manifest(text: str) -> dict[str, str]:
    entries: dict[str, str] = {}
    for line in text.splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, f"Malformed checksum row: {line!r}")
        digest, name = match.groups()
        safe_relative(name)
        require(name not in entries, f"Duplicate manifest path: {name}")
        entries[name] = digest
    require(bool(entries), "Empty checksum manifest")
    return entries


def verify_manifest(root: Path, manifest: Path) -> int:
    regular_under(root, manifest)
    entries = parse_manifest(manifest.read_text(encoding="utf-8"))
    for name, digest in entries.items():
        path = root / name
        regular_under(root, path)
        verify_sha256(path, digest)
    return len(entries)


def validate_tar_members(archive: tarfile.TarFile) -> None:
    seen: dict[str, bool] = {}
    for member in archive.getmembers():
        name = member.name.rstrip("/") if member.isdir() else member.name
        safe_relative(name)
        require(name not in seen, f"Duplicate archive path: {name}")
        require(member.isdir() or member.isreg(), f"Unsafe archive member type: {name}")
        seen[name] = member.isdir()
    for name in seen:
        for parent in PurePosixPath(name).parents:
            if str(parent) != "." and str(parent) in seen:
                require(seen[str(parent)], f"Archive file/directory collision: {name}")


def code_only(text: str) -> str:
    """Blank nested Lean comments and strings; reject incomplete lexical input."""
    output = list(text)
    index, depth, in_string = 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair in ("/-", "-/"):
                output[index:index + 2] = "  "
                depth += 1 if pair == "/-" else -1
                index += 2
                continue
            output[index] = "\n" if text[index] == "\n" else " "
        elif in_string:
            if text[index] == "\\":
                require(index + 1 < len(text), "Unterminated Lean string escape")
                output[index:index + 2] = "  "
                index += 2
                continue
            if text[index] == '"':
                in_string = False
            output[index] = "\n" if text[index] == "\n" else " "
        elif pair == "/-":
            depth = 1
            output[index:index + 2] = "  "
            index += 2
            continue
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end == -1 else end
            output[index:end] = " " * (end - index)
            index = end
            continue
        elif text[index] == '"':
            in_string = True
            output[index] = " "
        index += 1
    require(depth == 0 and not in_string, "Unterminated Lean comment or string")
    return "".join(output)


def scan_proof_policy(text: str) -> None:
    match = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code_only(text))
    require(match is None, f"Prohibited proof token: {match.group() if match else ''}")


def validate_axiom_log(text: str, expected_names: set[str]) -> dict[str, set[str]]:
    require(bool(expected_names), "Empty expected axiom audit set")
    require(re.search(r"\berror:|\bsorryAx\b|declaration uses .sorry.", text) is None,
            "Compiler log contains an error or placeholder dependency")
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    rows += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    found: dict[str, set[str]] = {}
    for name, raw in rows:
        require(name not in found, f"Duplicate compiled axiom audit: {name}")
        dependencies = set(filter(None, (item.strip() for item in raw.split(","))))
        require(dependencies <= ALLOWED_AXIOMS, f"Unapproved axioms for {name}: {dependencies}")
        found[name] = dependencies
    require(set(found) == expected_names,
            f"Axiom coverage mismatch: missing={sorted(expected_names - set(found))}; "
            f"extra={sorted(set(found) - expected_names)}")
    return found


def create_fresh_workdir(path: Path) -> Path:
    path = path.absolute()
    require(path.parent.is_dir(), f"Work directory parent does not exist: {path.parent}")
    try:
        path.mkdir()
    except OSError as error:
        raise VerificationError(f"Refusing existing/uncreatable work directory: {path}") from error
    return path.resolve()


class Checker:
    def __init__(self, args: argparse.Namespace, work: Path) -> None:
        self.args, self.work = args, work
        self.repo = work / "source"
        self.archive_root = work / "archive" / "NDEA_Evolve"
        self.logs = work / "logs"
        self.logs.mkdir()
        self.artifacts = args.artifacts.resolve()
        self.env = dict(os.environ)
        for key in list(self.env):
            if key in ("LEAN_PATH", "LEAN_SRC_PATH") or key.startswith("GIT_"):
                self.env.pop(key)
        self.env.update({"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                         "GIT_TERMINAL_PROMPT": "0", "GIT_OPTIONAL_LOCKS": "0", "LEAN_NUM_THREADS": "1",
                         "PYTHONDONTWRITEBYTECODE": "1"})
        self.report = {"schema": "ndea.exp005.portable-verification.v1", "start_utc": now(),
            "mode": args.mode, "expected_commit": COMMIT, "work_directory": str(work),
            "verifier_sha256": sha256(Path(__file__)), "platform": sys.platform,
            "python": sys.version, "commands": [], "integrity_passed": False,
            "proof_rebuild_passed": False, "passed": False,
            "scope": "Checks the frozen conditional Exp005 statements, not PDE consistency or well-posedness."}
        self.save()

    def save(self) -> None:
        target = self.work / "RESULT.json"
        temporary = self.work / "RESULT.json.tmp"
        temporary.write_text(json.dumps(self.report, indent=2) + "\n", encoding="utf-8")
        temporary.replace(target)

    def run(self, label: str, command: list[str], *, cwd: Path | None = None,
            sources: list[Path] | None = None, outputs: list[Path] | None = None) -> str:
        log = self.logs / f"{len(self.report['commands']) + 1:03d}_{label}.log"
        before = {str(path): sha256(path) for path in (sources or [])}
        record = {"label": label, "command": command, "cwd": str(cwd or self.work),
                  "start_utc": now(), "timeout_seconds": self.args.timeout, "log": str(log),
                  "source_sha256_before": before, "exit_code": None}
        self.report["commands"].append(record)
        self.save()
        print(f"START {label}", flush=True)
        begin, process = time.monotonic(), None
        try:
            with log.open("xb") as stream:
                process = subprocess.Popen(command, cwd=cwd or self.work, env=self.env,
                                           stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                while True:
                    remaining = self.args.timeout - (time.monotonic() - begin)
                    if remaining <= 0:
                        raise subprocess.TimeoutExpired(command, self.args.timeout)
                    try:
                        record["exit_code"] = process.wait(timeout=min(30, remaining))
                        break
                    except subprocess.TimeoutExpired:
                        print(f"  {label}: {int(time.monotonic() - begin)} seconds", flush=True)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            record["exit_code"] = 124 if time.monotonic() - begin >= self.args.timeout else 130
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
            raise
        finally:
            record.update({"end_utc": now(), "elapsed_seconds": round(time.monotonic() - begin, 6),
                "source_sha256_after": {str(path): sha256(path) for path in (sources or [])},
                "log_sha256": sha256(log) if log.is_file() else None,
                "output_sha256": {str(path): sha256(path) for path in (outputs or []) if path.is_file()}})
            self.save()
        content = log.read_text(encoding="utf-8", errors="replace")
        require(record["exit_code"] == 0, f"{label} failed: see {log}\n{content[-4000:]}")
        require(before == record["source_sha256_after"], f"Sources changed during {label}")
        print(f"PASS {label} ({record['elapsed_seconds']} seconds)", flush=True)
        return content

    def git(self, label: str, *args: str, repo: Path | None = None) -> str:
        return self.run(label, ["git", "-c", f"core.hooksPath={os.devnull}", "-c",
                               "core.autocrlf=false", "-C", str(repo or self.repo), *args])

    def check_inputs(self) -> None:
        for name, digest in ARTIFACTS.items():
            verify_sha256(self.artifacts / name, digest)
        self.report["artifact_sha256"] = ARTIFACTS
        receipt = json.loads((self.artifacts / "DELIVERY_RECEIPT.json").read_text())
        require(receipt.get("passed") is True and receipt.get("expected_commit") == COMMIT,
                "Pinned delivery receipt does not attest the expected release")

    def check_tree(self, root: Path) -> None:
        verify_sha256(root / MANIFEST, MANIFEST_SHA)
        require(verify_manifest(root, root / MANIFEST) == 889, "Unexpected manifest size")
        listed = set(parse_manifest((root / MANIFEST).read_text())) | {MANIFEST}
        require(listed == self.committed_paths, "Manifest coverage differs from committed tree")

    def integrity(self) -> None:
        self.check_inputs()
        bundle = self.artifacts / "exp005_verified_final.bundle"
        self.run("clone_bundle", ["git", "-c", f"core.hooksPath={os.devnull}", "clone",
                 "--no-checkout", str(bundle), str(self.repo)])
        self.git("checkout_release", "checkout", "--detach", COMMIT)
        self.git("verify_bundle", "bundle", "verify", str(bundle))
        require(self.git("release_head", "rev-parse", "HEAD").strip() == COMMIT, "Wrong HEAD")
        require(self.git("release_tag", "rev-parse", f"{TAG}^{{commit}}").strip() == COMMIT, "Wrong tag")
        require(self.git("release_tag_object", "rev-parse", TAG).strip() == TAG_OBJECT, "Wrong tag object")
        require(self.git("predecessor_tag", "rev-parse", f"{PREDECESSOR_TAG}^{{commit}}").strip()
                == PREDECESSOR, "Wrong predecessor tag")
        self.git("predecessor_ancestor", "merge-base", "--is-ancestor", PREDECESSOR, COMMIT)
        self.committed_paths = set(filter(None, self.git("release_file_list", "ls-tree", "-r",
                                                    "--name-only", "-z", COMMIT).split("\0")))
        require(len(self.committed_paths) == 890, "Unexpected release file count")
        for name in self.committed_paths:
            safe_relative(name)
        protected = set(filter(None, self.git("predecessor_file_list", "ls-tree", "-r",
                                             "--name-only", "-z", PREDECESSOR).split("\0")))
        changed = set(filter(None, self.git("predecessor_diff", "diff", "--no-renames",
                                           "--name-only", "-z", PREDECESSOR, COMMIT).split("\0")))
        require(len(protected) == 806 and not protected.intersection(changed), "Predecessor files changed")
        self.check_tree(self.repo)
        archive_path = self.artifacts / "exp005_verified_final_source.tar.gz"
        with tarfile.open(archive_path, "r:gz") as archive:
            validate_tar_members(archive)
            regular = [member for member in archive.getmembers() if member.isreg()]
            require({member.name for member in regular} ==
                    {"NDEA_Evolve/" + name for name in self.committed_paths},
                    "Archive file list differs from committed tree")
            destination = self.work / "archive"
            destination.mkdir()
            for member in regular:
                target = destination / member.name
                target.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(member)
                require(source is not None, f"Cannot read archive member: {member.name}")
                with source, target.open("xb") as stream:
                    shutil.copyfileobj(source, stream)
        self.check_tree(self.archive_root)
        require(self.git("source_clean", "status", "--porcelain=v1", "--untracked-files=all") == "",
                "Restored source is not clean")
        self.report.update({"integrity_passed": True, "manifest_entries": 889,
                            "release_files": 890, "predecessor_files_unchanged": 806})
        self.save()

    def package_state(self, packages: Path) -> list[dict]:
        pinned = json.loads((self.repo / "lake-manifest.json").read_text())["packages"]
        records = []
        for package in pinned:
            root = packages / safe_relative(package["name"])
            revision = self.git(f"package_{package['name']}_head", "rev-parse", "HEAD", repo=root).strip()
            clean = self.git(f"package_{package['name']}_clean", "status", "--porcelain=v1",
                             "--untracked-files=no", repo=root)
            require(revision == package["rev"] and clean == "",
                    f"Dependency revision/worktree mismatch: {package['name']}")
            records.append({"name": package["name"], "revision": revision, "root": str(root)})
        return records

    def proof(self) -> None:
        require(self.args.packages is not None, "Proof mode requires --packages DIR; see README.md")
        packages = self.args.packages.resolve(strict=True)
        elan_root = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
        selected = self.args.lean or elan_root / "toolchains/leanprover--lean4---v4.31.0/bin/lean"
        lean = selected.resolve(strict=True)
        require(lean.is_file() and lean.name != "elan", "Pass the real pinned Lean binary, not an elan shim")
        version = self.run("lean_version", [str(lean), "--version"], cwd=self.repo)
        require("version 4.31.0," in version and LEAN_COMMIT in version and "Release" in version,
                f"Unexpected Lean toolchain: {version.strip()}")
        library = lean.parent.parent / "lib/lean"
        require(library.is_dir(), "Cannot locate the pinned toolchain's core library")
        self.report["compiler"] = {"path": str(lean), "sha256": sha256(lean), "version": version.strip()}
        dependency_state = self.package_state(packages)
        self.report["packages"] = dependency_state
        generator = self.repo / EXP / "assurance/make_combined_verification.py"
        spec = importlib.util.spec_from_file_location("frozen_exp005_sources", generator)
        require(spec is not None and spec.loader is not None, "Cannot load verified source catalog")
        catalog = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(catalog)
        predecessors, production = catalog.source_groups(self.repo)
        controls = self.repo / EXP / "controls/lean/NegativeControls.lean"
        require(len(predecessors) == 10 and len(production) == 3, "Wrong source-chain length")
        expected: set[str] = set()
        per_file: dict[Path, set[str]] = {}
        for source in production + [controls]:
            text = source.read_text(encoding="utf-8")
            scan_proof_policy(text)
            code = code_only(text)
            names = re.findall(r"^\s*#print\s+axioms\s+(\S+)", code, re.MULTILINE)
            require(len(names) == len(set(names)) == AUDIT_COUNTS[source.name], "Wrong source audit count")
            public = re.findall(r"^\s*(?:theorem|lemma)\s+([^\s:{(]+)", code, re.MULTILINE)
            require({name.rsplit(".", 1)[-1] for name in names} == set(public), "Public theorem audit mismatch")
            require(not expected.intersection(names), "Repeated public theorem across files")
            per_file[source] = set(names)
            expected.update(names)
        require(len(expected) == 40 and REQUIRED_ENDPOINTS <= expected, "Missing principal endpoints")
        originals = [self.repo / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean",
                     self.repo / "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean"]
        for original, shadow in zip(originals, predecessors[:2]):
            require(catalog.filtered_source(original, False) == catalog.filtered_source(shadow, False),
                    "Predecessor shadow differs beyond imports")
        lib = self.work / "build/lib/lean"
        lib.mkdir(parents=True)
        helper = self.repo / "experiments/exp003_exact_order_defect_norm_bound/assurance/lean_import_closure.py"
        command = [sys.executable, "-B", str(helper)]
        for package in dependency_state:
            command += ["--root", package["root"], "--artifact-root",
                        str(Path(package["root"]) / ".lake/build/lib/lean")]
        command += ["--copy-artifacts-to", str(lib), "--report-artifact-bytes"]
        command += catalog.external_imports(predecessors + production + [controls])
        self.run("copy_dependency_cache", command, sources=[helper, generator, *predecessors, *production, controls])
        require(not (lib / "NDEAEvolve").exists(), "Project artifacts must not be copied from a cache")
        cached = {str(path.relative_to(lib)): sha256(path) for path in sorted(lib.rglob("*")) if path.is_file()}
        require(bool(cached), "Empty dependency cache; install compatible Mathlib artifacts first")
        cache_manifest = self.work / "DEPENDENCY_ARTIFACTS.json"
        cache_manifest.write_text(json.dumps(cached, indent=2) + "\n", encoding="utf-8")
        self.report["dependency_cache"] = {"artifact_count": len(cached), "sha256": sha256(cache_manifest),
            "manifest": str(cache_manifest), "project_cache_initially_empty": True,
            "trust_boundary": "Pinned dependency sources checked; compatible cached dependency artifacts reused, not rebuilt."}
        self.env["LEAN_PATH"] = str(lib) + os.pathsep + str(library)
        self.report["lean_path"] = self.env["LEAN_PATH"]
        shadow_root = self.repo / "experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources"
        completed = []
        for source in predecessors + production + [controls]:
            root = shadow_root if source.is_relative_to(shadow_root) else self.repo
            command = [str(lean), "-j", "1", "-R", str(root)]
            outputs = []
            if source != controls:
                target = lib / source.relative_to(root).with_suffix(".olean")
                require(not target.exists(), f"Refusing existing project output: {target}")
                target.parent.mkdir(parents=True, exist_ok=True)
                command += ["-o", str(target)]
                outputs = [target]
            content = self.run(source.stem, command + [str(source)], cwd=self.repo,
                               sources=[source], outputs=outputs)
            require(re.search(r"\berror:|\bsorryAx\b", content) is None, "Compiler emitted an error")
            if source in per_file:
                validate_axiom_log(content, per_file[source])
            completed.append(source.stem)
        combined = self.work / "CombinedExp005Controls.lean"
        self.run("generate_combined", [sys.executable, "-B", str(generator), "--repo", str(self.repo),
                 "--output", str(combined), "--controls"], sources=[generator, *predecessors, *production, controls],
                 outputs=[combined])
        combined_text = combined.read_text(encoding="utf-8")
        require(re.search(r"^\s*import\s+NDEAEvolve\.", combined_text, re.MULTILINE) is None,
                "Combined source must not import project artifacts")
        scan_proof_policy(combined_text)
        # Exclude freshly built project artifacts as well as old artifacts from this route.
        self.env["LEAN_PATH"] = str(self.work / "combined_dependencies") + os.pathsep + str(library)
        combined_lib = self.work / "combined_dependencies"
        combined_lib.mkdir()
        for name in cached:
            target = combined_lib / name
            target.parent.mkdir(parents=True, exist_ok=True)
            os.link(lib / name, target)
        content = self.run("combined_controls", [str(lean), "-j", "1", str(combined)],
                           sources=[combined, generator, *predecessors, *production, controls])
        rows = validate_axiom_log(content, expected)
        require(self.package_state(packages) == dependency_state, "Dependency state changed during verification")
        self.check_inputs()
        self.check_tree(self.repo)
        self.check_tree(self.archive_root)
        require(self.git("source_postflight_clean", "status", "--porcelain=v1", "--untracked-files=all") == "",
                "Frozen restored source was modified")
        self.report.update({"proof_rebuild_passed": True, "modular_invocations": completed,
            "axiom_audits": {name: sorted(deps) for name, deps in rows.items()},
            "combined_project_imports": False, "allowed_axioms": sorted(ALLOWED_AXIOMS)})


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, default=Path(__file__).resolve().parent / "release")
    parser.add_argument("--work-dir", type=Path, help="NEW directory; existing paths are refused")
    parser.add_argument("--mode", choices=("integrity", "proof"), default="integrity")
    parser.add_argument("--packages", type=Path, help="Existing pinned .lake/packages directory, used read-only")
    parser.add_argument("--lean", type=Path, help="Actual Lean 4.31.0 toolchain binary, not an elan shim")
    parser.add_argument("--timeout", type=int, default=900, help="Timeout per external command in seconds")
    parser.add_argument("--lock-file", type=Path,
                        default=Path(tempfile.gettempdir()) / "exp003_lean_one_job.lock")
    args = parser.parse_args()
    if os.name != "posix" or sys.version_info < (3, 10):
        parser.error("Use Python 3.10+ on Linux, macOS, or WSL")
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    checker = None
    try:
        work = (create_fresh_workdir(args.work_dir) if args.work_dir else
                Path(tempfile.mkdtemp(prefix="exp005_verify_")))
        checker = Checker(args, work)
        checker.integrity()
        if args.mode == "proof":
            with args.lock_file.open("a") as lock:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError as error:
                    raise VerificationError("Another verifier holds the shared Lean lock") from error
                checker.proof()
        checker.report["passed"] = True
        checker.report["verdict"] = ("FRESH_PROOF_CHECK_PASSED" if args.mode == "proof" else
                                     "INTEGRITY_ONLY_PASSED_NO_PROOF_REBUILD")
        return 0
    except (VerificationError, OSError, ValueError, subprocess.TimeoutExpired, KeyboardInterrupt) as error:
        if checker is not None:
            checker.report.update({"error": str(error), "verdict": "FAILED_OR_INCOMPLETE"})
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    finally:
        if checker is not None:
            checker.report["end_utc"] = now()
            checker.save()
            print(json.dumps({"passed": checker.report["passed"],
                              "verdict": checker.report.get("verdict", "INCOMPLETE"),
                              "result": str(checker.work / "RESULT.json")}, indent=2), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
