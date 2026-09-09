#!/usr/bin/env python3
"""Bootstrap verified development artifacts or retire the active project cache.

The caller owns the shared Lean lock and bounded subprocess timeout. No Lean
process runs here. The Exp004 source tree and old cache are always read-only.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

from make_combined_verification import source_groups


PREDECESSOR = "956ce8acac594c45cf576b66972a082c89190bf8"
OLD_REPO = Path("/home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve")
OLD_RUN = "20260908T002534.597869Z_2"
OLD_EVIDENCE = "experiments/exp004_symmetric_cayley_second_order/evidence"
LEAN = "/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean"
LEAN_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
MATHLIB_COMMIT = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
PACKAGES = Path("/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages")
PACKAGE_BY_PREFIX = {"Mathlib": "mathlib", "Batteries": "batteries", "Qq": "Qq",
    "Aesop": "aesop", "ProofWidgets": "proofwidgets", "ImportGraph": "importGraph",
    "LeanSearchClient": "LeanSearchClient", "Plausible": "plausible"}


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git(repo: Path, *arguments: str) -> str:
    result = subprocess.run(["git", "-C", str(repo), *arguments],
                            capture_output=True, text=True, timeout=60)
    require(result.returncode == 0, f"Git check failed: {repo} {arguments}: {result.stderr}")
    return result.stdout


def copy_verified(source: Path, destination: Path, expected: str, records: list[dict]) -> None:
    require(source.is_file() and not source.is_symlink(), f"Missing/nonregular cache source: {source}")
    before = source.stat()
    digest = sha(source)
    require(digest == expected, f"Source artifact differs from verified hash: {source}")
    existed = destination.exists()
    if existed:
        require(destination.is_file() and not destination.is_symlink() and sha(destination) == digest,
                f"Refusing to overwrite a different destination artifact: {destination}")
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    destination_sha = sha(destination)
    after = source.stat()
    require((before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            == (after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            f"Old cache artifact changed while copying: {source}")
    require(destination_sha == expected, f"Destination artifact hash mismatch: {destination}")
    records.append({"source": str(source), "destination": str(destination),
        "source_sha256": digest, "destination_sha256": destination_sha,
        "size_bytes": after.st_size, "already_present_identically": existed})


def bootstrap(args: argparse.Namespace, report: dict) -> None:
    repo = args.repo.resolve()
    old_cache = args.source_cache.resolve(strict=True)
    cache = args.cache_root.resolve()
    require(cache != old_cache and not cache.is_relative_to(old_cache), "Bootstrap destination overlaps old cache.")
    require(sha(Path(LEAN)) == LEAN_SHA, "Pinned Lean binary changed.")
    require(git(OLD_REPO, "rev-parse", "HEAD").strip() == PREDECESSOR, "Original Exp004 HEAD changed.")
    require(git(OLD_REPO, "status", "--porcelain=v1") == "", "Original Exp004 worktree is dirty.")
    require(git(PACKAGES / "mathlib", "rev-parse", "HEAD").strip() == MATHLIB_COMMIT,
            "Mathlib HEAD is not the pinned revision.")
    require(git(PACKAGES / "mathlib", "status", "--porcelain=v1", "--untracked-files=no") == "",
            "Mathlib tracked source changed.")
    predecessors, _ = source_groups(repo)
    require(len(predecessors) == 10, "Expected exactly ten predecessor project modules.")
    old_lib, new_lib = old_cache / "lib/lean", cache / "lib/lean"
    project_plan: list[tuple[Path, Path, str]] = []
    source_checks: list[dict] = []
    for number, current in enumerate(predecessors, 1):
        relative = current.relative_to(repo)
        original = OLD_REPO / relative
        receipt = repo / OLD_EVIDENCE / "receipts" / f"{OLD_RUN}_{number:03d}_{current.stem}.json"
        record = json.loads(receipt.read_text(encoding="utf-8"))
        require(record.get("stage") == "controls" and record.get("qualification") == "fresh"
                and record.get("exit_code") == 0 and record.get("sources_unchanged") is True
                and not record.get("timed_out", True), f"Unqualified predecessor receipt: {receipt}")
        command = record["command"]
        require(command[0] == LEAN and record.get("lean_binary_sha256") == LEAN_SHA,
                f"Predecessor receipt binary pin mismatch: {receipt}")
        digest = sha(current)
        require(sha(original) == digest
                and record["source_sha256_before"].get(str(original)) == digest
                and record["source_sha256_after"].get(str(original)) == digest,
                f"Current predecessor source differs from final verified input: {current}")
        require(sha(Path(record["log"])) == record["log_sha256"], f"Predecessor log changed: {receipt}")
        outputs = record.get("output_sha256", {})
        require(bool(outputs), f"No explicitly hashed output in predecessor receipt: {receipt}")
        for old_path, output_digest in outputs.items():
            artifact = Path(old_path)
            relative_artifact = artifact.relative_to(old_lib)
            require(relative_artifact.parts[0] == "NDEAEvolve", "Unexpected predecessor artifact namespace.")
            require(sha(artifact) == output_digest, f"Current old-cache output no longer matches final run: {artifact}")
            project_plan.append((artifact, new_lib / relative_artifact, output_digest))
        source_checks.append({"current_source": str(current), "original_source": str(original),
            "source_sha256": digest, "verified_receipt": str(receipt),
            "verified_receipt_sha256": sha(receipt), "final_run_id": OLD_RUN})
    report["predecessor_source_correspondence"] = source_checks
    report["dependency_artifacts"] = []
    for artifact in sorted(old_lib.rglob("*")):
        if not artifact.is_file():
            continue
        relative = artifact.relative_to(old_lib)
        if relative.parts[0] == "NDEAEvolve":
            continue
        prefix = relative.parts[0].split(".", 1)[0]
        require(prefix in PACKAGE_BY_PREFIX, f"Unrecognized cache dependency namespace: {relative}")
        package_artifact = PACKAGES / PACKAGE_BY_PREFIX[prefix] / ".lake/build/lib/lean" / relative
        require(package_artifact.is_file(), f"Dependency lacks a matching pinned-package cache artifact: {relative}")
        expected = sha(package_artifact)
        copy_verified(artifact, new_lib / relative, expected, report["dependency_artifacts"])
        report["dependency_artifacts"][-1]["pinned_package_artifact"] = str(package_artifact)
    report["project_artifacts"] = []
    for artifact, target, digest in project_plan:
        copy_verified(artifact, target, digest, report["project_artifacts"])
    for check in source_checks:
        require(sha(Path(check["current_source"])) == check["source_sha256"]
                and sha(Path(check["original_source"])) == check["source_sha256"],
                "A predecessor source changed during cache bootstrap.")
    report["qualification"] = "Development bootstrap only; fresh final modular and combined checks remain required."
    report["mathlib_commit"] = MATHLIB_COMMIT
    report["lean_binary_sha256"] = LEAN_SHA


def reset(args: argparse.Namespace, report: dict) -> None:
    cache = args.cache_root.resolve()
    active = cache / "lib/lean/NDEAEvolve"
    retired = cache / "retired_project_artifacts" / args.run_id / "NDEAEvolve"
    require(not active.is_symlink(), "Active project cache must not be a symlink.")
    require(not retired.exists(), f"Retired cache destination already exists: {retired}")
    artifacts = []
    if active.exists():
        require(active.is_dir(), "Active project cache is not a directory.")
        for path in sorted(active.rglob("*")):
            if path.is_file():
                require(not path.is_symlink(), f"Project cache contains a symlink: {path}")
                artifacts.append({"relative": str(path.relative_to(active)), "sha256": sha(path)})
        retired.parent.mkdir(parents=True, exist_ok=True)
        active.rename(retired)
    active.mkdir(parents=True, exist_ok=True)
    report.update({"active_project_cache": str(active), "retired_project_cache": str(retired),
                   "retired_artifacts": artifacts, "active_cache_empty": not any(active.iterdir())})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("bootstrap", "reset"))
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--cache-root", required=True, type=Path)
    parser.add_argument("--source-cache", type=Path, default=Path("/tmp/exp004_build"))
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--report", required=True, type=Path)
    args = parser.parse_args()
    require(not args.report.exists(), f"Refusing to overwrite cache receipt: {args.report}")
    report = {"action": args.action, "start_utc": now(), "run_id": args.run_id,
              "helper_sha256": sha(Path(__file__)), "cache_root": str(args.cache_root)}
    code = 0
    try:
        (bootstrap if args.action == "bootstrap" else reset)(args, report)
        report["passed"] = True
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        report.update({"passed": False, "error": repr(error)})
        code = 1
    finally:
        report["end_utc"] = now()
        args.report.parent.mkdir(parents=True, exist_ok=True)
        with args.report.open("x", encoding="utf-8") as stream:
            json.dump(report, stream, indent=2)
            stream.write("\n")
    print(json.dumps({"passed": report["passed"], "error": report.get("error"),
        "report": str(args.report), "dependency_artifact_count": len(report.get("dependency_artifacts", [])),
        "project_artifact_count": len(report.get("project_artifacts", []))}, indent=2))
    raise SystemExit(code)


if __name__ == "__main__":
    main()
