#!/usr/bin/env python3
"""Audit explicitly selected final Step-5 evidence; never run Lean or overwrite audits."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import subprocess

from make_combined_verification import EXPERIMENT, filtered_source, source_groups


PREDECESSOR = "902a5d44c222254a443a01aebf563df72b8154d5"
PREDECESSOR_TAG = "exp003-step4-finite-n-telescoping-global-bound-verified-final-20260907"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b")
AXIOM_ROW = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.MULTILINE)
NO_AXIOM_ROW = re.compile(r"'([^']+)' does not depend on any axioms")
PRINT_AXIOMS = re.compile(r"^\s*#print\s+axioms\s+(\S+)", re.MULTILINE)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code_only(text: str) -> str:
    """Blank nested comments and strings, preserving offsets and line numbers."""
    output = list(text)
    index, depth = 0, 0
    in_string = False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair in ("/-", "-/"):
                output[index:index + 2] = "  "
                depth += 1 if pair == "/-" else -1
                index += 2
                continue
            if text[index] != "\n":
                output[index] = " "
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                output[index] = " "
                if text[index + 1] != "\n":
                    output[index + 1] = " "
                index += 2
                continue
            if text[index] == '"':
                in_string = False
            if text[index] != "\n":
                output[index] = " "
        elif pair == "/-":
            depth = 1
            output[index:index + 2] = "  "
            index += 2
            continue
        elif pair == "--":
            end = text.find("\n", index)
            if end == -1:
                end = len(text)
            output[index:end] = " " * (end - index)
            index = end
            continue
        elif text[index] == '"':
            in_string = True
            output[index] = " "
        index += 1
    return "".join(output)


class Audit:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.repo = args.repo.resolve()
        self.exp = self.repo / EXPERIMENT
        self.errors: list[str] = []
        self.report: dict = {
            "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "repo": str(self.repo), "predecessor_commit": PREDECESSOR,
            "predecessor_tag": PREDECESSOR_TAG, "git_commands": [],
        }
        self.selected: set[Path] = set()

    def check(self, condition: bool, message: str) -> None:
        if not condition:
            self.errors.append(message)

    def git(self, *arguments: str) -> subprocess.CompletedProcess:
        return self.git_at(self.repo, *arguments)

    def git_at(self, repo: Path, *arguments: str) -> subprocess.CompletedProcess:
        command = ["git", "-C", str(repo), *arguments]
        result = subprocess.run(command, capture_output=True, text=True, timeout=60)
        self.report["git_commands"].append({"command": command, "exit_code": result.returncode,
                                             "stdout": result.stdout, "stderr": result.stderr})
        return result

    def predecessor(self) -> None:
        tag = self.git("rev-parse", f"{PREDECESSOR_TAG}^{{commit}}")
        self.check(tag.returncode == 0 and tag.stdout.strip() == PREDECESSOR,
                   "Predecessor tag does not resolve to the expected release commit.")
        ancestor = self.git("merge-base", "--is-ancestor", PREDECESSOR, "HEAD")
        self.check(ancestor.returncode == 0, "Predecessor is not an ancestor of HEAD.")
        tracked = self.git("ls-tree", "-r", "--name-only", "-z", PREDECESSOR)
        self.check(tracked.returncode == 0, "Could not enumerate predecessor tracked files.")
        protected = set(filter(None, tracked.stdout.split("\0")))
        changed = self.git("diff", "--no-renames", "--name-only", "-z", PREDECESSOR, "--")
        self.check(changed.returncode == 0, "Could not compare current files to predecessor.")
        changed_protected = sorted(protected.intersection(changed.stdout.split("\0")))
        self.report["protected_file_count"] = len(protected)
        self.report["changed_protected_files"] = changed_protected
        self.check(not changed_protected, "Protected predecessor files changed.")
        whitespace = self.git("diff", "--check", PREDECESSOR)
        self.check(whitespace.returncode == 0, "Git whitespace audit failed.")
        predecessors, _ = source_groups(self.repo)
        pairs = [
            (self.repo / "NDEAEvolve/Experiments/Exp002/OperatorCayley.lean", predecessors[0]),
            (self.repo / "NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean", predecessors[1]),
        ]
        self.report["shadow_import_only_checks"] = []
        for original, shadow in pairs:
            equal = filtered_source(original, False) == filtered_source(shadow, False)
            self.report["shadow_import_only_checks"].append({"original": str(original),
                "shadow": str(shadow), "non_import_source_equal": equal})
            self.check(equal, f"Predecessor shadow changes more than imports: {shadow}")
        baseline_path = Path(__file__).with_name("PREDECESSOR_BASELINE_20260907T222448Z.json").resolve()
        self.selected.add(baseline_path)
        baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
        predecessor_worktree = Path(baseline["worktree"])
        head = self.git_at(predecessor_worktree, "rev-parse", "HEAD")
        tag = self.git_at(predecessor_worktree, "rev-parse", f"{PREDECESSOR_TAG}^{{commit}}")
        status = self.git_at(predecessor_worktree, "status", "--porcelain=v1")
        self.check(head.returncode == 0 and head.stdout.strip() == PREDECESSOR,
                   "Original Step-4 worktree HEAD changed.")
        self.check(tag.returncode == 0 and tag.stdout.strip() == PREDECESSOR,
                   "Original Step-4 tag changed.")
        self.check(status.returncode == 0 and status.stdout == baseline["status_porcelain_v1"] == "",
                   "Original Step-4 worktree is no longer clean.")
        release_hashes = {path: sha256(Path(path)) for path in baseline["release_sha256"]}
        self.report["original_predecessor_and_release_check"] = {
            "baseline": str(baseline_path), "baseline_sha256": sha256(baseline_path),
            "baseline_captured_utc": baseline["captured_during_step5_utc"],
            "current_head": head.stdout.strip(), "current_tag_peeled": tag.stdout.strip(),
            "current_status_porcelain_v1": status.stdout,
            "baseline_release_sha256": baseline["release_sha256"],
            "current_release_sha256": release_hashes,
        }
        self.check(release_hashes == baseline["release_sha256"], "Original Step-4 release archives changed.")

    def policy(self, sources: list[Path]) -> list[str]:
        findings = []
        expected_axioms: list[str] = []
        for path in sources:
            self.selected.add(path)
            code = lean_code_only(path.read_text(encoding="utf-8"))
            for match in FORBIDDEN.finditer(code):
                findings.append({"source": str(path), "token": match.group(),
                                 "line": code.count("\n", 0, match.start()) + 1})
            expected_axioms.extend(PRINT_AXIOMS.findall(code))
        self.report["proof_policy_scan"] = {"files": [str(path) for path in sources],
                                              "findings": findings}
        self.check(not findings, "Prohibited proof-policy tokens were found in new Lean code.")
        self.check(bool(expected_axioms), "No principal declaration axiom audits were requested.")
        return expected_axioms

    def receipt(self, path: Path, required_sources: list[Path]) -> tuple[dict, str]:
        path = path.resolve()
        self.selected.add(path)
        record = json.loads(path.read_text(encoding="utf-8"))
        self.check(record.get("exit_code") == 0, f"Receipt is incomplete or failed: {path}")
        self.check(record.get("qualification") == "fresh", f"Receipt is development-only: {path}")
        self.check(record.get("sources_unchanged") is True, f"Receipt has changed input sources: {path}")
        self.check(not record.get("timed_out", True), f"Receipt timed out or lacks completion: {path}")
        self.check(bool(record.get("end_utc")), f"Receipt lacks end timestamp: {path}")
        command = record.get("command", [])
        worker_index = command.index("-j") if "-j" in command else -1
        self.check(0 <= worker_index < len(command) - 1 and command[worker_index + 1] == "1",
                   f"Receipt does not run Lean with one worker: {path}")
        before = record.get("source_sha256_before", {})
        after = record.get("source_sha256_after", {})
        for source in required_sources:
            current = sha256(source)
            self.check(before.get(str(source)) == current and after.get(str(source)) == current,
                       f"Receipt is not for current source {source}: {path}")
        for recorded_path, digest in before.items():
            recorded_source = Path(recorded_path)
            self.check(recorded_source.is_file() and sha256(recorded_source) == digest
                       and after.get(recorded_path) == digest,
                       f"Recorded input changed or is missing: {recorded_source}")
            if recorded_source.is_relative_to(self.repo):
                self.selected.add(recorded_source)
        log = Path(record["log"])
        self.selected.add(log)
        self.check(log.is_file() and record.get("log_sha256") == sha256(log),
                   f"Log hash mismatch: {path}")
        content = log.read_text(encoding="utf-8", errors="replace")
        self.check(re.search(r"\berror:|\bsorryAx\b|declaration uses .sorry.", content) is None,
                   f"Passing log contains a Lean error or sorry dependency: {log}")
        self.report.setdefault("selected_receipts", []).append({"path": str(path),
            "sha256": sha256(path), "label": record.get("label"),
            "source_sha256": before, "log_sha256": record.get("log_sha256")})
        return record, content

    def verify(self) -> None:
        predecessors, production = source_groups(self.repo)
        controls = self.exp / "controls/lean/NegativeControls.lean"
        expected_axioms = self.policy(production + [controls])
        self.predecessor()
        receipts = self.exp / "evidence/receipts"
        selected_modular = sorted(receipts.glob(f"{self.args.modular_run_prefix}_*.json"))
        labels: list[str] = []
        for path in selected_modular:
            preliminary = json.loads(path.read_text(encoding="utf-8"))
            matching = [source for source in predecessors + production + [controls]
                        if source.stem == preliminary.get("label")]
            if not matching:
                continue
            record, _ = self.receipt(path, matching)
            self.check(record.get("stage") == "controls", f"Expected full fresh controls run: {path}")
            labels.append(record["label"])
        expected_labels = [source.stem for source in predecessors + production + [controls]]
        self.report["modular_dependency_order"] = labels
        self.check(labels == expected_labels, "Selected modular run is incomplete or out of dependency order.")
        combined, content = self.receipt(self.args.combined_receipt,
                                          predecessors + production + [controls])
        self.check(combined.get("label") == "combined_controls",
                   "Selected combined receipt does not verify controls.")
        axioms = {name: sorted(filter(None, (item.strip() for item in dependencies.split(","))))
                  for name, dependencies in AXIOM_ROW.findall(content)}
        axioms.update({name: [] for name in NO_AXIOM_ROW.findall(content)})
        for name in expected_axioms:
            self.check(name in axioms, f"Missing compiled axiom audit: {name}")
        for name, dependencies in axioms.items():
            self.check(set(dependencies) <= ALLOWED_AXIOMS,
                       f"Unapproved axiom dependency for {name}: {dependencies}")
        self.report["principal_axiom_audit"] = {"expected_declarations": expected_axioms,
            "compiled_axiom_rows": axioms, "allowed_axioms": sorted(ALLOWED_AXIOMS)}
        self.selected.update(predecessors)
        self.selected.add(self.exp / "PLAN.md")
        self.selected.update(path for path in (self.exp / "assurance").iterdir()
                             if path.is_file() and path.suffix in (".py", ".sh", ".md"))
        self.report["selected_source_and_evidence_sha256"] = {
            str(path.relative_to(self.repo)): sha256(path) for path in sorted(self.selected)}

    def write(self) -> int:
        try:
            self.verify()
        except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
            self.errors.append(f"Audit could not finish: {error!r}")
        self.report["errors"] = self.errors
        self.report["passed"] = not self.errors
        self.args.output.parent.mkdir(parents=True, exist_ok=True)
        with self.args.output.open("x", encoding="utf-8") as stream:
            json.dump(self.report, stream, indent=2)
            stream.write("\n")
        if not self.errors and self.args.manifest:
            self.args.manifest.parent.mkdir(parents=True, exist_ok=True)
            with self.args.manifest.open("x", encoding="utf-8") as stream:
                for path, digest in self.report["selected_source_and_evidence_sha256"].items():
                    stream.write(f"{digest}  {path}\n")
        print(json.dumps({"passed": not self.errors, "errors": self.errors,
                          "output": str(self.args.output)}, indent=2))
        return 1 if self.errors else 0


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--modular-run-prefix", required=True,
                        help="Run ID before the command counter in a successful full controls run.")
    parser.add_argument("--combined-receipt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path)
    raise SystemExit(Audit(parser.parse_args()).write())


if __name__ == "__main__":
    main()
