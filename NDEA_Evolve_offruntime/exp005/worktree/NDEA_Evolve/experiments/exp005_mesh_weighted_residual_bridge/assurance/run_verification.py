#!/usr/bin/env python3
"""Bounded, serial Lean verification with immutable per-command evidence."""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from make_combined_verification import EXPERIMENT, external_imports, source_groups


DEFAULT_PACKAGES = Path("/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages")
DEFAULT_LEAN = Path("/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean")
PACKAGE_NAMES = ("mathlib", "batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient", "plausible")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Runner:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.repo = args.repo.resolve()
        self.exp = self.repo / EXPERIMENT
        self.cache = args.cache_root.resolve()
        self.lib = self.cache / "lib/lean"
        self.receipts = (args.evidence_root or self.exp / "evidence").resolve() / "receipts"
        self.logs = self.receipts.parent / "logs"
        self.receipts.mkdir(parents=True, exist_ok=True)
        self.logs.mkdir(parents=True, exist_ok=True)
        self.lib.mkdir(parents=True, exist_ok=True)
        self.predecessor, self.production = source_groups(self.repo)
        self.controls = self.exp / "controls/lean/NegativeControls.lean"
        self.lean = args.lean.resolve()
        self.env = dict(os.environ)
        self.env["LEAN_PATH"] = f"{self.lib}:{self.lean.parent.parent / 'lib/lean'}"
        self.env["LEAN_NUM_THREADS"] = "1"
        self.run_id = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ") + f"_{os.getpid()}"
        self.counter = 0

    def run(self, label: str, command: list[str], sources: list[Path], outputs: list[Path] | None = None) -> None:
        self.counter += 1
        stem = f"{self.run_id}_{self.counter:03d}_{label}"
        log = self.logs / f"{stem}.log"
        receipt = self.receipts / f"{stem}.json"
        before = {str(path): sha256(path) for path in sources}
        record = {
            "stage": self.args.stage,
            "label": label,
            "qualification": "development" if self.args.skip_existing or self.args.stage == "bootstrap" else "fresh",
            "command": command,
            "cwd": str(self.repo),
            "lean_path": self.env["LEAN_PATH"],
            "lean_binary": str(self.lean),
            "lean_binary_sha256": sha256(self.lean),
            "source_sha256_before": before,
            "start_utc": utc_now(),
            "timeout_seconds": self.args.timeout,
            "log": str(log),
        }
        # Create the receipt before launch so interrupted attempts remain attributable.
        receipt.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        print(f"START {label}: {receipt}", flush=True)
        begin = time.monotonic()
        code = 127
        timed_out = False
        interrupted = False
        try:
            with log.open("xb") as stream:
                process = subprocess.Popen(command, cwd=self.repo, env=self.env,
                                           stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                try:
                    code = process.wait(timeout=self.args.timeout)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    code = 124
                except KeyboardInterrupt:
                    interrupted = True
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    code = 130
        except OSError as error:
            record["launch_error"] = repr(error)
        finally:
            after = {str(path): sha256(path) if path.is_file() else None for path in sources}
            record.update({
                "end_utc": utc_now(),
                "elapsed_seconds": round(time.monotonic() - begin, 6),
                "exit_code": code,
                "timed_out": timed_out,
                "interrupted": interrupted,
                "source_sha256_after": after,
                "sources_unchanged": before == after,
                "log_sha256": sha256(log) if log.is_file() else None,
                "output_sha256": {str(path): sha256(path) for path in (outputs or []) if path.is_file()},
            })
            receipt.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        print(f"END {label}: exit={code} elapsed={record['elapsed_seconds']}s log={log}", flush=True)
        if code != 0:
            if log.is_file():
                print(log.read_text(encoding="utf-8", errors="replace")[-14000:], flush=True)
            raise SystemExit(code)
        if before != after:
            raise SystemExit("Source changed during verification; this attempt cannot qualify.")

    def prepare(self) -> None:
        helper = self.repo / "experiments/exp003_exact_order_defect_norm_bound/assurance/lean_import_closure.py"
        sources = self.predecessor + self.production + [self.controls]
        if self.args.path:
            sources.append(self.args.path.resolve())
        present_sources = [path for path in sources if path.is_file()]
        command = [sys.executable, str(helper)]
        roots = self.args.source_root or [self.args.packages / name for name in PACKAGE_NAMES]
        artifacts = self.args.artifact_root or [root / ".lake/build/lib/lean" for root in roots]
        for root in roots:
            command.extend(["--root", str(root.resolve())])
        for root in artifacts:
            command.extend(["--artifact-root", str(root.resolve())])
        command.extend(["--copy-artifacts-to", str(self.lib), "--report-artifact-bytes"])
        command.extend(external_imports(present_sources))
        command.extend(self.args.extra_import)
        self.run("prepare_import_closure", command, [helper, Path(__file__).resolve(),
                                                     Path(__file__).with_name("make_combined_verification.py").resolve(),
                                                     *present_sources])

    def cache_action(self, action: str) -> None:
        helper = Path(__file__).with_name("cache_tools.py").resolve()
        generator = Path(__file__).with_name("make_combined_verification.py").resolve()
        report = self.receipts / f"{self.run_id}_cache_{action}_manifest.json"
        command = [sys.executable, str(helper), action, "--repo", str(self.repo),
                   "--cache-root", str(self.cache), "--run-id", self.run_id,
                   "--report", str(report)]
        if action == "bootstrap":
            command.extend(["--source-cache", str(self.args.bootstrap_source_cache.resolve())])
        self.run(f"cache_{action}", command, [helper, generator, Path(__file__).resolve()], [report])

    def compile(self, source: Path, *, output: bool = True) -> None:
        source = source.resolve()
        shadow = self.repo / "experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources"
        root = shadow if source.is_relative_to(shadow) else self.repo
        target = self.lib / source.relative_to(root).with_suffix(".olean") if output else None
        if target and self.args.skip_existing and target.is_file():
            # Deliberately development-only: existence is insufficient for qualification.
            print(f"DEVELOPMENT SKIP {source}: existing {target}", flush=True)
            return
        command = [str(self.lean), "-j", "1", "-R", str(root)]
        if target:
            target.parent.mkdir(parents=True, exist_ok=True)
            command.extend(["-o", str(target)])
        command.append(str(source))
        self.run(source.stem, command, [source], [target] if target else [])

    def combined(self, controls: bool) -> None:
        generator = Path(__file__).with_name("make_combined_verification.py").resolve()
        target = self.exp / "evidence/generated" / f"CombinedExp005{'Controls' if controls else 'Production'}_{self.run_id}.lean"
        command = [sys.executable, str(generator), "--repo", str(self.repo), "--output", str(target)]
        inputs = [generator] + self.predecessor + self.production
        if controls:
            command.append("--controls")
            inputs.append(self.controls)
        self.run("generate_combined", command, inputs, [target])
        self.run("combined_controls" if controls else "combined_production",
                 [str(self.lean), "-j", "1", str(target)], [target, *inputs])

    def execute(self) -> None:
        stage = self.args.stage
        if stage == "bootstrap":
            self.cache_action("bootstrap")
            return
        if stage == "prepare":
            self.prepare()
            return
        if stage in ("combined", "combined-controls"):
            self.combined(stage == "combined-controls")
            return
        if stage in ("module", "probe"):
            if self.args.path is None:
                raise SystemExit(f"{stage} requires --path")
            self.compile(self.args.path, output=stage == "module")
            return
        if not self.args.skip_existing:
            self.cache_action("reset")
        for source in self.predecessor:
            self.compile(source)
        if stage == "predecessors":
            return
        for source in self.production:
            self.compile(source)
        if stage == "controls":
            self.compile(self.controls, output=False)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("bootstrap", "prepare", "predecessors", "module", "probe", "production", "controls", "combined", "combined-controls"))
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--cache-root", type=Path, default=Path("/tmp/exp005_build"))
    parser.add_argument("--bootstrap-source-cache", type=Path, default=Path("/tmp/exp004_build"))
    parser.add_argument("--evidence-root", type=Path)
    parser.add_argument("--packages", type=Path, default=DEFAULT_PACKAGES)
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--source-root", type=Path, action="append")
    parser.add_argument("--artifact-root", type=Path, action="append")
    parser.add_argument("--extra-import", action="append", default=[])
    parser.add_argument("--path", type=Path)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--skip-existing", action="store_true", help="Development only; cannot qualify a fresh build.")
    parser.add_argument("--lock-file", type=Path, default=Path("/tmp/exp003_lean_one_job.lock"))
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    if args.skip_existing and args.stage in ("combined", "combined-controls"):
        parser.error("--skip-existing does not apply to combined verification")
    args.lock_file.parent.mkdir(parents=True, exist_ok=True)
    with args.lock_file.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("Another verification runner holds the shared Lean job lock.")
        Runner(args).execute()


if __name__ == "__main__":
    main()
