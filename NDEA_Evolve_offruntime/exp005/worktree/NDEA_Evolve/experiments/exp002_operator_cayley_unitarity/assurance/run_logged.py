#!/usr/bin/env python3
"""Run one command, tee its complete combined output, and record exact timing/exit."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True)
    parser.add_argument("--timing", required=True)
    parser.add_argument("--cwd", default=os.getcwd())
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    argv = args.command
    if argv and argv[0] == "--":
        argv = argv[1:]
    if not argv:
        raise SystemExit("a command is required after --")

    log = Path(args.log).resolve()
    timing = Path(args.timing).resolve()
    cwd = Path(args.cwd).resolve()
    if log.exists() or timing.exists():
        raise SystemExit("refusing to overwrite an existing log or timing record")
    log.parent.mkdir(parents=True, exist_ok=True)
    timing.parent.mkdir(parents=True, exist_ok=True)

    started_utc = datetime.now(timezone.utc)
    started_monotonic = time.monotonic()
    with log.open("xb") as stream:
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL,
            env=os.environ.copy(),
        )
        assert process.stdout is not None
        while True:
            chunk = process.stdout.read(64 * 1024)
            if not chunk:
                break
            stream.write(chunk)
            stream.flush()
            sys.stdout.buffer.write(chunk)
            sys.stdout.buffer.flush()
        exit_code = process.wait()
    finished_utc = datetime.now(timezone.utc)
    elapsed = time.monotonic() - started_monotonic
    record = {
        "schema": "ndea.exp002.logged_command.v1",
        "argv": argv,
        "cwd": str(cwd),
        "started_utc": started_utc.isoformat(),
        "finished_utc": finished_utc.isoformat(),
        "elapsed_seconds": elapsed,
        "exit_code": exit_code,
        "log": str(log),
        "log_size_bytes": log.stat().st_size,
        "log_sha256": sha256(log),
    }
    timing.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nLOGGED_COMMAND_EXIT_CODE={exit_code}")
    print(f"LOGGED_COMMAND_LOG_SHA256={record['log_sha256']}")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
