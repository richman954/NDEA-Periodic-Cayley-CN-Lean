#!/usr/bin/env python3
"""Verified recovery snapshots; these archives are not proof-completion evidence."""
from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import signal
import stat
import tempfile
import threading
import time
import uuid
import zipfile

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent
PROJECT = WORKSPACE / "NDEA_Evolve_offruntime"
MANIFEST = "CHECKPOINT_MANIFEST.json"
METADATA_FILES = (
    "checkpoint.py", "README.md", "START_HERE.md", "RECOVERY_POLICY.md", "RECOVERY_REVIEW.md",
    "archive_releases.py", "verify_off_machine.py", "test_recovery.py", "RECOVERY_TEST_RESULT.json",
    "RUN_MANIFEST.json", "WATCHER_STATUS.json", "RELEASE_INVENTORY.json", "RELEASE_ARCHIVE_RECEIPT.json",
    "OFF_MACHINE_BACKUP_RECEIPT.json", "BACKUP_UPLOADS.json",
    "LOCAL_BACKUP_RECEIPT.json", "make_local_copy.py", "test_local_copy.py", "LOCAL_COPY_TEST_RESULT.json",
    "GITHUB_BACKUP_RECEIPT.json", "GITHUB_BACKUP_RUNBOOK.md",
)
GITHUB_EVIDENCE_SUFFIXES = {".json", ".log", ".md", ".py", ".txt", ".sha256"}
MAX_GITHUB_EVIDENCE_FILE_BYTES = 2 << 20
EXCLUDED_DIRS = {
    ".git", ".lake", "__pycache__", "build", "cache", "caches",
    "dependencies", "isolated_dependencies", "dependency_cache", "library_cache",
    "node_modules", ".venv", "venv",
}
EXCLUDED_SUFFIXES = {".pyc", ".pyo", ".olean", ".ilean", ".o", ".so"}
MAX_FILES = 100_000
MAX_BYTES = 1 << 30


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def atomic_bytes(path: Path, data: bytes) -> None:
    """Publish one complete file, then sync its directory entry."""
    descriptor, temporary = tempfile.mkstemp(prefix=".pending-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        fsync_directory(path.parent)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def safe_member(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if (not name or not path.parts or "\\" in name or "\x00" in name or ":" in name
            or path.is_absolute() or str(path) != name
            or any(part in {".", ".."} for part in path.parts)):
        raise ValueError(f"Unsafe archive path: {name!r}")
    return path


def verify_archive(archive: Path, expected_sha256: str) -> dict:
    """Verify every payload and reject unsafe, duplicate, or uncovered members."""
    digest = file_sha(archive)
    if digest != expected_sha256:
        raise ValueError("Archive SHA-256 mismatch")
    with zipfile.ZipFile(archive) as zipped:
        infos = zipped.infolist()
        if len(infos) > MAX_FILES or sum(i.file_size for i in infos) > MAX_BYTES:
            raise ValueError("Archive exceeds recovery size limits")
        names = set()
        for info in infos:
            safe_member(info.filename)
            mode = info.external_attr >> 16
            if (info.filename in names or info.is_dir() or not stat.S_ISREG(mode)
                    or info.flag_bits & 1):
                raise ValueError("Duplicate, nonregular, or encrypted archive member")
            names.add(info.filename)
        if MANIFEST not in names:
            raise ValueError("Missing checkpoint manifest")
        manifest = json.loads(zipped.read(MANIFEST))
        if (manifest.get("kind") != "recovery_checkpoint"
                or manifest.get("proof_completion_evidence") is not False):
            raise ValueError("Archive is not an explicitly qualified recovery checkpoint")
        payload = manifest["files"]
        if set(payload) != names - {MANIFEST}:
            raise ValueError("Manifest coverage mismatch")
        for name, record in payload.items():
            data = zipped.read(name)
            if len(data) != record["bytes"] or sha(data) != record["sha256"]:
                raise ValueError(f"Payload hash or length mismatch: {name}")
    return {"archive_sha256": digest, "payload_files_verified": len(payload),
            "payload_bytes": sum(v["bytes"] for v in payload.values()),
            "manifest": manifest}


def active_experiment(state: Path) -> Path:
    """The task manifest may select only a real expNNN child of this project."""
    if state.is_symlink():
        raise ValueError("Task state must not be a symlink")
    task = json.loads(state.read_text())
    selected = Path(task["active_experiment"])
    if not selected.is_absolute():
        selected = PROJECT / selected
    if (not re.fullmatch(r"exp[0-9]{3}", selected.name)
            or selected.parent != PROJECT or selected.is_symlink()
            or selected.resolve().parent != PROJECT.resolve()):
        raise ValueError("Active experiment must be a direct, nonsymlink project child named expNNN")
    if not selected.is_dir():
        raise FileNotFoundError(selected)
    return selected


def github_evidence_paths() -> list[Path]:
    """Include only explicitly staged small text evidence, never external clones."""
    root = HERE / "github_evidence"
    if root.is_symlink() or (root.exists() and not root.is_dir()):
        raise ValueError("GitHub evidence root must be a nonsymlink directory")
    paths = []
    for base, dirs, files in os.walk(root, followlinks=False):
        parent = Path(base)
        if any((parent / name).is_symlink() for name in dirs):
            raise ValueError("GitHub evidence directory symlink rejected")
        for name in files:
            path = parent / name
            if (path.is_symlink() or not path.is_file()
                    or path.suffix not in GITHUB_EVIDENCE_SUFFIXES
                    or path.stat().st_size > MAX_GITHUB_EVIDENCE_FILE_BYTES):
                raise ValueError(f"Invalid GitHub evidence file: {path}")
            paths.append(path)
    return sorted(paths)


def source_paths(state: Path, experiment: Path) -> tuple[list[Path], list[str]]:
    paths = []
    excluded = []
    for base, dirs, files in os.walk(experiment, followlinks=False):
        parent = Path(base)
        kept = []
        for name in sorted(dirs):
            path = parent / name
            if name in EXCLUDED_DIRS or path.is_symlink():
                excluded.append(str(path.relative_to(WORKSPACE)))
            else:
                kept.append(name)
        dirs[:] = kept
        for name in sorted(files):
            path = parent / name
            if path.is_symlink() or path.suffix in EXCLUDED_SUFFIXES:
                excluded.append(str(path.relative_to(WORKSPACE)))
            elif path.is_file():
                paths.append(path)
    required = {WORKSPACE / "AGENTS.md", PROJECT / "RESUME_STATUS.md", PROJECT / "WORKING_ROADMAP.md"}
    for path in [*required,
                 state, *(HERE / name for name in METADATA_FILES)]:
        if path.is_symlink():
            raise ValueError(f"Recovery metadata must not be a symlink: {path}")
        if path.is_file():
            paths.append(path)
        elif path in required:
            raise FileNotFoundError(path)
    paths.extend(github_evidence_paths())
    return sorted(set(paths)), excluded


def capture(path: Path) -> tuple[bytes, dict]:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, "rb") as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode):
            raise ValueError(f"Source is not a regular file: {path}")
        data = stream.read(MAX_BYTES + 1)
        after = os.fstat(stream.fileno())
    if len(data) > MAX_BYTES:
        raise ValueError(f"Source exceeds recovery size limit: {path}")
    if path.is_relative_to(HERE / "github_evidence"):
        if len(data) > MAX_GITHUB_EVIDENCE_FILE_BYTES:
            raise ValueError(f"GitHub evidence exceeds size limit: {path}")
        try:
            data.decode("utf-8")
        except UnicodeDecodeError as error:
            raise ValueError(f"GitHub evidence must be UTF-8 text: {path}") from error
    return data, {
        "sha256": sha(data), "bytes": len(data), "captured_utc": utc(),
        "source_mtime_ns_before": before.st_mtime_ns,
        "source_mtime_ns_after": after.st_mtime_ns,
        "source_size_before": before.st_size, "source_size_after": after.st_size,
        "changed_during_read": (before.st_mtime_ns, before.st_size)
        != (after.st_mtime_ns, after.st_size),
    }


def write_member(zipped: zipfile.ZipFile, name: str, data: bytes) -> None:
    safe_member(name)
    info = zipfile.ZipInfo(name, dt.datetime.now().timetuple()[:6])
    info.create_system = 3
    info.external_attr = (stat.S_IFREG | 0o644) << 16
    info.compress_type = zipfile.ZIP_DEFLATED
    zipped.writestr(info, data)


def snapshot_once(state: Path | None = None, reason: str = "manual",
                  expected_experiment: Path | None = None) -> dict:
    """Capture bytes once; per-file timestamps document the nontransactional scope."""
    state = HERE / "TASK_STATE.json" if state is None else state
    started = utc()
    experiment = active_experiment(state)
    if expected_experiment is not None and experiment != expected_experiment:
        raise ValueError("Active experiment changed; restart the watcher for the new task")
    final_receipt = experiment / "evidence/FINAL_PACKET_RECEIPT.json"
    paths, excluded = source_paths(state, experiment)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    stem = f"{experiment.name}_recovery_{stamp}_{uuid.uuid4().hex[:8]}"
    destination = HERE / "snapshots"
    destination.mkdir(exist_ok=True)
    fsync_directory(HERE)
    archive = destination / f"{stem}.zip"
    receipt_path = destination / f"{stem}.json"
    descriptor, temporary_name = tempfile.mkstemp(prefix=".pending-", dir=destination)
    temporary = Path(temporary_name)
    records = {}
    disappeared = []
    try:
        with os.fdopen(descriptor, "w+b") as stream:
            with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED) as zipped:
                total = 0
                for path in paths:
                    try:
                        data, record = capture(path)
                    except FileNotFoundError:
                        disappeared.append(str(path.relative_to(WORKSPACE)))
                        continue
                    total += len(data)
                    if len(records) >= MAX_FILES - 1 or total > MAX_BYTES:
                        raise ValueError("Snapshot exceeds recovery size limits")
                    name = str(path.relative_to(WORKSPACE))
                    records[name] = record
                    write_member(zipped, name, data)
                manifest = {
                    "schema_version": 1, "kind": "recovery_checkpoint",
                    "proof_completion_evidence": False,
                    "qualification": "Recovery copy only. Files are captured sequentially; mutable logs and state may represent different instants. Saved receipts are not a new proof verification.",
                    "started_utc": started, "capture_finished_utc": utc(),
                    "reason": reason, "workspace_root": str(WORKSPACE),
                    "active_experiment": experiment.name, "files": records,
                    "excluded_paths": excluded, "disappeared_before_read": disappeared,
                    "task_state_present": str(state.relative_to(WORKSPACE)) in records,
                    "final_packet_receipt_captured": str(final_receipt.relative_to(WORKSPACE)) in records,
                }
                write_member(zipped, MANIFEST, json_bytes(manifest))
            stream.flush()
            os.fsync(stream.fileno())
        digest = file_sha(temporary)
        verified = verify_archive(temporary, digest)
        os.replace(temporary, archive)
        fsync_directory(destination)
        # Read the published archive back before publishing its receipt and pointer.
        verify_archive(archive, digest)
        receipt = {
            "kind": "recovery_checkpoint_receipt", "proof_completion_evidence": False,
            "published_utc": utc(), "active_experiment": experiment.name,
            "archive": str(archive), "archive_sha256": digest,
            "archive_bytes": archive.stat().st_size,
            "payload_files_verified": verified["payload_files_verified"],
            "final_packet_receipt_captured": manifest["final_packet_receipt_captured"],
            "task_state_present": manifest["task_state_present"], "reason": reason,
        }
        receipt_bytes = json_bytes(receipt)
        atomic_bytes(receipt_path, receipt_bytes)
        if receipt_path.read_bytes() != receipt_bytes:
            raise ValueError("Published receipt readback mismatch")
        pointer = dict(receipt, receipt=str(receipt_path), receipt_sha256=sha(receipt_bytes))
        atomic_bytes(HERE / "LATEST_CHECKPOINT.json", json_bytes(pointer))
        return pointer
    finally:
        if temporary.exists():
            temporary.unlink()


def restore_archive(archive: Path, expected_sha256: str, target: Path) -> dict:
    """Restore only into a new directory, after complete integrity/path validation."""
    checked = verify_archive(archive, expected_sha256)
    # Refuse existing destinations and symlinked ancestors, including dangling links.
    for parent in [target, *target.parents]:
        if parent.is_symlink():
            raise ValueError(f"Symlink in restore destination: {parent}")
    target.mkdir(exist_ok=False)
    with zipfile.ZipFile(archive) as zipped:
        for info in zipped.infolist():
            relative = safe_member(info.filename)
            output = target.joinpath(*relative.parts)
            output.parent.mkdir(parents=True, exist_ok=True)
            with output.open("xb") as stream:
                stream.write(zipped.read(info))
                stream.flush()
                os.fsync(stream.fileno())
    for name, record in checked["manifest"]["files"].items():
        if file_sha(target / name) != record["sha256"]:
            raise ValueError(f"Restored file hash mismatch: {name}")
    fsync_directory(target)
    return {"restored_to": str(target), "files_verified": checked["payload_files_verified"],
            "archive_sha256": expected_sha256, "proof_completion_evidence": False}


def watch(state: Path, interval: float, hours: float) -> None:
    if interval < 60 or not 0 < hours <= 12:
        raise ValueError("Watch interval must be at least 60 seconds; duration must be in (0,12] hours")
    if not state.is_file():
        raise FileNotFoundError("Write TASK_STATE.json before starting the watcher")
    experiment = active_experiment(state)
    final_receipt = experiment / "evidence/FINAL_PACKET_RECEIPT.json"
    stop = threading.Event()
    for sig in [signal.SIGTERM, signal.SIGINT]:
        signal.signal(sig, lambda *_: stop.set())
    with (HERE / "WATCHER.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        deadline = time.monotonic() + hours * 3600
        status = {"pid": os.getpid(), "started_utc": utc(), "interval_seconds": interval,
                  "maximum_hours": hours, "task_state": str(state),
                  "active_experiment": experiment.name, "status": "running"}
        atomic_bytes(HERE / "WATCHER_STATUS.json", json_bytes(status))
        reason = "watch_start"
        try:
            while True:
                receipt = snapshot_once(state, reason, expected_experiment=experiment)
                print(json.dumps(receipt), flush=True)
                if receipt["final_packet_receipt_captured"]:
                    reason = "final_packet_receipt_captured"
                    break
                if stop.is_set() or time.monotonic() >= deadline:
                    reason = "signal_stop" if stop.is_set() else "maximum_duration_reached"
                    break
                # A final marker created during capture must be included in another snapshot.
                if final_receipt.is_file():
                    reason = "final_packet_receipt_detected"
                    continue
                stop.wait(min(interval, max(0, deadline - time.monotonic())))
                reason = "signal_final_snapshot" if stop.is_set() else "watch_interval"
            status.update(status="stopped", stopped_utc=utc(), stop_reason=reason,
                          latest_archive=receipt["archive"])
        except BaseException as error:
            status.update(status="failed", stopped_utc=utc(), error=repr(error))
            raise
        finally:
            atomic_bytes(HERE / "WATCHER_STATUS.json", json_bytes(status))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--once", action="store_true")
    mode.add_argument("--watch", action="store_true")
    mode.add_argument("--verify", type=Path, metavar="ARCHIVE")
    mode.add_argument("--restore", type=Path, metavar="ARCHIVE")
    parser.add_argument("--sha256", help="Required trusted archive hash for verify/restore")
    parser.add_argument("--restore-to", type=Path, help="New, nonexistent restoration directory")
    parser.add_argument("--state", type=Path, default=HERE / "TASK_STATE.json")
    parser.add_argument("--interval", type=float, default=60)
    parser.add_argument("--hours", type=float, default=12)
    args = parser.parse_args()
    if (args.verify or args.restore) and not args.sha256:
        parser.error("--verify/--restore requires --sha256 from a trusted saved receipt")
    if args.restore and not args.restore_to:
        parser.error("--restore requires --restore-to")
    if args.once:
        result = snapshot_once(args.state.resolve())
    elif args.watch:
        watch(args.state.resolve(), args.interval, args.hours)
        return
    elif args.verify:
        result = verify_archive(args.verify, args.sha256)
        result.pop("manifest")
    else:
        result = restore_archive(args.restore, args.sha256, args.restore_to.absolute())
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()
