#!/usr/bin/env python3
"""Fail-closed manifest and final-delivery packager for Experiment 002.

This helper has two deliberately separated phases:

* ``manifest-write`` / ``manifest-check`` cover every regular file below the
  final-delivery verifier's selected Git paths, except ``FINAL_SHA256SUMS``
  itself.  A differing manifest is never overwritten.
* ``package`` runs only after the manifest, clean final commit, annotated final
  tag, branch, and immutable Experiment 001 tag exist.  It creates a new output
  directory, a commit-bound Git archive, a Git bundle, an adjacent PASS receipt,
  and a verifier specification derived from an explicitly supplied template.

The package command does not commit, tag, build, run Lean/Julia, invoke the final
delivery verifier, or modify the repository.  Run the existing
``verify_exp002_final_delivery.py`` independently against the emitted spec.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from types import ModuleType
from typing import Any, BinaryIO, Iterable


HERE = Path(__file__).resolve().parent
VERIFIER_PATH = HERE / "verify_exp002_final_delivery.py"
EXP_ROOT = "experiments/exp002_operator_cayley_unitarity"
FINAL_MANIFEST = f"{EXP_ROOT}/FINAL_SHA256SUMS"
ARCHIVE_ROOT = "NDEA_Evolve"
DELIVERY_MANIFEST = "DELIVERY_SHA256SUMS"
PACKAGER_SCHEMA = "ndea.exp002.final_packager.v1"
REMOTE_RECEIPT_SCHEMA = "ndea.exp002.final_delivery.v1"
FAILURE_SCHEMA = "ndea.exp002.final_packager_failure.v1"
FAILURE_MARKER = "PACKAGING_FAILED.json"

# This is intentionally duplicated as a drift sentinel, not as an independent
# source of truth.  load_verifier() requires exact equality with the verifier.
KNOWN_SELECTED_PATHS = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "NDEAEvolve.lean",
    "NDEAEvolve/Basic.lean",
    "NDEAEvolve/Experiments/Exp002",
    EXP_ROOT,
)

HEX64 = re.compile(r"[0-9a-f]{64}\Z")
SAFE_FILENAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._+-]*\Z")


class PackagingError(RuntimeError):
    """A condition that prevents trustworthy packaging."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_verifier(path: Path = VERIFIER_PATH) -> ModuleType:
    spec = importlib.util.spec_from_file_location("ndea_exp002_final_verifier", path)
    if spec is None or spec.loader is None:
        raise PackagingError(f"cannot load final verifier: {path}")
    module = importlib.util.module_from_spec(spec)
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    selected = tuple(getattr(module, "ARCHIVE_SELECTED_PATHS", ()))
    if selected != KNOWN_SELECTED_PATHS:
        raise PackagingError(
            "final-verifier selected-path drift; review both programs before packaging: "
            f"observed={selected!r} expected={KNOWN_SELECTED_PATHS!r}"
        )
    return module


def require_canonical_directory(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise PackagingError(f"{label} must be absolute: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        metadata = os.lstat(path)
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise PackagingError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical or not stat.S_ISDIR(metadata.st_mode):
        raise PackagingError(f"{label} must be a canonical non-link directory: {path}")
    return resolved


def require_regular(path: Path, label: str) -> Path:
    if not path.is_absolute():
        raise PackagingError(f"{label} must be absolute: {path}")
    lexical = Path(os.path.abspath(path))
    try:
        metadata = os.lstat(path)
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise PackagingError(f"{label} is unavailable: {path}: {error}") from error
    if resolved != lexical or not stat.S_ISREG(metadata.st_mode):
        raise PackagingError(f"{label} must be a canonical regular non-link file: {path}")
    return resolved


def require_new_absolute_directory(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise PackagingError(f"{label} must be an absolute path that does not exist: {path}")
    require_canonical_directory(path.parent, f"{label} parent")
    return Path(os.path.abspath(path))


def require_distinct_directories(first: Path, second: Path) -> None:
    if first == second:
        raise PackagingError(
            "package output directory and fresh-verification output directory must differ"
        )


def require_safe_filename(value: str, label: str) -> str:
    if SAFE_FILENAME.fullmatch(value) is None or value in {".", ".."}:
        raise PackagingError(f"{label} must be one safe basename: {value!r}")
    return value


def hash_regular(path: Path) -> str:
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise PackagingError(f"cannot open regular non-link file {path}: {error}") from error
    digest = hashlib.sha256()
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise PackagingError(f"not a regular file: {path}")
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            digest.update(block)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    try:
        current = os.lstat(path)
    except OSError as error:
        raise PackagingError(f"file disappeared while hashing: {path}: {error}") from error
    identity_before = (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if identity_before != identity_after or (current.st_dev, current.st_ino) != (
        before.st_dev,
        before.st_ino,
    ):
        raise PackagingError(f"file changed while hashing: {path}")
    return digest.hexdigest()


def write_exclusive(path: Path, payload: bytes, mode: int = 0o600) -> None:
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    except OSError as error:
        raise PackagingError(f"refusing non-exclusive write to {path}: {error}") from error
    try:
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise PackagingError(f"short write while creating {path}")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def relative_posix(repo: Path, path: Path) -> str:
    try:
        return path.relative_to(repo).as_posix()
    except ValueError as error:
        raise PackagingError(f"path escapes repository: {path}") from error


def walk_directory(repo: Path, directory: Path) -> Iterable[tuple[str, Path]]:
    try:
        entries = sorted(os.scandir(directory), key=lambda entry: entry.name)
    except OSError as error:
        raise PackagingError(f"cannot scan selected directory {directory}: {error}") from error
    for entry in entries:
        path = Path(entry.path)
        try:
            metadata = entry.stat(follow_symlinks=False)
        except OSError as error:
            raise PackagingError(f"cannot stat selected path {path}: {error}") from error
        if stat.S_ISLNK(metadata.st_mode):
            raise PackagingError(f"symbolic links are forbidden below selected paths: {path}")
        if stat.S_ISDIR(metadata.st_mode):
            yield from walk_directory(repo, path)
        elif stat.S_ISREG(metadata.st_mode):
            yield relative_posix(repo, path), path
        else:
            raise PackagingError(f"special files are forbidden below selected paths: {path}")


def selected_regular_files(
    repo: Path,
    verifier: ModuleType,
    *,
    exclude_manifest: bool,
) -> dict[str, Path]:
    result: dict[str, Path] = {}
    folded: set[str] = set()
    for selected in verifier.ARCHIVE_SELECTED_PATHS:
        verifier.canonical_relative(selected, "selected path", 4096)
        target = repo.joinpath(*PurePosixPath(selected).parts)
        try:
            metadata = os.lstat(target)
        except OSError as error:
            raise PackagingError(f"required selected path is unavailable: {selected!r}: {error}") from error
        if stat.S_ISLNK(metadata.st_mode):
            raise PackagingError(f"selected path is a symbolic link: {selected!r}")
        if stat.S_ISREG(metadata.st_mode):
            rows = [(selected, target)]
        elif stat.S_ISDIR(metadata.st_mode):
            rows = list(walk_directory(repo, target))
            if not rows:
                raise PackagingError(f"selected directory contains no regular files: {selected!r}")
        else:
            raise PackagingError(f"selected path is neither a regular file nor directory: {selected!r}")
        for relative, path in rows:
            verifier.canonical_relative(relative, "selected regular file", 4096)
            if exclude_manifest and relative == FINAL_MANIFEST:
                continue
            if relative in result or relative.casefold() in folded:
                raise PackagingError(f"duplicate or case-fold-colliding selected file: {relative!r}")
            result[relative] = path
            folded.add(relative.casefold())
    return dict(sorted(result.items()))


def reject_ignored_selected_files(
    repo: Path,
    files: dict[str, Path],
    verifier: ModuleType,
) -> None:
    if not files:
        return
    payload = b"\0".join(relative.encode("utf-8", errors="strict") for relative in files) + b"\0"
    try:
        completed = subprocess.run(
            ["git", "check-ignore", "--no-index", "-z", "--stdin"],
            cwd=repo,
            env=clean_git_environment(verifier),
            input=payload,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise PackagingError(f"cannot check selected paths against Git ignore rules: {error}") from error
    if completed.returncode not in {0, 1}:
        raise PackagingError(
            "git check-ignore failed while auditing selected files: "
            f"exit={completed.returncode} stderr={completed.stderr.decode('utf-8', 'replace')}"
        )
    ignored: list[str] = []
    for raw in completed.stdout.split(b"\0"):
        if not raw:
            continue
        try:
            relative = raw.decode("utf-8", errors="strict")
        except UnicodeError as error:
            raise PackagingError(f"git check-ignore returned a non-UTF-8 path: {raw!r}") from error
        verifier.canonical_relative(relative, "ignored selected file", 4096)
        if relative not in files:
            raise PackagingError(f"git check-ignore returned an unexpected path: {relative!r}")
        ignored.append(relative)
    if completed.returncode == 0 and not ignored:
        raise PackagingError("git check-ignore reported ignored input without naming it")
    if completed.returncode == 1 and ignored:
        raise PackagingError("git check-ignore returned ignored paths with a no-match exit status")
    if ignored:
        raise PackagingError(
            "ignored regular files are forbidden below selected paths: "
            f"{sorted(ignored)!r}"
        )


def render_manifest(files: dict[str, Path]) -> bytes:
    rows = [f"{hash_regular(path)}  {relative}" for relative, path in files.items()]
    return ("\n".join(rows) + "\n").encode("utf-8")


def validate_manifest(repo: Path, verifier: ModuleType) -> dict[str, Any]:
    all_files = selected_regular_files(repo, verifier, exclude_manifest=False)
    reject_ignored_selected_files(repo, all_files, verifier)
    files = {relative: path for relative, path in all_files.items() if relative != FINAL_MANIFEST}
    manifest = repo.joinpath(*PurePosixPath(FINAL_MANIFEST).parts)
    require_regular(manifest, "FINAL_SHA256SUMS")
    expected = render_manifest(files)
    try:
        observed = manifest.read_bytes()
    except OSError as error:
        raise PackagingError(f"cannot read FINAL_SHA256SUMS: {error}") from error
    if observed != expected:
        raise PackagingError(
            "FINAL_SHA256SUMS is not the exact sorted digest listing for the selected regular files"
        )
    # Re-read the selected tree once so a mutation after an early digest is not
    # silently accepted as a coherent snapshot.
    if render_manifest(selected_regular_files(repo, verifier, exclude_manifest=True)) != observed:
        raise PackagingError("selected files changed during manifest validation")
    return {
        "path": FINAL_MANIFEST,
        "sha256": hash_regular(manifest),
        "entries": len(files),
        "selected_paths": list(verifier.ARCHIVE_SELECTED_PATHS),
    }


def write_manifest(repo: Path, verifier: ModuleType) -> dict[str, Any]:
    files = selected_regular_files(repo, verifier, exclude_manifest=True)
    reject_ignored_selected_files(repo, files, verifier)
    payload = render_manifest(files)
    manifest = repo.joinpath(*PurePosixPath(FINAL_MANIFEST).parts)
    if manifest.exists() or manifest.is_symlink():
        require_regular(manifest, "existing FINAL_SHA256SUMS")
        if manifest.read_bytes() != payload:
            raise PackagingError("refusing to overwrite a differing FINAL_SHA256SUMS")
        disposition = "ALREADY_IDENTICAL"
    else:
        require_canonical_directory(manifest.parent, "FINAL_SHA256SUMS parent")
        write_exclusive(manifest, payload)
        disposition = "CREATED_EXCLUSIVELY"
    result = validate_manifest(repo, verifier)
    result.update({"status": "PASS", "disposition": disposition})
    return result


def clean_git_environment(verifier: ModuleType) -> dict[str, str]:
    environment = verifier.clean_git_environment().copy()
    for key in (
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "GIT_SHALLOW_FILE",
        "GIT_TEMPLATE_DIR",
    ):
        environment.pop(key, None)
    environment.update(
        {
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_OPTIONAL_LOCKS": "0",
        }
    )
    return environment


class CommandRunner:
    def __init__(self, repo: Path, verifier: ModuleType, timeout: int):
        self.repo = repo
        self.verifier = verifier
        self.timeout = timeout
        self.records: list[dict[str, Any]] = []

    def run(
        self,
        argv: list[str],
        *,
        binary: bool = False,
        stdout_file: BinaryIO | None = None,
        cwd: Path | None = None,
    ) -> bytes | str:
        started = utc_now()
        before = time.monotonic()
        command_cwd = cwd if cwd is not None else self.repo
        try:
            completed = subprocess.run(
                argv,
                cwd=command_cwd,
                env=clean_git_environment(self.verifier),
                stdout=stdout_file if stdout_file is not None else subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=self.timeout,
                check=False,
            )
            timed_out = False
        except subprocess.TimeoutExpired as error:
            completed = subprocess.CompletedProcess(argv, 124, error.stdout or b"", error.stderr or b"")
            timed_out = True
        elapsed = time.monotonic() - before
        stdout = b"" if stdout_file is not None else bytes(completed.stdout or b"")
        stderr = bytes(completed.stderr or b"")
        record = {
            "argv": argv,
            "cwd": str(command_cwd),
            "started_utc": started,
            "elapsed_seconds": elapsed,
            "exit_code": completed.returncode,
            "timed_out": timed_out,
            "stdout_bytes": len(stdout),
            "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
            "stderr": stderr.decode("utf-8", "replace"),
            "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
            "stdout_redirected": str(getattr(stdout_file, "name", "")) if stdout_file else None,
        }
        self.records.append(record)
        if completed.returncode != 0 or timed_out:
            raise PackagingError(
                f"command failed with exit {completed.returncode}: {argv!r}: "
                f"{stderr.decode('utf-8', 'replace')}"
            )
        if stdout_file is not None:
            return b"" if binary else ""
        return stdout if binary else stdout.decode("utf-8", "strict")

    def git(
        self,
        *args: str,
        binary: bool = False,
        cwd: Path | None = None,
    ) -> bytes | str:
        return self.run(["git", *args], binary=binary, cwd=cwd)


def validate_ref(value: str, label: str, verifier: ModuleType) -> str:
    if (
        verifier.SAFE_REF.fullmatch(value) is None
        or value.startswith("-")
        or ".." in value
        or "//" in value
    ):
        raise PackagingError(f"unsafe {label}: {value!r}")
    return value


def git_text(runner: CommandRunner, *args: str) -> str:
    value = runner.git(*args)
    assert isinstance(value, str)
    return value.strip()


def require_plain_complete_git_repository(runner: CommandRunner) -> None:
    shallow = git_text(runner, "rev-parse", "--is-shallow-repository")
    if shallow != "false":
        raise PackagingError(
            f"repository must be complete and non-shallow; observed --is-shallow-repository={shallow!r}"
        )
    replacements = runner.git("for-each-ref", "--format=%(refname)", "refs/replace/")
    assert isinstance(replacements, str)
    replacement_refs = sorted(line for line in replacements.splitlines() if line)
    if replacement_refs:
        raise PackagingError(f"Git replacement refs are forbidden: {replacement_refs!r}")
    raw_grafts = git_text(runner, "rev-parse", "--git-path", "info/grafts")
    grafts = Path(raw_grafts)
    if not grafts.is_absolute():
        grafts = runner.repo / grafts
    try:
        os.lstat(grafts)
    except FileNotFoundError:
        pass
    except OSError as error:
        raise PackagingError(f"cannot inspect deprecated Git grafts path {grafts}: {error}") from error
    else:
        raise PackagingError(f"deprecated Git grafts file is forbidden, even if empty: {grafts}")


def require_clean_final_state(
    runner: CommandRunner,
    verifier: ModuleType,
    *,
    commit: str,
    branch: str,
    final_tag: str,
    exp001_tag: str,
    exp001_tag_object: str,
    exp001_commit: str,
) -> dict[str, str]:
    if verifier.GIT_OBJECT.fullmatch(commit) is None:
        raise PackagingError("--commit must be one exact lowercase Git object ID")
    validate_ref(branch, "branch", verifier)
    validate_ref(final_tag, "final tag", verifier)
    validate_ref(exp001_tag, "Experiment 001 tag", verifier)
    status = runner.git("status", "--porcelain=v1", "-z", "--untracked-files=all")
    if status != "":
        raise PackagingError("repository is not clean; packaging is forbidden")
    head = git_text(runner, "rev-parse", "--verify", "HEAD^{commit}")
    branch_commit = git_text(runner, "rev-parse", "--verify", f"refs/heads/{branch}^{{commit}}")
    final_object = git_text(runner, "rev-parse", "--verify", f"refs/tags/{final_tag}")
    final_type = git_text(runner, "cat-file", "-t", f"refs/tags/{final_tag}")
    final_commit = git_text(runner, "rev-parse", "--verify", f"refs/tags/{final_tag}^{{commit}}")
    old_object = git_text(runner, "rev-parse", "--verify", f"refs/tags/{exp001_tag}")
    old_type = git_text(runner, "cat-file", "-t", f"refs/tags/{exp001_tag}")
    old_commit = git_text(runner, "rev-parse", "--verify", f"refs/tags/{exp001_tag}^{{commit}}")
    expected = {
        "head": commit,
        "branch_commit": commit,
        "final_commit": commit,
        "final_type": "tag",
        "exp001_tag_object": exp001_tag_object,
        "exp001_type": "tag",
        "exp001_commit": exp001_commit,
    }
    observed = {
        "head": head,
        "branch_commit": branch_commit,
        "final_commit": final_commit,
        "final_type": final_type,
        "exp001_tag_object": old_object,
        "exp001_type": old_type,
        "exp001_commit": old_commit,
    }
    if observed != expected:
        raise PackagingError(f"Git identity mismatch: observed={observed!r} expected={expected!r}")
    return {
        "commit": commit,
        "branch": branch,
        "tag": final_tag,
        "tag_object": final_object,
        "exp001_tag": exp001_tag,
        "exp001_tag_object": old_object,
        "exp001_commit": old_commit,
    }


def verify_selected_git_tree(
    runner: CommandRunner,
    verifier: ModuleType,
    repo: Path,
    commit: str,
) -> dict[str, dict[str, str]]:
    payload = runner.git(
        "ls-tree",
        "-rz",
        "-r",
        "--full-tree",
        commit,
        "--",
        *verifier.ARCHIVE_SELECTED_PATHS,
        binary=True,
    )
    assert isinstance(payload, bytes)
    tree = verifier.parse_ls_tree(payload, 4096)
    worktree = selected_regular_files(repo, verifier, exclude_manifest=False)
    if set(tree) != set(worktree):
        raise PackagingError(
            "clean worktree file set differs from selected commit tree: "
            f"tree_only={sorted(set(tree) - set(worktree))!r} "
            f"worktree_only={sorted(set(worktree) - set(tree))!r}"
        )
    if FINAL_MANIFEST not in tree:
        raise PackagingError("the final commit does not contain FINAL_SHA256SUMS")
    for selected in verifier.ARCHIVE_SELECTED_PATHS:
        if not any(path == selected or path.startswith(selected + "/") for path in tree):
            raise PackagingError(f"final commit has no file under selected path {selected!r}")
    return tree


def parse_bundle_heads(text: str, verifier: ModuleType, label: str) -> dict[str, str]:
    heads: dict[str, str] = {}
    for line in text.splitlines():
        try:
            object_id, ref = line.split(" ", 1)
        except ValueError as error:
            raise PackagingError(f"cannot parse {label} head: {line!r}") from error
        if verifier.GIT_OBJECT.fullmatch(object_id) is None:
            raise PackagingError(f"invalid object ID in {label} head: {line!r}")
        if not ref.startswith("refs/") or verifier.SAFE_REF.fullmatch(ref) is None:
            raise PackagingError(f"invalid ref in {label} head: {line!r}")
        if ref in heads:
            raise PackagingError(f"duplicate {label} ref: {ref!r}")
        heads[ref] = object_id
    return heads


def verify_bundle_in_fresh_repository(
    runner: CommandRunner,
    verifier: ModuleType,
    bundle: Path,
    expected_heads: dict[str, str],
    expected_tree: dict[str, dict[str, str]],
    commit: str,
    max_path_bytes: int,
) -> None:
    with tempfile.TemporaryDirectory(prefix="ndea_exp002_bundle_verify_") as raw:
        scratch = Path(raw).resolve()
        unbundle_repo = scratch / "unbundle.git"
        clone = scratch / "clone.git"
        runner.git("init", "--bare", "--template=", str(unbundle_repo), cwd=scratch)
        runner.git(
            "-C",
            str(unbundle_repo),
            "bundle",
            "verify",
            str(bundle),
            cwd=scratch,
        )
        unbundle_text = runner.git(
            "-C",
            str(unbundle_repo),
            "bundle",
            "unbundle",
            str(bundle),
            cwd=scratch,
        )
        assert isinstance(unbundle_text, str)
        unbundled_heads = parse_bundle_heads(unbundle_text, verifier, "fresh unbundle")
        if unbundled_heads != expected_heads:
            raise PackagingError(
                "fresh-unbundle ref set mismatch: "
                f"observed={unbundled_heads!r} expected={expected_heads!r}"
            )
        runner.git(
            "-C",
            str(unbundle_repo),
            "fsck",
            "--full",
            "--strict",
            "--no-dangling",
            cwd=scratch,
        )
        runner.git(
            "clone",
            "--bare",
            "--template=",
            str(bundle),
            str(clone),
            cwd=scratch,
        )
        runner.git(
            "-C",
            str(clone),
            "fsck",
            "--full",
            "--strict",
            "--no-dangling",
            cwd=scratch,
        )
        refs_text = runner.git(
            "-C",
            str(clone),
            "for-each-ref",
            "--format=%(objectname) %(refname)",
            "refs/heads/",
            "refs/tags/",
            cwd=scratch,
        )
        assert isinstance(refs_text, str)
        cloned_heads = parse_bundle_heads(refs_text, verifier, "fresh clone")
        if cloned_heads != expected_heads:
            raise PackagingError(
                "fresh-clone ref set mismatch: "
                f"observed={cloned_heads!r} expected={expected_heads!r}"
            )
        tree_payload = runner.git(
            "-C",
            str(clone),
            "ls-tree",
            "-rz",
            "-r",
            "--full-tree",
            commit,
            "--",
            *verifier.ARCHIVE_SELECTED_PATHS,
            binary=True,
            cwd=scratch,
        )
        assert isinstance(tree_payload, bytes)
        cloned_tree = verifier.parse_ls_tree(tree_payload, max_path_bytes)
        if cloned_tree != expected_tree:
            raise PackagingError(
                "fresh-clone selected tree differs from the source-selected tree: "
                f"clone_only={sorted(set(cloned_tree) - set(expected_tree))!r} "
                f"source_only={sorted(set(expected_tree) - set(cloned_tree))!r} "
                f"changed={sorted(path for path in set(cloned_tree) & set(expected_tree) if cloned_tree[path] != expected_tree[path])!r}"
            )


def strict_json(path: Path, verifier: ModuleType, label: str) -> dict[str, Any]:
    value = verifier.read_json_strict(path)
    return verifier.require_mapping(value, label)


def derive_direct_check_count(repo: Path, verifier: ModuleType) -> int:
    path = repo / verifier.JULIA_PATHS["regression_results"]
    results = strict_json(path, verifier, "validator regression results")
    if results.get("schema") != "ndea.exp002.validator_regression.v1" or results.get("all_passed") is not True:
        raise PackagingError("validator regression results are not a frozen PASS receipt")
    rows = results.get("results")
    if not isinstance(rows, list):
        raise PackagingError("validator regression results.rows is not a list")
    matches = [row for row in rows if isinstance(row, dict) and row.get("name") == "valid_full_absolute"]
    if len(matches) != 1 or matches[0].get("passed") is not True or matches[0].get("exit_code") != 0:
        raise PackagingError("cannot identify one passing valid_full_absolute regression row")
    stdout = matches[0].get("stdout")
    if not isinstance(stdout, str):
        raise PackagingError("valid_full_absolute stdout is absent")
    counts = re.findall(r"(?m)^CHECKS=([1-9][0-9]*)$", stdout)
    if len(counts) != 1:
        raise PackagingError("valid_full_absolute stdout does not contain one positive CHECKS count")
    certificate_hash = hash_regular(repo / verifier.JULIA_PATHS["certificate"])
    if f"CERTIFICATE_SHA256={certificate_hash}\n" not in stdout:
        raise PackagingError("valid_full_absolute stdout is not bound to the archived certificate")
    return int(counts[0])


def set_dotted(target: dict[str, Any], dotted: str, value: Any) -> None:
    parts = dotted.split(".")
    if not parts or any(not part for part in parts):
        raise PackagingError(f"invalid dotted receipt path: {dotted!r}")
    cursor = target
    for part in parts[:-1]:
        existing = cursor.setdefault(part, {})
        if not isinstance(existing, dict):
            raise PackagingError(f"receipt field collision at {dotted!r}")
        cursor = existing
    if parts[-1] in cursor and cursor[parts[-1]] != value:
        raise PackagingError(f"conflicting receipt values at {dotted!r}")
    cursor[parts[-1]] = value


def populate_spec(
    template: dict[str, Any],
    verifier: ModuleType,
    repo: Path,
    *,
    archive: Path,
    bundle: Path,
    receipt: Path,
    verification_output: Path,
    repository: dict[str, str],
    manifest: dict[str, Any],
) -> dict[str, Any]:
    result = copy.deepcopy(template)
    verifier.validate_spec(result)
    verifier.parse_limits(result)
    delivery = verifier.require_mapping(result["delivery"], "delivery")
    verifier.require_exact_keys(
        delivery,
        {
            "archive_path",
            "bundle_path",
            "receipt_path",
            "output_directory",
            "archive_sha256",
            "bundle_sha256",
            "receipt_sha256",
            "archive_root",
        },
        set(),
        "delivery",
    )
    delivery.update(
        {
            "archive_path": str(archive),
            "bundle_path": str(bundle),
            "receipt_path": str(receipt),
            "output_directory": str(verification_output),
            "archive_sha256": hash_regular(archive),
            "bundle_sha256": hash_regular(bundle),
            "receipt_sha256": "0" * 64,
            "archive_root": ARCHIVE_ROOT,
        }
    )
    result["repository"] = {
        "commit": repository["commit"],
        "tag": repository["tag"],
        "tag_object": repository["tag_object"],
        "branch": repository["branch"],
    }
    result["manifest"] = {
        "path": manifest["path"],
        "expected_sha256": manifest["sha256"],
        "expected_entries": manifest["entries"],
    }

    toolchain = (repo / "lean-toolchain").read_text(encoding="utf-8", errors="strict").splitlines()
    if len(toolchain) != 1:
        raise PackagingError("lean-toolchain must contain exactly one line")
    lake_manifest = strict_json(repo / "lake-manifest.json", verifier, "lake-manifest.json")
    mathlib = [
        row
        for row in lake_manifest.get("packages", [])
        if isinstance(row, dict) and row.get("name") == "mathlib"
    ]
    if len(mathlib) != 1 or verifier.GIT_OBJECT.fullmatch(str(mathlib[0].get("rev", ""))) is None:
        raise PackagingError("lake-manifest.json must contain one exact Mathlib revision")
    pins = verifier.require_mapping(result["pins"], "pins")
    verifier.require_exact_keys(
        pins,
        {"lean_toolchain", "lean_version", "mathlib_revision", "mathlib_input_revision"},
        set(),
        "pins",
    )
    pins["lean_toolchain"] = toolchain[0]
    version_match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+)", toolchain[0])
    if version_match is None:
        raise PackagingError("cannot derive Lean version from lean-toolchain")
    pins["lean_version"] = version_match.group(1)
    pins["mathlib_revision"] = mathlib[0]["rev"]
    try:
        lakefile = tomllib.loads((repo / "lakefile.toml").read_text(encoding="utf-8", errors="strict"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise PackagingError(f"cannot parse lakefile.toml: {error}") from error
    mathlib_requirements = [
        row
        for row in lakefile.get("require", [])
        if isinstance(row, dict) and row.get("name") == "mathlib"
    ]
    if len(mathlib_requirements) != 1 or not isinstance(mathlib_requirements[0].get("rev"), str):
        raise PackagingError("lakefile.toml must contain one exact Mathlib requirement")
    pins["mathlib_input_revision"] = mathlib_requirements[0]["rev"]

    julia = verifier.require_mapping(result["julia"], "julia")
    verifier.require_exact_keys(
        julia,
        {
            "validator_sha256",
            "certificate_sha256",
            "run_receipt_sha256",
            "regression_driver_sha256",
            "direct_check_count",
            "timeout_seconds",
        },
        set(),
        "julia",
    )
    for key in ("validator", "certificate", "run_receipt", "regression_driver"):
        julia[f"{key}_sha256"] = hash_regular(repo / verifier.JULIA_PATHS[key])
    julia["direct_check_count"] = derive_direct_check_count(repo, verifier)
    verifier.require_integer(julia["timeout_seconds"], "julia.timeout_seconds", minimum=1, maximum=3600)

    lean_evidence = verifier.require_mapping(result["lean_evidence"], "lean_evidence")
    verifier.require_exact_keys(
        lean_evidence,
        {"roles", "allowed_axioms", "forbidden_tokens"},
        set(),
        "lean_evidence",
    )
    roles = verifier.require_mapping(lean_evidence["roles"], "lean evidence roles")
    if set(roles) != set(verifier.REQUIRED_LEAN_ROLES):
        raise PackagingError("spec template Lean role set differs from verifier requirements")
    for role, config in roles.items():
        relative = verifier.canonical_relative(config.get("metadata_path"), f"{role} metadata", 4096)
        config["metadata_sha256"] = hash_regular(repo.joinpath(*PurePosixPath(relative).parts))
    return result


def build_remote_receipt(
    spec: dict[str, Any],
    verifier: ModuleType,
    repository: dict[str, str],
    manifest: dict[str, Any],
    archive: Path,
    bundle: Path,
    commands: list[dict[str, Any]],
) -> dict[str, Any]:
    archive_hash = hash_regular(archive)
    bundle_hash = hash_regular(bundle)
    context = {
        "archive_sha256": archive_hash,
        "bundle_sha256": bundle_hash,
        "commit": repository["commit"],
        "tag": repository["tag"],
        "tag_object": repository["tag_object"],
        "manifest_sha256": manifest["sha256"],
        "manifest_entries": manifest["entries"],
    }
    receipt: dict[str, Any] = {
        "schema": REMOTE_RECEIPT_SCHEMA,
        "created_utc": utc_now(),
        "overall_status": "PASS",
        "external_review": "PENDING",
        "generator": {
            "schema": PACKAGER_SCHEMA,
            "path": f"{EXP_ROOT}/assurance/{Path(__file__).name}",
            "sha256": hash_regular(Path(__file__).resolve()),
        },
        "repository": {
            "commit": repository["commit"],
            "branch": repository["branch"],
            "tag": repository["tag"],
            "tag_object": repository["tag_object"],
            "immutable_exp001_tag": repository["exp001_tag"],
            "immutable_exp001_tag_object": repository["exp001_tag_object"],
            "immutable_exp001_commit": repository["exp001_commit"],
        },
        "internal_manifest": {
            "path": manifest["path"],
            "sha256": manifest["sha256"],
            "entries": manifest["entries"],
            "status": "PASS",
        },
        "artifacts": {
            "archive": {
                "path": str(archive),
                "sha256": archive_hash,
                "size_bytes": archive.stat().st_size,
            },
            "bundle": {
                "path": str(bundle),
                "sha256": bundle_hash,
                "size_bytes": bundle.stat().st_size,
            },
        },
        "packaging_commands": commands,
        "causal_boundary": (
            "This adjacent receipt records packaging checks; independent fresh-extraction "
            "verification and external human review remain separate."
        ),
    }
    contract = verifier.require_mapping(spec.get("receipt_contract"), "receipt_contract")
    verifier.require_exact_keys(
        contract,
        {
            "schema_field",
            "schema_value",
            "status_field",
            "external_review_field",
            "bindings",
            "expectations",
        },
        set(),
        "receipt_contract",
    )
    schema_field = verifier.require_string(contract["schema_field"], "receipt_contract.schema_field")
    schema_value = verifier.require_string(contract["schema_value"], "receipt_contract.schema_value")
    status_field = verifier.require_string(contract["status_field"], "receipt_contract.status_field")
    review_field = verifier.require_string(
        contract["external_review_field"], "receipt_contract.external_review_field"
    )
    if schema_value != REMOTE_RECEIPT_SCHEMA:
        raise PackagingError(
            f"receipt schema drift: observed={schema_value!r} expected={REMOTE_RECEIPT_SCHEMA!r}"
        )
    set_dotted(receipt, schema_field, schema_value)
    set_dotted(receipt, status_field, "PASS")
    set_dotted(receipt, review_field, "PENDING")
    expectations = verifier.require_mapping(contract.get("expectations"), "receipt_contract.expectations")
    for field, value in expectations.items():
        verifier.require_string(field, "receipt expectation field")
        set_dotted(receipt, field, value)
    bindings = verifier.require_mapping(contract.get("bindings"), "receipt_contract.bindings")
    required_sources = {
        "archive_sha256",
        "bundle_sha256",
        "commit",
        "tag",
        "tag_object",
        "manifest_sha256",
        "manifest_entries",
    }
    if not required_sources <= set(bindings.values()):
        raise PackagingError("receipt contract omits one or more verifier-required binding sources")
    for field, source in bindings.items():
        verifier.require_string(field, "receipt binding field")
        verifier.require_string(source, f"receipt binding source for {field}")
        if source not in context:
            raise PackagingError(f"receipt contract names unknown source {source!r}")
        set_dotted(receipt, field, context[source])
    if receipt.get("external_review") != "PENDING":
        raise PackagingError("external_review must remain PENDING")
    return receipt


def verifier_mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise PackagingError(f"{label} must be a JSON object")
    return value


def reject_unresolved_placeholders(value: Any, label: str = "spec") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            reject_unresolved_placeholders(child, f"{label}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_unresolved_placeholders(child, f"{label}[{index}]")
    elif isinstance(value, str) and (
        value in {"0" * 40, "0" * 64}
        or "YYYYMMDD" in value
        or value.startswith("/ABS/PATH/")
    ):
        raise PackagingError(f"unresolved verifier-spec placeholder at {label}: {value!r}")


def verify_exp001_external_inputs(exp001: dict[str, Any], verifier: ModuleType) -> None:
    verifier.require_exact_keys(
        exp001,
        {
            "archive",
            "bundle",
            "tag",
            "tag_object",
            "commit",
            "subtree_ids",
            "pin_blob_ids",
            "additional_files",
        },
        set(),
        "exp001",
    )
    descriptors: list[tuple[str, dict[str, Any]]] = []
    for role in ("archive", "bundle"):
        descriptor = verifier.require_mapping(exp001[role], f"exp001.{role}")
        verifier.require_exact_keys(descriptor, {"path", "sha256"}, set(), f"exp001.{role}")
        descriptors.append((role, descriptor))
    additional = verifier.require_list(exp001["additional_files"], "exp001.additional_files")
    for index, raw in enumerate(additional):
        descriptor = verifier.require_mapping(raw, f"exp001.additional_files[{index}]")
        verifier.require_exact_keys(
            descriptor,
            {"label", "path", "sha256"},
            set(),
            f"exp001.additional_files[{index}]",
        )
        label = verifier.require_string(descriptor["label"], f"exp001.additional_files[{index}].label")
        descriptors.append((label, descriptor))
    for label, descriptor in descriptors:
        path = require_regular(
            Path(verifier.require_string(descriptor["path"], f"exp001 {label} path")),
            f"Exp001 {label}",
        )
        expected = verifier.require_sha(descriptor["sha256"], f"exp001 {label} sha256")
        observed = hash_regular(path)
        if observed != expected:
            raise PackagingError(
                f"immutable Exp001 external hash mismatch for {label}: "
                f"observed={observed} expected={expected}"
            )


def archive_hashes(archive: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    try:
        with tarfile.open(archive, "r:gz") as stream:
            for member in stream:
                if not member.isreg():
                    continue
                source = stream.extractfile(member)
                if source is None:
                    raise PackagingError(f"cannot read archived file: {member.name!r}")
                digest = hashlib.sha256()
                with source:
                    for block in iter(lambda: source.read(1024 * 1024), b""):
                        digest.update(block)
                relative = PurePosixPath(member.name).relative_to(ARCHIVE_ROOT).as_posix()
                result[relative] = digest.hexdigest()
    except (OSError, tarfile.TarError, ValueError) as error:
        raise PackagingError(f"cannot hash generated archive: {error}") from error
    return result


def preserve_failed_output(output: Path, error: BaseException) -> tuple[Path, Path]:
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    fingerprint = hashlib.sha256(
        f"{type(error).__name__}\0{error}\0{output}\0{time.time_ns()}".encode(
            "utf-8", errors="replace"
        )
    ).hexdigest()[:16]
    safe_name = re.sub(r"[^A-Za-z0-9._+-]+", "_", output.name)[:80] or "package"
    forensic = Path(
        tempfile.mkdtemp(
            prefix=f".{safe_name}.FAILED-{timestamp}-{fingerprint}-",
            dir=output.parent,
        )
    ).resolve()
    os.chmod(forensic, 0o700)
    preserved = forensic / "partial_output"
    try:
        with os.scandir(output) as iterator:
            entries = sorted(entry.name for entry in iterator)
    except OSError:
        entries = []
    marker = forensic / FAILURE_MARKER
    write_exclusive(
        marker,
        json_bytes(
            {
                "schema": FAILURE_SCHEMA,
                "created_utc": utc_now(),
                "overall_status": "FAIL",
                "requested_output_directory": str(output),
                "preserved_output_directory": str(preserved),
                "observed_entries": entries,
                "failure": {
                    "type": type(error).__name__,
                    "message": str(error),
                },
                "causal_boundary": (
                    "This marker records an incomplete packaging attempt.  Files below "
                    "partial_output are forensic leftovers and are not a final delivery."
                ),
            }
        ),
    )
    try:
        os.rename(output, preserved)
    except OSError as rename_error:
        raise PackagingError(
            f"cannot atomically preserve failed output {output} below {forensic}: {rename_error}"
        ) from rename_error
    return forensic, marker


def build_created_package(
    args: argparse.Namespace,
    verifier: ModuleType,
    repo: Path,
    template: dict[str, Any],
    limits: dict[str, int],
    output: Path,
    verification_output: Path,
    names: dict[str, str],
    runner: CommandRunner,
    repository: dict[str, str],
    manifest: dict[str, Any],
    tree: dict[str, dict[str, str]],
) -> dict[str, Any]:
    archive = output / names["archive"]
    bundle = output / names["bundle"]
    receipt_path = output / names["receipt"]
    spec_path = output / names["spec"]

    try:
        with archive.open("xb") as archive_stream:
            runner.run(
                [
                    "git",
                    "archive",
                    "--format=tar.gz",
                    f"--prefix={ARCHIVE_ROOT}/",
                    args.commit,
                    "--",
                    *verifier.ARCHIVE_SELECTED_PATHS,
                ],
                stdout_file=archive_stream,
            )
    except OSError as error:
        raise PackagingError(f"cannot exclusively create archive: {error}") from error
    scanned = verifier.scan_tar(archive, ARCHIVE_ROOT, args.commit, limits)
    archived_files = {
        row["name"][len(ARCHIVE_ROOT) + 1 :]
        for row in scanned
        if row["kind"] == "file"
    }
    if archived_files != set(tree):
        raise PackagingError("generated archive file set differs from selected final Git tree")
    committed_hashes = {
        relative: hash_regular(path)
        for relative, path in selected_regular_files(
            repo, verifier, exclude_manifest=False
        ).items()
    }
    if archive_hashes(archive) != committed_hashes:
        raise PackagingError("generated archive bytes differ from the clean selected worktree")
    if archive.stat().st_size > limits["max_archive_bytes"]:
        raise PackagingError("generated archive exceeds verifier size limit")

    runner.git(
        "bundle",
        "create",
        str(bundle),
        f"refs/heads/{args.branch}",
        f"refs/tags/{args.final_tag}",
        f"refs/tags/{repository['exp001_tag']}",
    )
    if not bundle.is_file() or bundle.is_symlink():
        raise PackagingError("git bundle did not create one regular non-link file")
    runner.git("bundle", "verify", str(bundle))
    bundle_heads_text = runner.git("bundle", "list-heads", str(bundle))
    assert isinstance(bundle_heads_text, str)
    heads = parse_bundle_heads(bundle_heads_text, verifier, "bundle")
    expected_heads = {
        f"refs/heads/{args.branch}": args.commit,
        f"refs/tags/{args.final_tag}": repository["tag_object"],
        f"refs/tags/{repository['exp001_tag']}": repository["exp001_tag_object"],
    }
    if heads != expected_heads:
        raise PackagingError(
            f"bundle ref set mismatch: observed={heads!r} expected={expected_heads!r}"
        )
    verify_bundle_in_fresh_repository(
        runner,
        verifier,
        bundle,
        expected_heads,
        tree,
        args.commit,
        limits["max_path_bytes"],
    )

    # Ensure packaging observed one stable repository state before issuing PASS.
    ending = require_clean_final_state(
        runner,
        verifier,
        commit=args.commit,
        branch=args.branch,
        final_tag=args.final_tag,
        exp001_tag=repository["exp001_tag"],
        exp001_tag_object=repository["exp001_tag_object"],
        exp001_commit=repository["exp001_commit"],
    )
    if ending != repository or validate_manifest(repo, verifier) != manifest:
        raise PackagingError("repository or final manifest changed while packaging")
    require_new_absolute_directory(
        verification_output, "fresh-verification output directory"
    )

    generated_spec = populate_spec(
        template,
        verifier,
        repo,
        archive=archive,
        bundle=bundle,
        receipt=receipt_path,
        verification_output=verification_output,
        repository=repository,
        manifest=manifest,
    )
    receipt = build_remote_receipt(
        generated_spec,
        verifier,
        repository,
        manifest,
        archive,
        bundle,
        runner.records,
    )
    write_exclusive(receipt_path, json_bytes(receipt))
    generated_spec["delivery"]["receipt_sha256"] = hash_regular(receipt_path)
    verifier.validate_spec(generated_spec)
    verifier.parse_limits(generated_spec)
    reject_unresolved_placeholders(generated_spec)
    role_limit = generated_spec["limits"]["max_path_bytes"]
    for role, config in generated_spec["lean_evidence"]["roles"].items():
        verifier.validate_role_config(role, config, role_limit)
    write_exclusive(spec_path, json_bytes(generated_spec))

    artifact_hashes = {
        names["archive"]: hash_regular(archive),
        names["bundle"]: hash_regular(bundle),
        names["receipt"]: hash_regular(receipt_path),
        names["spec"]: hash_regular(spec_path),
    }
    delivery_payload = "".join(
        f"{digest}  {name}\n" for name, digest in sorted(artifact_hashes.items())
    ).encode("utf-8")
    write_exclusive(output / DELIVERY_MANIFEST, delivery_payload)
    if hash_regular(archive) != generated_spec["delivery"]["archive_sha256"]:
        raise PackagingError("archive changed after spec creation")
    if hash_regular(bundle) != generated_spec["delivery"]["bundle_sha256"]:
        raise PackagingError("bundle changed after spec creation")
    if hash_regular(receipt_path) != generated_spec["delivery"]["receipt_sha256"]:
        raise PackagingError("receipt changed after spec creation")
    return {
        "schema": PACKAGER_SCHEMA,
        "status": "PASS",
        "external_review": "PENDING",
        "output_directory": str(output),
        "repository": repository,
        "internal_manifest": manifest,
        "artifacts": {
            name: {
                "path": str(output / filename),
                "sha256": artifact_hashes[filename],
                "size_bytes": (output / filename).stat().st_size,
            }
            for name, filename in names.items()
        },
        "delivery_manifest": {
            "path": str(output / DELIVERY_MANIFEST),
            "sha256": hash_regular(output / DELIVERY_MANIFEST),
            "entries": len(artifact_hashes),
        },
        "next_command": [
            sys.executable,
            str(VERIFIER_PATH),
            "--spec",
            str(spec_path),
        ],
    }


def create_package(args: argparse.Namespace, verifier: ModuleType) -> dict[str, Any]:
    repo = require_canonical_directory(Path(args.repo_root), "repository root")
    if not (repo / ".git").exists():
        raise PackagingError(f"not a Git working tree: {repo}")
    template_path = require_regular(Path(args.spec_template), "verifier spec template")
    template = strict_json(template_path, verifier, "verifier spec template")
    verifier.validate_spec(template)
    limits = verifier.parse_limits(template)
    output = require_new_absolute_directory(Path(args.output_directory), "package output directory")
    verification_output = require_new_absolute_directory(
        Path(args.verification_output_directory), "fresh-verification output directory"
    )
    require_distinct_directories(output, verification_output)
    if os.path.commonpath((str(repo), str(output))) == str(repo):
        raise PackagingError("package output directory must be outside the repository")
    if os.path.commonpath((str(repo), str(verification_output))) == str(repo):
        raise PackagingError("verification output directory must be outside the repository")

    names = {
        "archive": require_safe_filename(args.archive_name, "archive name"),
        "bundle": require_safe_filename(args.bundle_name, "bundle name"),
        "receipt": require_safe_filename(args.receipt_name, "receipt name"),
        "spec": require_safe_filename(args.spec_name, "spec name"),
    }
    if len(set(names.values()) | {DELIVERY_MANIFEST}) != len(names) + 1:
        raise PackagingError("package output filenames must be distinct")

    exp001 = verifier_mapping(template.get("exp001"), "exp001")
    verify_exp001_external_inputs(exp001, verifier)
    exp001_tag = args.exp001_tag or str(exp001.get("tag", ""))
    if exp001_tag != exp001.get("tag"):
        raise PackagingError("--exp001-tag differs from the verifier template")
    exp001_tag_object = str(exp001.get("tag_object", ""))
    exp001_commit = str(exp001.get("commit", ""))
    if verifier.GIT_OBJECT.fullmatch(exp001_tag_object) is None or verifier.GIT_OBJECT.fullmatch(exp001_commit) is None:
        raise PackagingError("template has invalid immutable Experiment 001 object IDs")

    runner = CommandRunner(repo, verifier, limits["command_timeout_seconds"])
    require_plain_complete_git_repository(runner)
    repository = require_clean_final_state(
        runner,
        verifier,
        commit=args.commit,
        branch=args.branch,
        final_tag=args.final_tag,
        exp001_tag=exp001_tag,
        exp001_tag_object=exp001_tag_object,
        exp001_commit=exp001_commit,
    )
    manifest = validate_manifest(repo, verifier)
    tree = verify_selected_git_tree(runner, verifier, repo, args.commit)

    output.mkdir(parents=False, exist_ok=False)
    try:
        os.chmod(output, 0o700)
        return build_created_package(
            args,
            verifier,
            repo,
            template,
            limits,
            output,
            verification_output,
            names,
            runner,
            repository,
            manifest,
            tree,
        )
    except BaseException as error:
        try:
            forensic, marker = preserve_failed_output(output, error)
        except BaseException as preservation_error:
            raise PackagingError(
                f"packaging failed ({type(error).__name__}: {error}); "
                f"failed output remains at {output}; forensic preservation also failed: "
                f"{type(preservation_error).__name__}: {preservation_error}"
            ) from error
        raise PackagingError(
            f"packaging failed ({type(error).__name__}: {error}); incomplete output was "
            f"preserved at {forensic} with failure marker {marker}"
        ) from error


def self_test(verifier: ModuleType) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="ndea_exp002_packager_test_") as raw:
        root = Path(raw).resolve()
        verifier_copy = root / "verify_exp002_final_delivery.py"
        verifier_copy.write_bytes(VERIFIER_PATH.read_bytes())
        original_dont_write_bytecode = sys.dont_write_bytecode
        try:
            sys.dont_write_bytecode = False
            load_verifier(verifier_copy)
            if sys.dont_write_bytecode:
                raise PackagingError("self-test bytecode setting was not restored")
        finally:
            sys.dont_write_bytecode = original_dont_write_bytecode
        if (root / "__pycache__").exists():
            raise PackagingError("self-test verifier import created a bytecode cache")
        same_output = root / "same-output"
        try:
            require_distinct_directories(same_output, same_output)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test equal output-directory rejection failed")
        (root / "tree").mkdir()
        (root / "one.txt").write_bytes(b"one\n")
        (root / "tree" / "two.txt").write_bytes(b"two\n")
        files = {"one.txt": root / "one.txt", "tree/two.txt": root / "tree/two.txt"}
        fake_verifier = ModuleType("fake_manifest_verifier")
        fake_verifier.ARCHIVE_SELECTED_PATHS = ("one.txt", "tree")
        fake_verifier.canonical_relative = verifier.canonical_relative
        selected = selected_regular_files(root, fake_verifier, exclude_manifest=True)
        if list(selected) != ["one.txt", "tree/two.txt"]:
            raise PackagingError("self-test selected-file enumeration failed")
        payload = render_manifest(files)
        one_hash = hashlib.sha256(b"one\n").hexdigest()
        two_hash = hashlib.sha256(b"two\n").hexdigest()
        expected = (
            f"{one_hash}  one.txt\n"
            f"{two_hash}  tree/two.txt\n"
        ).encode("utf-8")
        if payload != expected:
            raise PackagingError("self-test manifest rendering failed")
        target = root / "exclusive"
        write_exclusive(target, b"frozen\n")
        try:
            write_exclusive(target, b"overwrite\n")
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test exclusive-write rejection failed")
        receipt: dict[str, Any] = {}
        set_dotted(receipt, "a.b", "fixed")
        try:
            set_dotted(receipt, "a.b", "changed")
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test dotted-field collision rejection failed")
        (root / "tree" / "forbidden-link").symlink_to(root / "one.txt")
        try:
            selected_regular_files(root, fake_verifier, exclude_manifest=True)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test selected-tree symlink rejection failed")
        failed_output = root / "failed-output"
        failed_output.mkdir()
        (failed_output / "partial.bin").write_bytes(b"partial\n")
        forensic, marker = preserve_failed_output(
            failed_output, PackagingError("synthetic late failure")
        )
        failure_record = verifier.require_mapping(
            verifier.read_json_strict(marker), "self-test failure marker"
        )
        if (
            failed_output.exists()
            or forensic.parent != root
            or failure_record.get("schema") != FAILURE_SCHEMA
            or failure_record.get("overall_status") != "FAIL"
            or (forensic / "partial_output" / "partial.bin").read_bytes() != b"partial\n"
        ):
            raise PackagingError("self-test failed-output forensic preservation failed")
    with tempfile.TemporaryDirectory(prefix="ndea_exp002_manifest_test_") as raw:
        repo = Path(raw).resolve()
        initialized = subprocess.run(
            ["git", "init", "-q"],
            cwd=repo,
            env=clean_git_environment(verifier),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if initialized.returncode != 0:
            raise PackagingError(
                "self-test cannot initialize temporary Git repository: "
                f"{initialized.stderr.decode('utf-8', 'replace')}"
            )
        fixture_bytes = {
            "lean-toolchain": b"leanprover/lean4:v4.31.0\n",
            "lakefile.toml": b'name = "fixture"\n',
            "lake-manifest.json": b"{}\n",
            "NDEAEvolve.lean": b"import NDEAEvolve.Basic\n",
            "NDEAEvolve/Basic.lean": b"def fixture := 1\n",
            "NDEAEvolve/Experiments/Exp002/Fixture.lean": b"theorem fixture : True := by trivial\n",
            f"{EXP_ROOT}/README.md": b"fixture\n",
        }
        for relative, payload in fixture_bytes.items():
            path = repo.joinpath(*PurePosixPath(relative).parts)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
        first = write_manifest(repo, verifier)
        if first["disposition"] != "CREATED_EXCLUSIVELY":
            raise PackagingError("self-test manifest exclusive creation failed")
        second = write_manifest(repo, verifier)
        if second["disposition"] != "ALREADY_IDENTICAL":
            raise PackagingError("self-test manifest idempotent validation failed")
        changed = repo / "NDEAEvolve" / "Basic.lean"
        changed.write_bytes(b"def fixture := 2\n")
        try:
            write_manifest(repo, verifier)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test differing-manifest overwrite rejection failed")
        (repo / ".gitignore").write_text("*.ignored\n", encoding="utf-8")
        ignored = repo / EXP_ROOT / "generated.ignored"
        ignored.write_bytes(b"ignored\n")
        ignored_files = selected_regular_files(repo, verifier, exclude_manifest=False)
        try:
            reject_ignored_selected_files(repo, ignored_files, verifier)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test ignored-selected-file rejection failed")
        staged = subprocess.run(
            ["git", "add", "-f", ignored.relative_to(repo).as_posix()],
            cwd=repo,
            env=clean_git_environment(verifier),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if staged.returncode != 0:
            raise PackagingError(
                "self-test cannot stage ignored selected fixture: "
                f"{staged.stderr.decode('utf-8', 'replace')}"
            )
        try:
            reject_ignored_selected_files(repo, ignored_files, verifier)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test tracked-but-ignored selected-file rejection failed")
    with tempfile.TemporaryDirectory(prefix="ndea_exp002_bundle_test_") as raw:
        root = Path(raw).resolve()
        repo = root / "repo"

        def fixture_git(*arguments: str) -> str:
            completed = subprocess.run(
                ["git", *arguments],
                cwd=repo if repo.exists() else root,
                env=clean_git_environment(verifier),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
            )
            if completed.returncode != 0:
                raise PackagingError(
                    f"self-test Git command failed: {arguments!r}: "
                    f"{completed.stderr.decode('utf-8', 'replace')}"
                )
            return completed.stdout.decode("utf-8", errors="strict").strip()

        fixture_git("init", "-q", "-b", "main", str(repo))
        (repo / "one.txt").write_bytes(b"one\n")
        fixture_git("add", "one.txt")
        fixture_git(
            "-c",
            "user.name=Packager Self-Test",
            "-c",
            "user.email=packager-self-test@example.invalid",
            "commit",
            "-q",
            "-m",
            "fixture",
        )
        for tag in ("old", "final"):
            fixture_git(
                "-c",
                "user.name=Packager Self-Test",
                "-c",
                "user.email=packager-self-test@example.invalid",
                "tag",
                "-a",
                tag,
                "-m",
                tag,
            )
        fake_git_verifier = ModuleType("fake_git_verifier")
        fake_git_verifier.ARCHIVE_SELECTED_PATHS = ("one.txt",)
        fake_git_verifier.GIT_OBJECT = verifier.GIT_OBJECT
        fake_git_verifier.SAFE_REF = verifier.SAFE_REF
        fake_git_verifier.clean_git_environment = verifier.clean_git_environment
        fake_git_verifier.parse_ls_tree = verifier.parse_ls_tree
        runner = CommandRunner(repo, fake_git_verifier, 30)
        require_plain_complete_git_repository(runner)
        commit = fixture_git("rev-parse", "HEAD")
        tree_payload = runner.git(
            "ls-tree", "-rz", "-r", "--full-tree", commit, "--", "one.txt", binary=True
        )
        assert isinstance(tree_payload, bytes)
        tree = verifier.parse_ls_tree(tree_payload, 4096)
        bundle = root / "fixture.bundle"
        runner.git(
            "bundle",
            "create",
            str(bundle),
            "refs/heads/main",
            "refs/tags/final",
            "refs/tags/old",
        )
        expected_heads = {
            "refs/heads/main": commit,
            "refs/tags/final": fixture_git("rev-parse", "refs/tags/final"),
            "refs/tags/old": fixture_git("rev-parse", "refs/tags/old"),
        }
        verify_bundle_in_fresh_repository(
            runner,
            fake_git_verifier,
            bundle,
            expected_heads,
            tree,
            commit,
            4096,
        )
        fixture_git("update-ref", f"refs/replace/{commit}", commit)
        try:
            require_plain_complete_git_repository(runner)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test replacement-ref rejection failed")
        fixture_git("update-ref", "-d", f"refs/replace/{commit}")
        grafts = Path(fixture_git("rev-parse", "--git-path", "info/grafts"))
        if not grafts.is_absolute():
            grafts = repo / grafts
        grafts.parent.mkdir(parents=True, exist_ok=True)
        grafts.write_bytes(b"")
        try:
            require_plain_complete_git_repository(runner)
        except PackagingError:
            pass
        else:
            raise PackagingError("self-test graft-file rejection failed")
    return {
        "schema": PACKAGER_SCHEMA,
        "status": "PASS",
        "tests": [
            "selected_file_enumeration",
            "sorted_manifest",
            "exclusive_write",
            "dotted_collision",
            "selected_tree_symlink_rejection",
            "verifier_import_without_bytecode_cache",
            "verifier_import_setting_restoration",
            "equal_output_directory_rejection",
            "failed_output_forensic_preservation",
            "full_manifest_exclusive_creation",
            "full_manifest_idempotent_validation",
            "differing_manifest_overwrite_rejection",
            "ignored_selected_file_rejection",
            "tracked_but_ignored_selected_file_rejection",
            "fresh_bundle_unbundle_clone_fsck",
            "fresh_bundle_exact_refs_and_tree",
            "replacement_ref_rejection",
            "graft_file_rejection",
        ],
        "selected_path_drift_guard": list(verifier.ARCHIVE_SELECTED_PATHS),
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subcommands = result.add_subparsers(dest="command", required=True)
    for name in ("manifest-write", "manifest-check"):
        command = subcommands.add_parser(name)
        command.add_argument("--repo-root", required=True)
    package = subcommands.add_parser("package")
    package.add_argument("--repo-root", required=True)
    package.add_argument("--spec-template", required=True)
    package.add_argument("--output-directory", required=True)
    package.add_argument("--verification-output-directory", required=True)
    package.add_argument("--commit", required=True)
    package.add_argument("--branch", required=True)
    package.add_argument("--final-tag", required=True)
    package.add_argument("--exp001-tag")
    package.add_argument("--archive-name", default="NDEA_Evolve_exp002_final_evidence.tar.gz")
    package.add_argument("--bundle-name", default="NDEA_Evolve_exp002_final.bundle")
    package.add_argument("--receipt-name", default="NDEA_Evolve_exp002_final_delivery_receipt.json")
    package.add_argument("--spec-name", default="NDEA_Evolve_exp002_final_verifier_spec.json")
    subcommands.add_parser("self-test")
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        verifier = load_verifier()
        if args.command == "manifest-write":
            repo = require_canonical_directory(Path(args.repo_root), "repository root")
            outcome = write_manifest(repo, verifier)
        elif args.command == "manifest-check":
            repo = require_canonical_directory(Path(args.repo_root), "repository root")
            outcome = {"schema": PACKAGER_SCHEMA, "status": "PASS", **validate_manifest(repo, verifier)}
        elif args.command == "package":
            outcome = create_package(args, verifier)
        else:
            outcome = self_test(verifier)
    except Exception as error:
        print(f"PACKAGING_STATUS=FAIL\nERROR={type(error).__name__}: {error}", file=sys.stderr)
        return 1
    print(json.dumps(outcome, indent=2, sort_keys=True))
    print("PACKAGING_STATUS=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
