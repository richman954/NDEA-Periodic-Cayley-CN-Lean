#!/usr/bin/env python3
"""Package an already committed Step-5 release and verify recovery locally.

This helper does not build Lean, commit, tag, publish, or rewrite repository files.
It creates a new external release directory and refuses to reuse an existing one.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import time


EXPERIMENT = "experiments/exp003_continuous_exponential_comparison"
FINAL_MANIFEST = f"{EXPERIMENT}/evidence/FINAL_SHA256SUMS"
DEFAULT_RELEASE = Path("/home/richman954/NDEA_Evolve_offruntime/exp003_step5/releases/20260907_verified_final")
ARCHIVE_PREFIX = "NDEA_Evolve/"
PREDECESSOR_TAG = "exp003-step4-finite-n-telescoping-global-bound-verified-final-20260907"
PREDECESSOR_COMMIT = "902a5d44c222254a443a01aebf563df72b8154d5"


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


class Delivery:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.repo = args.repo.resolve(strict=True)
        self.release = args.release_dir.absolute()
        require(not self.release.exists() and not self.release.is_symlink(),
                f"Refusing to reuse existing release path: {self.release}")
        require(not self.release.resolve().is_relative_to(self.repo),
                "Release directory must be outside the source repository.")
        require(re.fullmatch(r"[0-9a-f]{40}", args.commit) is not None,
                "--commit must be the full 40-character expected commit hash.")
        require(args.timeout > 0, "--timeout must be positive.")
        self.archive = self.release / "exp003_step5_verified_final_source.tar.gz"
        self.bundle = self.release / "exp003_step5_verified_final.bundle"
        self.receipt = self.release / "DELIVERY_RECEIPT.json"
        self.release_created = False
        self.record: dict = {
            "schema": "ndea.exp003.step5.delivery.v1",
            "start_utc": utc_now(), "repo": str(self.repo),
            "expected_commit": args.commit, "release_tag": args.tag,
            "release_directory": str(self.release), "commands": [],
            "helper_sha256": sha256(Path(__file__)),
            "verification_scope": "Local archive and Git-bundle recovery; no Lean builds or publication.",
        }

    def run(self, label: str, command: list[str], *, cwd: Path | None = None) -> str:
        entry = {"label": label, "command": command, "cwd": str(cwd or self.repo),
                 "start_utc": utc_now(), "timeout_seconds": self.args.timeout}
        self.record["commands"].append(entry)
        begin = time.monotonic()
        try:
            result = subprocess.run(command, cwd=cwd or self.repo, text=True,
                                    capture_output=True, timeout=self.args.timeout)
            entry.update({"exit_code": result.returncode, "stdout": result.stdout,
                          "stderr": result.stderr, "timed_out": False})
            require(result.returncode == 0,
                    f"{label} failed with exit {result.returncode}: {result.stderr[-3000:]}")
            return result.stdout
        except subprocess.TimeoutExpired as error:
            entry.update({"exit_code": 124, "timed_out": True,
                          "stdout": (error.stdout or b"").decode(errors="replace")
                          if isinstance(error.stdout, bytes) else (error.stdout or ""),
                          "stderr": (error.stderr or b"").decode(errors="replace")
                          if isinstance(error.stderr, bytes) else (error.stderr or "")})
            raise RuntimeError(f"{label} exceeded its bounded timeout.") from error
        finally:
            entry.update({"end_utc": utc_now(),
                          "elapsed_seconds": round(time.monotonic() - begin, 6)})

    def git(self, label: str, *arguments: str, repo: Path | None = None) -> str:
        target = repo or self.repo
        return self.run(label, ["git", "-C", str(target), *arguments], cwd=target)

    def repository_state(self, repo: Path, label: str, branch: str) -> dict:
        head = self.git(f"{label}_head", "rev-parse", "HEAD", repo=repo).strip()
        tag = self.git(f"{label}_tag", "rev-parse",
                       f"refs/tags/{self.args.tag}^{{commit}}", repo=repo).strip()
        tag_object = self.git(f"{label}_tag_object", "rev-parse",
                              f"refs/tags/{self.args.tag}", repo=repo).strip()
        branch_commit = self.git(f"{label}_branch_commit", "rev-parse",
                                 f"refs/heads/{branch}", repo=repo).strip()
        current_branch = self.git(f"{label}_current_branch", "symbolic-ref", "--short", "HEAD",
                                  repo=repo).strip()
        status = self.git(f"{label}_clean", "status", "--porcelain=v1", "--untracked-files=all",
                          repo=repo)
        require(head == tag == branch_commit == self.args.commit,
                f"{label} HEAD, tag, and branch must all resolve to the expected commit.")
        require(current_branch == branch, f"{label} checked-out branch differs from the expected branch.")
        require(status == "", f"{label} worktree is not clean.")
        return {"head": head, "tag_peeled": tag, "tag_object": tag_object,
                "branch": branch, "status_porcelain_v1": status}

    def manifest(self, repo: Path, label: str) -> dict:
        manifest = repo / FINAL_MANIFEST
        if not manifest.is_file():
            require(not self.args.require_manifest, f"Required final manifest is absent in {label}.")
            return {"present": False, "verified": False, "reason": "FINAL_SHA256SUMS absent"}
        seen: set[str] = set()
        for line in manifest.read_text(encoding="utf-8").splitlines():
            require(bool(line), f"Blank checksum manifest row in {label}.")
            match = re.fullmatch(r"([0-9a-f]{64}) [ *](.+)", line)
            require(match is not None, f"Invalid checksum manifest row in {label}: {line!r}")
            relative = match.group(2)
            path = PurePosixPath(relative)
            require(not path.is_absolute() and ".." not in path.parts
                    and path.as_posix() == relative and relative not in seen,
                    f"Unsafe or duplicate checksum manifest path in {label}: {relative!r}")
            target = repo / relative
            require(target.is_file() and target.resolve().is_relative_to(repo.resolve()),
                    f"Checksum manifest target is absent or outside {label}: {relative}")
            seen.add(relative)
        require(bool(seen), f"Final checksum manifest is empty in {label}.")
        self.run(f"{label}_manifest_sha256sum",
                 ["sha256sum", "--check", "--strict", FINAL_MANIFEST], cwd=repo)
        return {"present": True, "verified": True, "path": FINAL_MANIFEST,
                "sha256": sha256(manifest), "entry_count": len(seen)}

    def inspect_archive(self, tracked: set[str]) -> dict:
        files: set[str] = set()
        with tarfile.open(self.archive, "r:gz") as archive:
            for member in archive:
                path = PurePosixPath(member.name)
                require(not path.is_absolute() and ".." not in path.parts
                        and path.parts and path.parts[0] == "NDEA_Evolve",
                        f"Unexpected archive path: {member.name!r}")
                require(member.isfile() or member.isdir(),
                        f"Archive member is not a regular file or directory: {member.name!r}")
                if member.isfile():
                    relative = path.relative_to("NDEA_Evolve").as_posix()
                    require(relative not in files, f"Duplicate archive member: {relative}")
                    files.add(relative)
        require(files == tracked,
                f"Archive differs from tracked source tree: missing={sorted(tracked-files)}, extra={sorted(files-tracked)}")
        return {"prefix": ARCHIVE_PREFIX, "regular_file_count": len(files),
                "lean_source_count": sum(path.endswith(".lean") for path in files),
                "matches_committed_file_list": True}

    def execute(self) -> None:
        self.git("validate_tag_ref", "check-ref-format", f"refs/tags/{self.args.tag}")
        branch = self.args.branch or self.git("discover_branch", "symbolic-ref", "--short", "HEAD").strip()
        self.git("validate_branch_ref", "check-ref-format", f"refs/heads/{branch}")
        self.record["release_branch"] = branch
        self.record["source_preflight"] = self.repository_state(self.repo, "source_preflight", branch)
        predecessor = self.git("source_predecessor_tag", "rev-parse",
                               f"refs/tags/{PREDECESSOR_TAG}^{{commit}}").strip()
        require(predecessor == PREDECESSOR_COMMIT,
                "Source Step-4 predecessor tag does not resolve to the expected release commit.")
        self.record["source_predecessor_tag"] = {"tag": PREDECESSOR_TAG, "commit": predecessor}
        self.record["source_manifest"] = self.manifest(self.repo, "source")
        tracked_raw = self.git("committed_file_list", "ls-tree", "-r", "--name-only", "-z", self.args.commit)
        tracked = set(filter(None, tracked_raw.split("\0")))
        self.release.parent.mkdir(parents=True, exist_ok=True)
        self.release.mkdir()  # Atomic refusal to reuse an existing release directory.
        self.release_created = True
        self.git("create_source_archive", "archive", "--format=tar.gz", f"--prefix={ARCHIVE_PREFIX}",
                 f"--output={self.archive}", self.args.commit)
        self.git("create_git_bundle", "bundle", "create", str(self.bundle), "--all")
        self.record["bundle_reference_scope"] = "All refs in the isolated Step-5 release repository, including predecessor release tags."
        self.record["archive_contents"] = self.inspect_archive(tracked)
        self.git("verify_git_bundle", "bundle", "verify", str(self.bundle))
        self.record["bundle_verification_passed"] = True
        temporary = Path(self.run("create_fresh_recovery_directory",
            ["mktemp", "-d", "/tmp/exp003_step5_delivery_verify.XXXXXX"]).strip())
        require(temporary.is_dir() and temporary.parent == Path("/tmp")
                and temporary.name.startswith("exp003_step5_delivery_verify."),
                "Fresh recovery directory did not have the expected path.")
        self.record["retained_recovery_directory"] = str(temporary)
        extracted = temporary / "archive"
        extracted.mkdir()
        self.run("fresh_archive_extraction", ["tar", "--extract", "--gzip", "--file", str(self.archive),
            "--directory", str(extracted), "--no-same-owner", "--no-same-permissions"])
        self.record["extracted_manifest"] = self.manifest(extracted / "NDEA_Evolve", "extracted")
        recovered = temporary / "bundle_clone"
        self.run("fresh_bundle_clone", ["git", "clone", "--branch", branch,
                 str(self.bundle), str(recovered)])
        self.record["recovered_bundle_state"] = self.repository_state(recovered, "recovered_bundle", branch)
        require(self.record["recovered_bundle_state"] == self.record["source_preflight"],
                "Recovered bundle does not preserve the original branch and tag object identity.")
        recovered_predecessor = self.git("recovered_predecessor_tag", "rev-parse",
            f"refs/tags/{PREDECESSOR_TAG}^{{commit}}", repo=recovered).strip()
        require(recovered_predecessor == PREDECESSOR_COMMIT,
                "Recovered bundle did not preserve the pinned Step-4 release tag.")
        self.record["recovered_predecessor_tag"] = {
            "tag": PREDECESSOR_TAG, "commit": recovered_predecessor, "verified": True}
        self.record["recovered_manifest"] = self.manifest(recovered, "recovered_bundle")
        self.record["source_postflight"] = self.repository_state(self.repo, "source_postflight", branch)
        require(self.record["source_preflight"] == self.record["source_postflight"],
                "Source repository identity changed during packaging.")
        self.record["artifacts"] = {
            "source_archive": {"path": str(self.archive), "sha256": sha256(self.archive),
                               "size_bytes": self.archive.stat().st_size},
            "git_bundle": {"path": str(self.bundle), "sha256": sha256(self.bundle),
                           "size_bytes": self.bundle.stat().st_size},
        }

    def finish(self) -> int:
        code = 0
        try:
            self.execute()
            self.record["passed"] = True
        except (OSError, RuntimeError, ValueError, tarfile.TarError) as error:
            code = 1
            self.record.update({"passed": False, "error": repr(error)})
        finally:
            self.record["end_utc"] = utc_now()
            if self.release_created:
                with self.receipt.open("x", encoding="utf-8") as stream:
                    json.dump(self.record, stream, indent=2)
                    stream.write("\n")
        print(json.dumps({"passed": self.record.get("passed", False),
            "error": self.record.get("error"),
            "receipt": str(self.receipt) if self.receipt.is_file() else None,
            "artifacts": self.record.get("artifacts", {}),
            "retained_recovery_directory": self.record.get("retained_recovery_directory")}, indent=2))
        return code


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--commit", required=True)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--branch")
    parser.add_argument("--release-dir", type=Path, default=DEFAULT_RELEASE)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--require-manifest", action="store_true",
                        help="Fail instead of reporting absent FINAL_SHA256SUMS; recommended for final release.")
    try:
        code = Delivery(parser.parse_args()).finish()
    except (OSError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        code = 1
    raise SystemExit(code)


if __name__ == "__main__":
    main()
