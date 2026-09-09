#!/usr/bin/env python3
"""Opt-in network bootstrap for the separate, offline Exp005 verifier.

This helper never builds the NDEA root project or verifies a mathematical proof.
All generated files, the downloaded Lean distribution, and the package/cache
trees live in a NEW directory below /content.  The optional Lake cache-tool
build is not claimed to have strictly one Lean child process at a time.
Requires Linux x86_64, Python with tarfile.data_filter, Git, curl, and libzstd.
"""

from __future__ import annotations

import argparse
import ctypes
import ctypes.util
import datetime as dt
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import signal
import subprocess
import sys
import tarfile
import time

sys.dont_write_bytecode = True

LEAN_COMMIT = "68218e876d2a38b1985b8590fff244a83c321783"
LOCK_SHA = "8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158"
TOOLCHAIN_SHA = "efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee"
LEAN_DIR = "lean-4.31.0-linux"
LEAN_URL = ("https://github.com/leanprover/lean4/releases/download/v4.31.0/"
            "lean-4.31.0-linux.tar.zst")
ROOTS = (
    "Mathlib.Algebra.BigOperators.Group.Finset.Basic",
    "Mathlib.Analysis.CStarAlgebra.Matrix",
    "Mathlib.Analysis.Normed.Algebra.Exponential",
    "Mathlib.Analysis.Normed.Group.Continuity",
    "Mathlib.Analysis.SpecificLimits.Basic",
    "Mathlib.Analysis.SpecificLimits.Normed",
    "Mathlib.LinearAlgebra.Matrix.Hermitian",
    "Mathlib.LinearAlgebra.Matrix.PosDef",
    "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.FinCases", "Mathlib.Tactic.GCongr",
    "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Module", "Mathlib.Tactic.NoncommRing",
    "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Positivity", "Mathlib.Tactic.Ring",
)
WRAPPER = '''name = "NDEA_Evolve"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.31.0"
'''


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def decompress_zstd(source: Path, target: Path) -> None:
    """Use the host's decoder library, without apt or a Python package install."""
    library = ctypes.util.find_library("zstd")
    require(library is not None, "System libzstd was not found; no files were installed globally")
    lib = ctypes.CDLL(library)

    class Buffer(ctypes.Structure):
        _fields_ = [("data", ctypes.c_void_p), ("size", ctypes.c_size_t),
                    ("pos", ctypes.c_size_t)]

    lib.ZSTD_createDStream.restype = ctypes.c_void_p
    lib.ZSTD_freeDStream.argtypes = [ctypes.c_void_p]
    lib.ZSTD_freeDStream.restype = ctypes.c_size_t
    lib.ZSTD_initDStream.argtypes = [ctypes.c_void_p]
    lib.ZSTD_initDStream.restype = ctypes.c_size_t
    lib.ZSTD_decompressStream.argtypes = [ctypes.c_void_p, ctypes.POINTER(Buffer),
                                        ctypes.POINTER(Buffer)]
    lib.ZSTD_decompressStream.restype = ctypes.c_size_t
    lib.ZSTD_isError.argtypes = [ctypes.c_size_t]
    lib.ZSTD_isError.restype = ctypes.c_uint
    lib.ZSTD_getErrorName.argtypes = [ctypes.c_size_t]
    lib.ZSTD_getErrorName.restype = ctypes.c_char_p

    def checked(value: int) -> int:
        require(not lib.ZSTD_isError(value),
                "zstd error: " + lib.ZSTD_getErrorName(value).decode())
        return value

    decoder = lib.ZSTD_createDStream()
    require(bool(decoder), "Could not allocate zstd decoder")
    total = 0
    remaining = 1
    try:
        checked(lib.ZSTD_initDStream(decoder))
        output_bytes = ctypes.create_string_buffer(1024 * 1024)
        with source.open("rb") as incoming, target.open("xb") as outgoing:
            for chunk in iter(lambda: incoming.read(1024 * 1024), b""):
                input_bytes = ctypes.create_string_buffer(chunk)
                input_buffer = Buffer(ctypes.cast(input_bytes, ctypes.c_void_p), len(chunk), 0)
                while True:
                    output_buffer = Buffer(ctypes.cast(output_bytes, ctypes.c_void_p),
                                           len(output_bytes), 0)
                    before = input_buffer.pos
                    remaining = checked(lib.ZSTD_decompressStream(
                        decoder, ctypes.byref(output_buffer), ctypes.byref(input_buffer)))
                    if input_buffer.pos == before and output_buffer.pos == 0:
                        require(input_buffer.pos == input_buffer.size,
                                "zstd decoder made no progress with unconsumed input")
                        break
                    total += output_buffer.pos
                    require(total <= 16 * 1024**3, "Lean archive exceeded 16 GiB unpacked limit")
                    outgoing.write(output_bytes.raw[:output_buffer.pos])
                    if (input_buffer.pos == input_buffer.size
                            and output_buffer.pos < output_buffer.size):
                        break
        require(remaining == 0, "Incomplete zstd archive")
    finally:
        lib.ZSTD_freeDStream(decoder)
    print(f"Decompressed {total} bytes using {library}", flush=True)


def unpack_toolchain(source: Path, target: Path) -> None:
    require(hasattr(tarfile, "data_filter"), "Python tarfile.data_filter is required")
    require(target.is_dir() and not (target / LEAN_DIR).exists(), "Toolchain target is not fresh")
    seen: set[str] = set()
    total = 0
    with tarfile.open(source, "r:") as archive:
        for member in archive:
            name = member.name.rstrip("/")
            path = PurePosixPath(name)
            require(path.parts and path.parts[0] == LEAN_DIR and not path.is_absolute()
                    and ".." not in path.parts and "\\" not in name,
                    f"Unsafe toolchain member: {name!r}")
            require(name not in seen, f"Duplicate toolchain archive path: {name}")
            seen.add(name)
            require(member.isfile() or member.isdir() or member.issym() or member.islnk(),
                    f"Unsupported toolchain archive member: {name}")
            total += member.size
            require(total <= 16 * 1024**3, "Toolchain member sizes exceeded 16 GiB")
            # This rejects escaping link targets and symlink-parent escapes while
            # retaining the distribution's legitimate relative library symlinks.
            archive.extract(member, target, filter="data")
    require((target / LEAN_DIR / "bin/lean").is_file(), "Lean binary absent after extraction")
    print(f"Safely extracted {len(seen)} members", flush=True)


class Bootstrap:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.source = args.source.resolve(strict=True)
        self.deps = args.deps.absolute()
        require(args.allow_network, "Network bootstrap requires --allow-network")
        require(platform.system() == "Linux" and platform.machine() == "x86_64",
                "This bootstrap is specifically for Linux x86_64 (Colab)")
        require(hasattr(tarfile, "data_filter"), "Python tarfile.data_filter is required")
        require(ctypes.util.find_library("zstd") is not None, "System libzstd is required")
        require(shutil.which("curl") is not None and shutil.which("git") is not None,
                "curl and Git must already be installed")
        require(not self.deps.exists() and not self.deps.is_symlink(),
                "--deps must be a NEW directory; existing attempts are retained")
        require(self.deps.parent.resolve(strict=True) == Path("/content")
                and self.deps.name.startswith("exp005-"),
                "--deps must be a new /content/exp005-* directory")
        require(self.source != self.deps and self.deps not in self.source.parents,
                "Source and dependency output must not overlap")
        for name, expected in (("lake-manifest.json", LOCK_SHA), ("lean-toolchain", TOOLCHAIN_SHA)):
            path = self.source / name
            require(path.is_file() and not path.is_symlink() and sha256(path) == expected,
                    f"Source does not contain the frozen pinned {name}")
        self.deps.mkdir()
        for name in ("logs", "downloads", "toolchain", "tmp", "cache"):
            (self.deps / name).mkdir()
        self.env = dict(os.environ)
        for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_PACKAGE_URL_MAP"):
            self.env.pop(name, None)
        self.env["TMPDIR"] = str(self.deps / "tmp")
        self.env["MATHLIB_CACHE_DIR"] = str(self.deps / "cache")
        self.env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
        self.env["LEAN_NUM_THREADS"] = "1"
        self.env["GIT_TERMINAL_PROMPT"] = "0"
        self.report = {
            "started_utc": now(), "status": "running", "source": str(self.source),
            "deps": str(self.deps), "network_authorized": True,
            "qualification": "dependency bootstrap only; not a mathematical verification",
            "concurrency": "Commands are sequential; Lake cache-tool builds may spawn concurrent Lean children",
            "archive_trust": "Pinned official release HTTPS URL; archive SHA-256 recorded, compiler commit checked",
            "commands": [], "source_lock_sha256": LOCK_SHA,
            "source_toolchain_sha256": TOOLCHAIN_SHA,
        }
        self.save()

    def save(self) -> None:
        (self.deps / "BOOTSTRAP_REPORT.json").write_text(
            json.dumps(self.report, indent=2) + "\n", encoding="utf-8")

    def run(self, label: str, command: list[str], cwd: Path | None = None) -> str:
        log = self.deps / "logs" / f"{len(self.report['commands']) + 1:03d}_{label}.log"
        receipt = {"label": label, "command": command, "cwd": str(cwd or self.deps),
                   "log": str(log), "started_utc": now(), "timeout_seconds": self.args.timeout}
        self.report["commands"].append(receipt)
        self.save()
        print(f"START {label}; log={log}", flush=True)
        started = time.monotonic()
        process = None
        try:
            with log.open("xb") as stream:
                process = subprocess.Popen(command, cwd=cwd or self.deps, env=self.env,
                                           stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                try:
                    receipt["exit_code"] = process.wait(timeout=self.args.timeout)
                except (subprocess.TimeoutExpired, KeyboardInterrupt):
                    receipt["interrupted_or_timed_out"] = True
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    receipt["exit_code"] = process.returncode
                    raise
        except BaseException as error:
            receipt["error"] = repr(error)
            raise
        finally:
            receipt["finished_utc"] = now()
            receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
            self.save()
        require(receipt["exit_code"] == 0, f"{label} failed; see {log}")
        print(f"PASS {label} ({receipt['elapsed_seconds']}s)", flush=True)
        with log.open("r", encoding="utf-8", errors="replace") as stream:
            return stream.read(128 * 1024)

    def verify_lock(self) -> None:
        for root in (self.source, self.deps):
            require(sha256(root / "lake-manifest.json") == LOCK_SHA,
                    f"Pinned manifest changed: {root}")
            require(sha256(root / "lean-toolchain") == TOOLCHAIN_SHA,
                    f"Pinned toolchain file changed: {root}")

    def package_state(self) -> list[dict]:
        entries = json.loads((self.deps / "lake-manifest.json").read_text())["packages"]
        result = []
        for package in entries:
            root = self.deps / ".lake/packages" / package["name"]
            revision = self.run("head_" + package["name"],
                                ["git", "rev-parse", "HEAD"], root).strip()
            changes = self.run("clean_" + package["name"],
                               ["git", "status", "--porcelain=v1", "--untracked-files=no"], root)
            require(revision == package["rev"] and not changes.strip(),
                    f"Wrong revision or tracked changes in {package['name']}")
            result.append({"name": package["name"], "revision": revision, "root": str(root)})
        require(len(result) == 9, "Expected all nine pinned packages")
        return result

    def execute(self) -> None:
        for name in ("lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(self.source / name, self.deps / name)
        (self.deps / "lakefile.toml").write_text(WRAPPER, encoding="utf-8")
        archive = self.deps / "downloads" / (LEAN_DIR + ".tar.zst")
        self.run("download_lean", ["curl", "--fail", "--location", "--retry", "2",
                 "--connect-timeout", "30", "--max-time", str(self.args.timeout),
                 "--proto", "=https", "--tlsv1.2", "--output", str(archive), LEAN_URL])
        self.report["lean_archive"] = {"url": LEAN_URL, "sha256": sha256(archive),
                                       "bytes": archive.stat().st_size}
        self.save()
        tar_path = self.deps / "downloads" / (LEAN_DIR + ".tar")
        self.run("decompress_lean", [sys.executable, str(Path(__file__).resolve()),
                                    "--internal-decompress", str(archive), str(tar_path)])
        self.run("extract_lean", [sys.executable, str(Path(__file__).resolve()),
                                 "--internal-extract", str(tar_path), str(self.deps / "toolchain")])
        binary_dir = self.deps / "toolchain" / LEAN_DIR / "bin"
        lean = binary_dir / "lean"
        lake = binary_dir / "lake"
        self.env["PATH"] = str(binary_dir) + os.pathsep + self.env.get("PATH", "")
        version = self.run("lean_version", [str(lean), "--version"])
        require("version 4.31.0," in version and LEAN_COMMIT in version and "Release" in version,
                "Downloaded compiler does not match the frozen release version/commit")
        require((binary_dir / "leantar").is_file(), "Bundled leantar is missing")
        self.report["compiler"] = {"lean": str(lean), "version": version.strip(),
                                   "sha256": sha256(lean)}
        self.save()
        # With an existing manifest this only materializes its locked revisions.
        # In particular, never use lake update, --update, or the root default build.
        self.run("materialize_locked_packages", [str(lake), "env", "true"])
        self.verify_lock()
        before = self.package_state()
        self.report["packages_before_cache"] = before
        self.save()
        self.run("get_narrow_mathlib_cache", [str(lake), "exe", "cache", "get", *ROOTS])
        self.verify_lock()
        after = self.package_state()
        require(before == after, "Package state changed during cache retrieval")
        self.report["packages_after_cache"] = after
        self.report["offline_verifier_arguments"] = {
            "--packages": str(self.deps / ".lake/packages"), "--lean": str(lean)}
        self.report["status"] = "passed"
        self.report["finished_utc"] = now()
        self.save()
        print(json.dumps(self.report["offline_verifier_arguments"], indent=2), flush=True)
        print("BOOTSTRAP PASS — run the separate offline proof verifier next.", flush=True)


def main() -> int:
    if len(sys.argv) == 4 and sys.argv[1] == "--internal-decompress":
        decompress_zstd(Path(sys.argv[2]), Path(sys.argv[3]))
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "--internal-extract":
        unpack_toolchain(Path(sys.argv[2]), Path(sys.argv[3]))
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True,
                        help="Already integrity-verified extracted release source (read-only)")
    parser.add_argument("--deps", type=Path, required=True,
                        help="NEW /content/exp005-* directory, e.g. /content/exp005-deps")
    parser.add_argument("--allow-network", action="store_true",
                        help="Authorize official Lean/Git package/cache downloads")
    parser.add_argument("--timeout", type=int, default=900, help="Per-command timeout in seconds")
    args = parser.parse_args()
    require(1 <= args.timeout <= 3600, "Timeout must be between 1 and 3600 seconds")
    job = None
    try:
        job = Bootstrap(args)
        job.execute()
        return 0
    except BaseException as error:
        if job is not None:
            job.report["status"] = "failed"
            job.report["error"] = repr(error)
            job.report["finished_utc"] = now()
            job.save()
        print(f"BOOTSTRAP FAILED: {error}", file=sys.stderr, flush=True)
        return 130 if isinstance(error, KeyboardInterrupt) else 1


if __name__ == "__main__":
    raise SystemExit(main())
