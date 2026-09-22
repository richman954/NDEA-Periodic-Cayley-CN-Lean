#!/usr/bin/env python3
import argparse
import json
import os
import subprocess
import tarfile
import hashlib
import sys
from datetime import datetime, timezone

def run_cmd(cmd):
    try:
        return subprocess.check_output(cmd, shell=True, stderr=subprocess.STDOUT).decode('utf-8').strip()
    except subprocess.CalledProcessError:
        return "UNKNOWN"

def get_hash(filepath):
    if not os.path.exists(filepath): return None
    h = hashlib.sha256()
    with open(filepath, 'rb') as f:
        while chunk := f.read(8192):
            h.update(chunk)
    return h.hexdigest()

def discover_active_experiment():
    task_state_path = "NDEA_Recovery/TASK_STATE.json"
    if os.path.exists(task_state_path):
        try:
            with open(task_state_path, 'r') as f:
                ts = json.load(f)
            return ts.get("current_state", {}).get("active_experiment", "exp016")
        except:
            pass
    return "exp016"

def get_lean_version():
    return run_cmd("lake --version")

def create_manifest(artifact_class):
    exp = discover_active_experiment()
    active_dir = f"NDEA_Evolve_offruntime/{exp}"

    if artifact_class == "qualified":
        task_state_path = "NDEA_Recovery/TASK_STATE.json"
        is_qualified = False
        if os.path.exists(task_state_path):
            with open(task_state_path, 'r') as f:
                ts = json.load(f)
                qual_text = ts.get("current_state", {}).get("qualification", "")
                if "unsealed" not in qual_text.lower() and "fully sealed" in qual_text.lower():
                    is_qualified = True
        if not is_qualified:
            print("WARNING: Insufficient evidence for 'qualified' class. Downgrading to 'pre-risk'.")
            artifact_class = "pre-risk"

    source_hashes = {}
    if os.path.exists(active_dir):
        for root, dirs, files in os.walk(active_dir):
            for f in files:
                if f.endswith('.lean'):
                    path = os.path.join(root, f)
                    source_hashes[path] = get_hash(path)

    manifest = {
        "schema_version": "1.0",
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "artifact_class": artifact_class,
        "source_repository": run_cmd("git config --get remote.origin.url"),
        "git_branch": run_cmd("git rev-parse --abbrev-ref HEAD"),
        "git_commit": run_cmd("git rev-parse HEAD"),
        "dirty_state": run_cmd("git status --porcelain"),
        "source_hashes": source_hashes,
        "lean_toolchain": get_lean_version(),
        "compiler_identity": get_hash(run_cmd("which lean")),
        "mathlib_revision": "pinned-via-lake",
        "platform_architecture": run_cmd("uname -m"),
        "originating_receipts": "NDEA_Recovery/TASK_STATE.json",
        "compatibility_requirements": {
            "lean_version": get_lean_version(),
            "arch": run_cmd("uname -m")
        },
        "exclusions": ["node_modules", "target", ".git"]
    }
    return manifest

def create(args):
    manifest = create_manifest(args.artifact_class)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    output_name = f"ndea_savepoint_{manifest['artifact_class']}_{timestamp}.tar.gz"
    outpath = os.path.join(args.output_dir, output_name)

    exp = discover_active_experiment()
    active_dir = f"NDEA_Evolve_offruntime/{exp}"

    os.makedirs(args.output_dir, exist_ok=True)

    files_to_add = []
    if os.path.exists(active_dir):
        files_to_add.append(active_dir)
    if os.path.exists("NDEA_Recovery"):
        files_to_add.append("NDEA_Recovery")
    if os.path.exists(".lake/build/lib"):
        files_to_add.append(".lake/build/lib")

    payload_hashes = {}

    with tarfile.open(outpath, "w:gz") as tar:
        with open("/tmp/manifest.json", "w") as f:
            json.dump(manifest, f, indent=2)
        tar.add("/tmp/manifest.json", arcname="manifest.json")
        payload_hashes["manifest.json"] = get_hash("/tmp/manifest.json")

        for p in files_to_add:
            for root, dirs, files in os.walk(p):
                for file in files:
                    fp = os.path.join(root, file)
                    tar.add(fp, arcname=fp)
                    payload_hashes[fp] = get_hash(fp)

        manifest["payload_hashes"] = payload_hashes
        with open("/tmp/manifest.json", "w") as f:
            json.dump(manifest, f, indent=2)

        tar.add("/tmp/manifest.json", arcname="manifest.json")

    print(f"Created artifact: {outpath}")
    print(f"Artifact SHA-256: {get_hash(outpath)}")
    sys.exit(0)

def inspect(args):
    with tarfile.open(args.archive, "r:gz") as tar:
        f = tar.extractfile("manifest.json")
        manifest = json.load(f)
        print(json.dumps(manifest, indent=2))
    sys.exit(0)

def do_verify(archive):
    with tarfile.open(archive, "r:gz") as tar:
        f = tar.extractfile("manifest.json")
        manifest = json.load(f)

        payload_hashes = manifest.get("payload_hashes", {})
        for member in tar.getmembers():
            if not member.isfile(): continue
            if member.name == "manifest.json": continue
            if member.name not in payload_hashes:
                print(f"FAIL: {member.name} not in manifest hashes")
                return False
            f = tar.extractfile(member)
            h = hashlib.sha256()
            while chunk := f.read(8192):
                h.update(chunk)
            if h.hexdigest() != payload_hashes[member.name]:
                print(f"FAIL: Hash mismatch for {member.name}")
                return False

    print("VERIFIED: All payload hashes match manifest.")
    return True

def verify(args):
    if do_verify(args.archive):
        sys.exit(0)
    else:
        sys.exit(1)

def restore(args):
    if not do_verify(args.archive):
        if not args.unsafe_override:
            print("Restore aborted due to verification failure.")
            sys.exit(1)
        else:
            print("WARNING: Unsafe override applied. Restoring unverified data.")

    with tarfile.open(args.archive, "r:gz") as tar:
        f = tar.extractfile("manifest.json")
        manifest = json.load(f)

        compat = manifest.get("compatibility_requirements", {})
        current_lean = get_lean_version()
        if compat.get("lean_version") != current_lean:
            print(f"INCOMPATIBLE: Manifest needs {compat.get('lean_version')} but found {current_lean}")
            if not args.unsafe_override:
                sys.exit(1)
            else:
                print("WARNING: Unsafe override applied for toolchain mismatch.")

        os.makedirs(args.target_dir, exist_ok=True)
        def is_within_directory(directory, target):
            abs_directory = os.path.abspath(directory)
            abs_target = os.path.abspath(target)
            prefix = os.path.commonprefix([abs_directory, abs_target])
            return prefix == abs_directory

        for member in tar.getmembers():
            member_path = os.path.join(args.target_dir, member.name)
            if not is_within_directory(args.target_dir, member_path):
                raise Exception("Attempted Path Traversal in Tar File")

        tar.extractall(args.target_dir)
        print(f"Restored save point to {args.target_dir}")
        print("Note: Restored artifacts are acceleration/recovery inputs and do not substitute for fresh independent qualification.")
        sys.exit(0)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="NDEA Artifact Save Point CLI")
    subparsers = parser.add_subparsers(dest="command", required=True)

    parser_create = subparsers.add_parser("create")
    parser_create.add_argument("artifact_class", choices=["development", "pre-risk", "qualified"])
    parser_create.add_argument("--output_dir", default="/tmp")

    parser_inspect = subparsers.add_parser("inspect")
    parser_inspect.add_argument("archive")

    parser_verify = subparsers.add_parser("verify")
    parser_verify.add_argument("archive")

    parser_restore = subparsers.add_parser("restore")
    parser_restore.add_argument("archive")
    parser_restore.add_argument("target_dir")
    parser_restore.add_argument("--unsafe-override", action="store_true")

    args = parser.parse_args()
    if args.command == "create": create(args)
    elif args.command == "inspect": inspect(args)
    elif args.command == "verify": verify(args)
    elif args.command == "restore": restore(args)
