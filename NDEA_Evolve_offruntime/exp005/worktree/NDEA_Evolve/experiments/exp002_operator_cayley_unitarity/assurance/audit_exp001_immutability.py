#!/usr/bin/env python3
"""Fail-closed post-check of immutable Experiment 001 sentinels."""

from __future__ import annotations

import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUTPUT = HERE / "final_exp001_immutability.json"
COMMIT = "a88a3fb141d63b460a5d19d2e33f2a76f05101f2"
TAG = "exp001-fourier-stability-verified-final-20260905"
EXPECTED_TAG_OBJECT = "6526b9414207c3becc2b01db7ebce1f5ee482494"
FILES = {
    "/home/richman954/NDEA_Evolve_offruntime/exp001/final/NDEA_Evolve_exp001_final_evidence.tar.gz":
        "131a89fc12a0f7ae71011c50af7e359fd9c3f8ebbb974c982f77f9309c4127aa",
    "/home/richman954/NDEA_Evolve_offruntime/exp001/final/NDEA_Evolve_exp001_final.bundle":
        "10dc27fd1046a419358a92565fe59e1ae40414c9c5692c9afd3b016bce7540c1",
    "/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/Exp001_Assurance_Hardening_v2_evidence.tar.gz":
        "3f460ecd7f88de93bc403ae2371601686a083dcba911b05f6784464114f719be",
    "/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/Exp001_Assurance_Hardening_v2.bundle":
        "fb8cb79fc574522fdb142b348b50637087c75e582f437ed19531260546ad5257",
    "/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/local_v2_delivery_verification.json":
        "62a02d08b0dcb873ffba905622803e2e27ce7dd6695bf8a4f426391d8e466556",
}
OBJECTS = {
    f"{COMMIT}:NDEAEvolve/Experiments/Exp001":
        "c3f74e21f1882e0aa73fbe71a985aca9f2794cab",
    f"{COMMIT}:experiments/exp001_fourier_stability":
        "0e6e91fa06a526d654d040b182abf0b1435d7f07",
    f"{COMMIT}:lean-toolchain": "18640c8b066b182147f324d3aefd8ee48ee45238",
    f"{COMMIT}:lakefile.toml": "a62e22edd1ccbf3eda0514bc3c4c8901c29411b5",
    f"{COMMIT}:lake-manifest.json": "9d7e58f96268bd595a19b05dc0da88b35edaa2b6",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def rev_parse(spec: str) -> str:
    run = subprocess.run(
        ["git", "rev-parse", spec], cwd=REPO, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if run.returncode != 0:
        raise RuntimeError(f"git rev-parse failed for {spec!r}: {run.stderr.strip()}")
    return run.stdout.strip()


def main() -> int:
    if OUTPUT.exists():
        raise SystemExit(f"refusing to overwrite existing result: {OUTPUT}")
    file_rows = []
    passed = True
    for raw, expected in FILES.items():
        path = Path(raw)
        regular = path.is_file() and not path.is_symlink()
        actual = sha256(path) if regular else None
        ok = regular and actual == expected
        passed &= ok
        file_rows.append({
            "path": raw, "expected_sha256": expected, "actual_sha256": actual,
            "regular_nonlink": regular, "status": "PASS" if ok else "FAIL",
        })
    actual_tag = rev_parse(f"refs/tags/{TAG}")
    actual_commit = rev_parse(f"refs/tags/{TAG}^{{commit}}")
    tag_ok = actual_tag == EXPECTED_TAG_OBJECT and actual_commit == COMMIT
    passed &= tag_ok
    object_rows = []
    for spec, expected in OBJECTS.items():
        actual = rev_parse(spec)
        ok = actual == expected
        passed &= ok
        object_rows.append({
            "spec": spec, "expected": expected, "actual": actual,
            "status": "PASS" if ok else "FAIL",
        })
    result = {
        "schema": "ndea.exp002.exp001_post_immutability_audit.v1",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "status": "PASS" if passed else "FAIL",
        "external_review": "PENDING",
        "files": file_rows,
        "tag": {
            "name": TAG, "expected_tag_object": EXPECTED_TAG_OBJECT,
            "actual_tag_object": actual_tag, "expected_commit": COMMIT,
            "actual_commit": actual_commit, "status": "PASS" if tag_ok else "FAIL",
        },
        "git_objects": object_rows,
    }
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
