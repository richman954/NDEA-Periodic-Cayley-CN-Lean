"""Bind replay subprocesses to the verified compiler; never set an elan default."""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import shutil
from typing import Mapping

PINNED_TOOLCHAIN = 'leanprover/lean4:v4.31.0'


def pinned_replay_environment(lean: Path, inherited: Mapping[str, str],
                              expected_sha256: str, toolchain: str) -> dict[str, str]:
    """Return a child-only environment using the already hash-checked Lean binary.

    Lean 4.31.0's findSysroot invokes `lean --print-prefix` through PATH.
    The scratch sources directory intentionally has no lean-toolchain file.
    Put the real pinned binary before elan proxies, override stale toolchain
    selection, and discard inherited source/sysroot overrides. LEAN_PATH is
    retained because the caller has already built its isolated import path.
    """
    if toolchain != PINNED_TOOLCHAIN:
        raise ValueError('Unexpected replay toolchain pin')
    lean = lean.resolve(strict=True)
    if lean.name != 'lean' or not lean.is_file() or not os.access(lean, os.X_OK):
        raise ValueError('Replay compiler is not an executable lean binary')
    if hashlib.sha256(lean.read_bytes()).hexdigest() != expected_sha256:
        raise ValueError('Replay compiler SHA-256 mismatch')
    env = dict(inherited)
    for name in ('LEAN_SYSROOT', 'LEAN_SRC_PATH'):
        env.pop(name, None)
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', os.defpath)
    env['ELAN_TOOLCHAIN'] = toolchain
    selected = shutil.which('lean', path=env['PATH'])
    if selected is None or Path(selected).resolve(strict=True) != lean:
        raise ValueError('Replay PATH does not select the pinned compiler')
    return env
