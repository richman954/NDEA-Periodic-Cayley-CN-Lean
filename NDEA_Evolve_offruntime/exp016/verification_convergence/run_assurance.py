#!/usr/bin/env python3
"""Additive checks of unchanged Exp016 sources; no acceptance or sealing writes."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
import evidence_audit as evidence

HERE = Path(__file__).resolve().parent
ROOT = 'NDEA_Evolve_offruntime/exp016'
BLOBS = {
    'InitialErrorTransfer': '32e149dda788b429d77db9fe15ef4cd07543cde3',
    'BaselineTimeOneConvergence': 'f25d88c7d7c2bb34180113ff2bf35e475b5c4f43',
    'UniformGridTimeConvergence': '3888607003336797ff29c7d70c668ec21137a0d6',
}


def load_builder(repo: Path):
    path = repo / ROOT / 'verification_initial_error/check_initial_error_transfer.py'
    spec = importlib.util.spec_from_file_location('original_builder', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.TARGET = 'UniformGridTimeConvergence'
    module.SOURCE = ROOT + '/lean/UniformGridTimeConvergence.lean'
    module.BASELINE_BLOB = BLOBS[module.TARGET]
    # The retained builder's generated audit imports InitialErrorTransfer literally.
    # Keep its eight-declaration audit intact; target-axioms below separately
    # imports VerificationContracts and checks all 23 convergence declarations.
    evidence.require(tuple(module.DECLARATIONS) == tuple(evidence.INITIAL),
                     'Retained builder audit changed; review before adapting')
    return module


def save(out: Path, name: str, value: dict) -> None:
    (out / name).write_text(json.dumps(value, indent=2) + '\n')


def validate_inputs(repo: Path, builder) -> None:
    for name, expected in BLOBS.items():
        data = (repo / ROOT / 'lean' / (name + '.lean')).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        evidence.require(actual == expected, 'Reviewed target bytes changed: ' + name)
    for item in builder.resolve(repo):
        code = builder.code_only((repo / item['path']).read_text())
        evidence.require(not re.search(r'\b(unsafe|native_decide|run_tac|elab|initialize|macro)\b', code),
                         'Executable proof-environment extension requires review: ' + item['path'])


def command(out: Path, label: str, args: list[str], cwd: Path, env: dict,
            timeout: int = 900) -> dict:
    log = out / (label + '.log')
    start = datetime.now(timezone.utc).isoformat()
    with log.open('w') as stream:
        try:
            proc = subprocess.run(args, cwd=cwd, env=env, stdout=stream,
                                  stderr=subprocess.STDOUT, timeout=timeout)
            code = proc.returncode
        except subprocess.TimeoutExpired:
            code = 124
    receipt = {'command': args, 'exit_code': code, 'log': log.name,
               'log_sha256': evidence.digest(log), 'started_utc': start,
               'finished_utc': datetime.now(timezone.utc).isoformat()}
    save(out, label + '.json', receipt)
    print(label, 'exit', code, flush=True)
    print(log.read_text(errors='replace'), end='', flush=True)
    return receipt


def run(repo: Path, out: Path, builder) -> None:
    validate_inputs(repo, builder)
    builder.run(repo, out)
    deps = out / 'deps'
    lean = Path(subprocess.check_output(['elan', 'which', 'lean'], cwd=deps, text=True).strip()).resolve()
    checker = lean.with_name('leanchecker')
    evidence.require(checker.is_file(), 'Pinned toolchain has no leanchecker')
    lock = json.loads((deps / 'lake-manifest.json').read_text())
    paths = [out / 'olean'] + [deps / '.lake/packages' / p['name'] / '.lake/build/lib/lean' for p in lock['packages']]
    paths += [lean.parent.parent / 'lib/lean']
    env = dict(os.environ)
    for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
        env.pop(name, None)
    env.update(LEAN_PATH=os.pathsep.join(map(str, paths)), LEAN_NUM_THREADS='1')
    source = out / 'sources/VerificationContracts.lean'
    shutil.copyfile(HERE / source.name, source)
    spec_check = command(out, 'contract', [str(lean), '-j', '1', '-R', str(out / 'sources'),
                         '-o', str(out / 'olean/VerificationContracts.olean'), str(source)], out / 'sources', env)
    evidence.require(spec_check['exit_code'] == 0, 'Explicit theorem contracts did not compile')
    audit_source = out / 'sources/TargetAxioms.lean'
    audit_source.write_text('import VerificationContracts\n' + '\n'.join('#print axioms ' + d for d in evidence.EXPECTED) + '\n')
    checked = command(out, 'target-axioms', [str(lean), '-j', '1', str(audit_source)], out / 'sources', env)
    evidence.require(checked['exit_code'] == 0, 'Target axiom report failed')
    evidence.parse_axioms((out / 'target-axioms.log').read_text(), evidence.EXPECTED)
    negative = out / 'negative-controls'
    negative.mkdir(exist_ok=False)
    fixtures = [
        ('false_statement_rejected', 'import Mathlib\nexample : False := by trivial\n', None),
        ('sorry_axiom_rejected', 'import Mathlib\ntheorem AssuranceSorry : False := by sorry\n#print axioms AssuranceSorry\n', 'AssuranceSorry'),
        ('custom_axiom_rejected', 'import Mathlib\naxiom AssuranceInjected : False\ntheorem AssuranceBad : False := AssuranceInjected\n#print axioms AssuranceBad\n', 'AssuranceBad'),
        ('missing_module_rejected', 'import AssuranceDefinitelyMissingModule\n', None),
    ]
    controls = {}
    for label, text, declaration in fixtures:
        path = negative / (label + '.lean')
        path.write_text(text)
        receipt = command(out, label, [str(lean), '-j', '1', str(path)], negative, env, 120)
        if declaration is None:
            evidence.require(receipt['exit_code'] not in (0, 124), 'Negative compile control failed: ' + label)
        else:
            evidence.require(receipt['exit_code'] == 0, 'Axiom control did not compile: ' + label)
            try:
                evidence.parse_axioms((out / receipt['log']).read_text(), [declaration])
            except ValueError as exc:
                evidence.require('Disallowed axioms' in str(exc), 'Wrong rejection reason: ' + str(exc))
            else:
                raise ValueError('Unsafe axiom passed: ' + label)
        controls[label] = {**receipt, 'passed': True, 'declaration': declaration}
    save(out, 'controls.json', controls)
    replay = command(out, 'kernel-replay', [str(checker), '--fresh', '--verbose', 'VerificationContracts'],
                     out / 'sources', env, 1200)
    evidence.require(replay['exit_code'] == 0, 'Fresh kernel replay failed or timed out')
    evidence.require('replaying VerificationContracts with --fresh' in (out / 'kernel-replay.log').read_text(),
                     'Fresh replay marker missing')
    plan = json.loads((out / 'plan.json').read_text())
    builder.unchanged(repo, plan)
    evidence.require(evidence.digest(source) == evidence.digest(HERE / source.name), 'Contract source changed')
    for package in lock['packages']:
        folder = deps / '.lake/packages' / package['name']
        evidence.require(builder.git(folder, 'rev-parse', 'HEAD') == package['rev'], 'Package revision changed')
        evidence.require(not builder.git(folder, 'status', '--porcelain', '--untracked-files=no'), 'Tracked dependency changed')
    binaries = {'lean': evidence.digest(lean), 'leanchecker': evidence.digest(checker)}
    evidence.require(binaries['lean'] == builder.LEAN_SHA256, 'Compiler changed during verification')
    for lib in sorted((lean.parent.parent / 'lib/lean').glob('*.so')):
        binaries[lib.name] = evidence.digest(lib)
    for path in HERE.iterdir():
        if path.is_file() and path.suffix in ('.py', '.lean', '.md'):
            folder = out / 'verification-tools'; folder.mkdir(exist_ok=True)
            shutil.copyfile(path, folder / path.name)
    save(out, 'verification.json', {'status': 'SCOPED_CHECKS_PASS', 'commit': plan['commit'],
         'run_id': os.environ.get('GITHUB_RUN_ID'), 'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
         'runner': os.environ.get('RUNNER_NAME'), 'binary_hashes': binaries,
         'external_package_revisions': {p['name']: p['rev'] for p in lock['packages']},
         'checked_declarations': evidence.EXPECTED, 'independent_kernel': False, 'exp016_sealed': False,
         'trust_limit': 'Same Lean kernel; cached external library artifacts; no independent mathematical reviewer.',
         'finished_utc': datetime.now(timezone.utc).isoformat()})
    files = {}
    for path in sorted(out.rglob('*')):
        relative = path.relative_to(out)
        if relative.parts[0] == 'deps' or not path.is_file():
            continue
        if path.name not in ('EVIDENCE_MANIFEST.json', 'EVIDENCE_AUDIT.json'):
            files[str(relative)] = evidence.digest(path)
    save(out, 'EVIDENCE_MANIFEST.json', {'files': files})
    print('SCOPED_CHECKS_PASS; evidence audit still required; Exp016 unsealed.', flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'run'])
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.output.resolve()
    evidence.require(out != repo and repo not in out.parents, 'Output must be outside checkout')
    if args.mode == 'prepare':
        evidence.require(not out.exists(), 'Refusing to overwrite previous output')
    else:
        evidence.require(not (out / 'verification.json').exists(), 'Refusing to overwrite a completed check')
    builder = load_builder(repo)
    try:
        validate_inputs(repo, builder)
        if args.mode == 'prepare':
            builder.prepare(repo, out)
        else:
            run(repo, out, builder)
    except Exception as exc:
        if out.is_dir():
            save(out, 'ASSURANCE_FAILURE.json', {'status': 'BLOCKED_OR_FAILED', 'error': str(exc)})
        print('BLOCKED_OR_FAILED:', exc, file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
