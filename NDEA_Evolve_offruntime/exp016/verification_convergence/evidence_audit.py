#!/usr/bin/env python3
"""Evidence integrity check, not a proof checker or independent Lean kernel."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
INITIAL = ['sampledInitialState_sub', 'initialCutoffDifference_coefficientNorm_sum',
           'synth_norm_le_coefficientSum', 'synth_spatialL2_le_coefficientSum',
           'synth_initialCutoff_spatialL2_le_tail', 'sampledInitialCutoff_weighted_norm_le_tail',
           'solution_initialCutoff_spatialL2_le_tail', 'sampledCayley_initialCutoff_error_transfer']
TIME_ONE = ['tendsto_zero_of_uniform_approximation',
            'scheduledCayley_potentialCutoff_error_tendsto_zero',
            'scheduledCayley_baseline_timeOne_error_tendsto_zero']
HORIZON = ['horizonGridError_nonneg', 'horizonGridError_le_iff',
           'horizonGridError_eq_max_at_nk', 'horizonGridError_doubleCutoff_tendsto_zero',
           'horizonGridError_initialCutoff_transfer', 'horizonGridError_potentialCutoff_transfer',
           'horizonGridError_potentialCutoff_tendsto_zero', 'horizonGridError_tendsto_zero']
CONTRACTS = ['Verification.time_one_spec', 'Verification.finite_horizon_spec',
             'Verification.initial_error_in_max', 'Verification.endpoint_error_in_max']
EXPECTED = ['NDEAEvolve.Exp016.' + x for x in INITIAL + TIME_ONE + HORIZON + CONTRACTS]
CONTROL_NAMES = {'false_statement_rejected', 'sorry_axiom_rejected', 'custom_axiom_rejected',
                 'missing_module_rejected'}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_file(root: Path, name: str) -> Path:
    path = Path(name)
    require(not path.is_absolute() and '..' not in path.parts, 'Unsafe evidence path')
    result = root / path
    require(result.is_file() and not result.is_symlink(), 'Missing or linked evidence: ' + name)
    require(root.resolve() in result.resolve().parents, 'Escaping evidence path')
    return result


def parse_axioms(text: str, expected: list[str]) -> dict[str, list[str]]:
    # Full, line-anchored names. Missing, duplicate or suffix-spoofed reports fail.
    found: dict[str, list[str]] = {}
    pattern = re.compile(r"^'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$", re.M)
    for match in pattern.finditer(text):
        name = match.group(1)
        if name not in expected:
            continue
        require(name not in found, 'Duplicate axiom report: ' + name)
        values = [x.strip() for x in (match.group(2) or '').split(',') if x.strip()]
        require(set(values) <= ALLOWED, 'Disallowed axioms: ' + name + ': ' + repr(values))
        found[name] = values
    require(set(found) == set(expected), 'Missing axiom reports: ' + repr(sorted(set(expected) - set(found))))
    return found


def audit(repo: Path, out: Path) -> dict:
    repo, out = repo.resolve(), out.resolve()
    manifest = json.loads(safe_file(out, 'EVIDENCE_MANIFEST.json').read_text())
    files = manifest['files']
    require(isinstance(files, dict) and len(files) > 10, 'Evidence manifest is incomplete')
    for name, value in files.items():
        require(digest(safe_file(out, name)) == value, 'Evidence hash mismatch: ' + name)
    needed = {'plan.json', 'compiled.json', 'result.json', 'verification.json',
              'target-axioms.log', 'kernel-replay.log', 'kernel-replay.json',
              'controls.json', 'contract.log', 'sources/VerificationContracts.lean',
              'olean/VerificationContracts.olean'}
    require(needed <= set(files), 'Required evidence omitted from manifest')
    plan = json.loads(safe_file(out, 'plan.json').read_text())
    result = json.loads(safe_file(out, 'result.json').read_text())
    compiled = json.loads(safe_file(out, 'compiled.json').read_text())
    verification = json.loads(safe_file(out, 'verification.json').read_text())
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    require(head == plan['commit'] == verification['commit'], 'Commit mismatch')
    require(result['status'] == 'TARGET_COMPILE_AND_AXIOM_AUDIT_PASS', 'Target compilation did not pass')
    require(verification['status'] == 'SCOPED_CHECKS_PASS', 'Additional checks did not pass')
    require(verification.get('independent_kernel') is False, 'Unsupported independent-kernel claim')
    require(verification.get('exp016_sealed') is False, 'Unsupported sealing claim')
    require(compiled.get('complete') is True, 'Compilation incomplete')
    modules = compiled['modules']
    require(len(modules) == len(plan['sources']) and len(modules) > 80, 'Incomplete source closure')
    require(modules[-1]['module'] == 'UniformGridTimeConvergence', 'Wrong target')
    require(len({x['module'] for x in modules}) == len(modules), 'Duplicate modules')
    for index, (source, record) in enumerate(zip(plan['sources'], modules)):
        for key in ('module', 'path', 'sha256'):
            require(source[key] == record[key], 'Compile record does not match plan')
        path = safe_file(repo, source['path'])
        committed = subprocess.check_output(['git', '-C', str(repo), 'show', head + ':' + source['path']])
        require(hashlib.sha256(committed).hexdigest() == source['sha256'] == digest(path), 'Source differs from committed bytes')
        staged = 'sources/' + source['module'].replace('.', '/') + '.lean'
        obj = 'olean/' + source['module'].replace('.', '/') + '.olean'
        log = f"{index:03}_{source['module']}.log"
        require({staged, obj, log} <= set(files), 'Module payload omitted')
        require(digest(safe_file(out, staged)) == source['sha256'], 'Staged source mismatch')
        require(digest(safe_file(out, obj)) == record['olean_sha256'], 'Object mismatch')
        require(digest(safe_file(out, log)) == record['log_sha256'], 'Compiler log mismatch')
        command = record['command']
        require('-o' in command and command[-1].endswith('/' + staged), 'Wrong compilation command')
    for pin, value in plan['pins'].items():
        require(digest(safe_file(repo, pin)) == value, 'Dependency pin changed')
    reports = parse_axioms(safe_file(out, 'target-axioms.log').read_text(), EXPECTED)
    replay = json.loads(safe_file(out, 'kernel-replay.json').read_text())
    require(replay['exit_code'] == 0, 'Kernel replay failed')
    require(replay['command'][-3:] == ['--fresh', '--verbose', 'VerificationContracts'], 'Wrong replay target or mode')
    require('replaying VerificationContracts with --fresh' in safe_file(out, 'kernel-replay.log').read_text(), 'Replay marker missing')
    require(replay['log_sha256'] == digest(safe_file(out, 'kernel-replay.log')), 'Replay log mismatch')
    controls = json.loads(safe_file(out, 'controls.json').read_text())
    require(set(controls) == CONTROL_NAMES, 'Incomplete negative controls')
    for name, control in controls.items():
        require(control['passed'] is True, 'Control failed: ' + name)
        require(control['log'] in files and digest(safe_file(out, control['log'])) == control['log_sha256'], 'Control log mismatch')
    for name in ('false_statement_rejected', 'missing_module_rejected'):
        require(controls[name]['exit_code'] not in (0, 124), 'Failure control did not reject normally')
    for name in ('sorry_axiom_rejected', 'custom_axiom_rejected'):
        require(controls[name]['exit_code'] == 0, 'Axiom control never compiled')
        try:
            parse_axioms(safe_file(out, controls[name]['log']).read_text(), [controls[name]['declaration']])
        except ValueError as exc:
            require('Disallowed axioms' in str(exc), 'Control was rejected for the wrong reason')
        else:
            raise ValueError('Unsafe axiom accepted by audit')
    return {'status': 'EVIDENCE_AUDIT_PASS', 'commit': head, 'project_modules': len(modules),
            'audited_declarations': len(reports), 'manifest_sha256': digest(out / 'EVIDENCE_MANIFEST.json'),
            'independent_kernel': False, 'exp016_sealed': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.repo, args.output)
    destination = args.output / 'EVIDENCE_AUDIT.json'
    require(not destination.exists(), 'Refusing to overwrite previous evidence audit')
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
