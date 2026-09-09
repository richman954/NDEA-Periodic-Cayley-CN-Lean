"""Prepare direct Colab commands and strictly accept their downloaded module results.

This helper performs no network calls and never launches Lean itself. Network
commands remain direct, reviewable Colab CLI operations under existing approvals.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import shlex
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROJECT = ROOT.parent
COLAB = '/home/richman954/.local/bin/colab'
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
HELPERS = {
    'prepare_check.py': '377e390980bab7d34556217db82129c583cc4935812785c36681f4ad814535e6',
    'run_module.py': '6afc87c76470de47823cc7caff2b4b8ffd2948c53f0c947f81891bca3382d2bf',
    'accept_result.py': '0e9c05415148b25e2444fa17a30482968b43aea0125fcc0f8d15d807e901140d',
}
sha = lambda data: hashlib.sha256(data).hexdigest()
digest = lambda path: sha(path.read_bytes())


def save_new(path, value):
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def verify_helpers():
    for name, expected in HELPERS.items():
        assert digest(HERE / name) == expected, 'Reviewed helper changed: ' + name


def command(argv):
    return shlex.join(map(str, argv))


def prepare(module, runtime_record):
    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', module)
    source = ROOT / 'lean' / (module + '.lean')
    data = source.read_bytes()
    runtime_path = (ROOT / runtime_record).resolve()
    assert runtime_path.parent == ROOT / 'evidence' and runtime_path.suffix == '.json'
    runtime = json.loads(runtime_path.read_bytes())
    assert runtime['passed'] is True and runtime['independent_qualification'] is False
    expected_imports = {}
    for imported in re.findall(r'^import\s+([^\s]+)', data.decode('utf-8'), re.M):
        if imported.startswith(('Mathlib', 'Lean', 'Std', 'Batteries')):
            continue
        relative = Path(*imported.split('.')).with_suffix('.lean')
        candidates = [PROJECT / f'exp{i:03}' for i in [*range(16, 7, -1), 6]]
        owner = next((p for p in candidates if (p / 'lean' / relative).is_file()), None)
        assert owner is not None, 'Unresolved project source import: ' + imported
        imported_source = owner / 'lean' / relative
        artifact = owner / 'build/lib/lean' / relative.with_suffix('.olean')
        assert artifact.is_file(), 'Missing accepted import artifact: ' + imported
        expected_imports[imported] = {
            'source': imported_source.relative_to(PROJECT).as_posix(),
            'source_sha256': digest(imported_source),
            'artifact': artifact.relative_to(PROJECT).as_posix(),
            'artifact_sha256': digest(artifact),
        }
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = HERE / 'workflows' / (stamp + '_' + module)
    work.mkdir(parents=True, exist_ok=False)
    subprocess.run([sys.executable, str(HERE / 'prepare_check.py'), module],
                   check=True, capture_output=True, text=True)
    assert source.read_bytes() == data, 'Source changed while preparing.'
    (work / source.name).write_bytes(data)
    payload = (HERE / ('check_' + module + '.py')).read_bytes()
    launch_file = work / 'check.py'
    launch_file.write_bytes(payload)
    manifest = {'module': module, 'source_sha256': sha(data),
                'frozen_source': str(work / source.name), 'command_file': str(launch_file),
                'command_file_sha256': sha(payload), 'reviewed_helper_sha256': HELPERS,
                'lean_binary_sha256': LEAN_SHA, 'expected_project_imports': expected_imports,
                'runtime_readback': str(runtime_path), 'runtime_readback_sha256': digest(runtime_path),
                'bootstrap_receipt_sha256': runtime['bootstrap_receipt_sha256'],
                'mathlib_pin': runtime['mathlib_pin'], 'independent_qualification': False,
                'explicit_audit_requests': re.findall(r'^#print\s+axioms\s+(\S+)', data.decode(), re.M)}
    path = work / 'PREPARED.json'
    save_new(path, manifest)
    print(json.dumps({'prepared_manifest': str(path), 'source_sha256': sha(data),
          'project_imports_bound': expected_imports,
          'launch_command': command([COLAB, 'exec', '--session', 'exp016-development',
              '--file', launch_file, '--timeout', '660']),
          'full_cli_log_suggestion': str(work / 'CLI.log'),
          'next_step': 'Save full CLI output, then run this helper downloads MANIFEST CLI_LOG.'}, indent=2))


def downloads(manifest_path, cli_log):
    manifest = json.loads(manifest_path.read_bytes())
    module = manifest['module']
    text = cli_log.read_bytes().decode('utf-8')
    matches = re.findall(r'^RESULT_ARCHIVE (/content/exp016_dev/checks/[^\s]+\.zip) SHA256 ([0-9a-f]{64})$',
                         text, re.M)
    assert len(matches) == 1, 'Require the complete output from one finished check.'
    remote, archive_sha = matches[0]
    assert remote.endswith('_' + module + '.zip')
    target = manifest_path.parent / Path(remote).name
    print(json.dumps({'remote_archive': remote, 'expected_archive_sha256': archive_sha,
          'download_command': command([COLAB, 'download', remote, target,
              '--session', 'exp016-development']),
          'accept_command': command([sys.executable, __file__, 'accept', manifest_path,
              target, archive_sha]),
          'cli_log_sha256': digest(cli_log),
          'note': 'A failed compiler result is preserved evidence; accept rejects it.'}, indent=2))


def accept(manifest_path, archive, expected_sha):
    manifest = json.loads(manifest_path.read_bytes())
    module = manifest['module']
    assert re.fullmatch('[0-9a-f]{64}', expected_sha)
    assert digest(archive) == expected_sha
    assert manifest['reviewed_helper_sha256'] == HELPERS
    assert manifest['independent_qualification'] is False
    assert digest(Path(manifest['runtime_readback'])) == manifest['runtime_readback_sha256']
    source = ROOT / 'lean' / (module + '.lean')
    assert source.read_bytes() == Path(manifest['frozen_source']).read_bytes()
    assert digest(source) == manifest['source_sha256']
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        required = {module + '.lean', module + '.olean', 'RESULT.json', 'compiler.log', 'run_module.py'}
        assert set(z.namelist()) == required and len(z.namelist()) == len(required)
        rec = json.loads(z.read('RESULT.json'))
        assert rec['module'] == module and rec['exit_code'] == 0
        assert rec['sources_unchanged'] is True and rec['imports_unchanged'] is True
        assert rec['independent_qualification'] is False
        assert rec['lean_binary_sha256'] == manifest['lean_binary_sha256'] == LEAN_SHA
        assert rec['bootstrap_receipt_sha256'] == manifest['bootstrap_receipt_sha256']
        assert rec['source_sha256_before'] == rec['source_sha256_after'] == digest(source)
        assert z.read(module + '.lean') == source.read_bytes()
        assert sha(z.read('run_module.py')) == rec['runner_sha256'] == HELPERS['run_module.py']
        assert sha(z.read('compiler.log')) == rec['log_sha256']
        assert sha(z.read(module + '.olean')) == rec['output_sha256']
        for imported, expected in manifest['expected_project_imports'].items():
            assert rec['project_sources'][expected['source']] == expected['source_sha256'], imported
            assert rec['project_import_artifacts'][expected['artifact']] == expected['artifact_sha256'], imported
            assert digest(PROJECT / expected['source']) == expected['source_sha256'], imported
            assert digest(PROJECT / expected['artifact']) == expected['artifact_sha256'], imported
        log = z.read('compiler.log').decode('utf-8')
        assert 'error:' not in log and 'sorryAx' not in log
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
        assert len(reports) == len(manifest['explicit_audit_requests'])
        for requested in manifest['explicit_audit_requests']:
            assert sum(name == requested or name.endswith('.' + requested) for name, _ in reports) == 1
        assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
                   for _, a in reports)
    # The original reviewed acceptor is unchanged and performs the only artifact installation.
    completed = subprocess.run([sys.executable, str(HERE / 'accept_result.py'), str(archive), expected_sha],
                               check=True, capture_output=True, text=True)
    result = json.loads(completed.stdout)
    audit = {'passed': True, 'module': module, 'prepared_manifest_sha256': digest(manifest_path),
             'source_sha256': digest(source), 'receipt_sha256': result['receipt_sha256'],
             'artifact_sha256': result['artifact_sha256'], 'explicit_axiom_audit_count': len(reports),
             'explicit_axiom_audit_names': [n for n, _ in reports], 'standard_axioms_only': True,
             'warning_count': log.count('warning:'), 'expected_project_imports': manifest['expected_project_imports'],
             'bootstrap_receipt_sha256': manifest['bootstrap_receipt_sha256'],
             'runtime_readback_sha256': manifest['runtime_readback_sha256'],
             'helper_sha256': digest(Path(__file__)), 'independent_qualification': False,
             'scope': 'Source-bound incremental development with pinned restored imports, not independent qualification.'}
    save_new(Path(result['receipt']).parent / 'WORKFLOW_VALIDATION.json', audit)
    print(completed.stdout, end='')
    print(json.dumps(audit, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    p = sub.add_parser('prepare')
    p.add_argument('module')
    p.add_argument('--runtime-receipt', default='evidence/INITIAL_SAMPLING_RUNTIME_READBACK.json')
    p = sub.add_parser('downloads')
    p.add_argument('manifest', type=Path)
    p.add_argument('cli_log', type=Path)
    p = sub.add_parser('accept')
    p.add_argument('manifest', type=Path)
    p.add_argument('archive', type=Path)
    p.add_argument('sha256')
    args = parser.parse_args()
    verify_helpers()
    if args.action == 'prepare':
        prepare(args.module, args.runtime_receipt)
    elif args.action == 'downloads':
        downloads(args.manifest, args.cli_log)
    else:
        accept(args.manifest, args.archive, args.sha256)


if __name__ == '__main__':
    main()
