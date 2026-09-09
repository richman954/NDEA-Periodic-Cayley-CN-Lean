#!/usr/bin/env python3
"""Independently clone and verify the uploaded source backup; no remote writes."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import traceback

ROOT = Path('/home/richman954/NDEA_GitHub_Backup')
CLONE = ROOT / 'source_readback'
UPLOAD = ROOT / 'SOURCE_UPLOAD.json'
BASE = '15b13fb8ad5e0b51d1ec3e4a0fefcb68614ebd9c'
COMMIT = '2a4028add0c09e7e8445e8f6886a965cd2573ac0'
TREE = '252ca564f70e9d4772c920cd85338f605d80f4a4'
BRANCH = 'backup/ndeaevolve-20260909'
sha256 = lambda data: hashlib.sha256(data).hexdigest()
commands = []
result = {'passed': False, 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'remote': 'https://github.com/richman954/NDEA-Periodic-Cayley-CN-Lean.git',
          'branch': BRANCH, 'expected_commit': COMMIT, 'expected_tree': TREE,
          'expected_parent': BASE, 'clone': str(CLONE), 'commands': commands}

def run(label, args, cwd=None):
    log = ROOT / f'source_readback_{label}.log'
    with log.open('xb') as output:
        process = subprocess.run(args, cwd=cwd, stdout=output, stderr=subprocess.STDOUT)
    data = log.read_bytes()
    commands.append({'command': args, 'cwd': str(cwd) if cwd else None,
                     'exit_code': process.returncode, 'log': str(log),
                     'log_sha256': sha256(data), 'bytes': len(data)})
    if process.returncode:
        raise RuntimeError(f'{label} returned {process.returncode}; inspect saved log')
    return data

def git(label, *args):
    return run(label, ['git', '--no-optional-locks', *args], CLONE)

def tree_entries(raw):
    entries = {}
    for entry in raw.split(b'\0'):
        if not entry:
            continue
        meta, name = entry.split(b'\t', 1)
        mode, kind, oid = meta.decode().split()
        entries[name.decode()] = (mode, kind, oid)
    return entries

try:
    assert not CLONE.exists(), 'Readback destination must be new'
    upload_data = UPLOAD.read_bytes()
    manifest = json.loads(upload_data)
    result['upload_manifest_sha256'] = sha256(upload_data)
    run('clone', ['git', 'clone', '--branch', BRANCH, '--single-branch', result['remote'], str(CLONE)])
    head = git('head', 'rev-parse', 'HEAD').decode().strip()
    parents = git('parents', 'show', '-s', '--format=%P', 'HEAD').decode().strip().split()
    tree = git('tree', 'rev-parse', 'HEAD^{tree}').decode().strip()
    base_tree = git('base_tree', 'rev-parse', BASE + '^{tree}').decode().strip()
    assert head == COMMIT and parents == [BASE] and tree == TREE
    assert base_tree == manifest['base_tree']
    before = tree_entries(git('original_tree', 'ls-tree', '-rz', BASE))
    after = tree_entries(git('uploaded_tree', 'ls-tree', '-rz', COMMIT))
    assert len(before) == 66
    assert all(after.get(path) == value for path, value in before.items())
    selected = manifest['files']
    assert len(selected) == 1093
    targets = [e['target'] for e in selected]
    assert len(set(targets)) == len(targets)
    assert set(after) - set(before) == set(targets)
    assert not set(before).intersection(targets)
    for entry in selected:
        name = entry['target']
        path = Path(name)
        assert not path.is_absolute() and '..' not in path.parts
        local = CLONE / path
        assert local.is_file() and not local.is_symlink()
        data = local.read_bytes()
        assert len(data) == entry['bytes'] and sha256(data) == entry['sha256'], name
        git_blob_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert after[name] == (entry['git_mode'], 'blob', git_blob_sha), name
    diff = git('diff', 'diff', '--name-status', '-z', BASE, COMMIT).split(b'\0')
    assert diff.pop() == b''
    assert len(diff) == 2 * len(targets)
    assert all(diff[i] == b'A' for i in range(0, len(diff), 2))
    assert {diff[i].decode() for i in range(1, len(diff), 2)} == set(targets)
    git('fsck', 'fsck', '--full')
    status = git('status', 'status', '--porcelain=v1', '--untracked-files=all')
    assert status == b''
    refs = git('remote_refs', 'ls-remote', '--heads', 'origin', 'refs/heads/main', 'refs/heads/' + BRANCH)
    ref_map = dict(line.decode().split()[::-1] for line in refs.splitlines())
    assert ref_map['refs/heads/main'] == BASE
    assert ref_map['refs/heads/' + BRANCH] == COMMIT
    result.update({'passed': True, 'actual_commit': head, 'actual_tree': tree,
        'actual_parents': parents, 'original_main_files_unchanged': len(before),
        'uploaded_files_sha256_verified': len(selected),
        'uploaded_bytes_verified': sum(e['bytes'] for e in selected),
        'all_added_paths_match_upload_manifest': True, 'all_git_blob_hashes_verified': True,
        'git_fsck_passed': True, 'worktree_clean': True, 'remote_main_unchanged': True,
        'remote_branch_still_matches_verified_commit': True})
except Exception as error:
    result['error'] = str(error)
    result['traceback'] = traceback.format_exc()
finally:
    result['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes())
    receipt = ROOT / 'SOURCE_REMOTE_READBACK.json'
    with receipt.open('x') as output:
        output.write(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'passed': result['passed'], 'receipt': str(receipt),
                      'receipt_sha256': sha256(receipt.read_bytes()),
                      'error': result.get('error')}, indent=2))
    if not result['passed']:
        raise SystemExit(1)
