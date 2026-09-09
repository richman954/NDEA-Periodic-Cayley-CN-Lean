#!/usr/bin/env python3
"""Verify preserved bytes; optionally reconstruct archives into a new directory.

This is a transport/integrity check, not a Lean proof qualification.
Pin the manifest/commit using the separately retained publication receipt.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_file(root, name):
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or any(x in ('', '.', '..') for x in p.parts):
        raise ValueError('Noncanonical path: ' + name)
    if str(p) != name:
        raise ValueError('Noncanonical path: ' + name)
    q = root
    for component in p.parts:
        q = q / component
        if q.is_symlink():
            raise ValueError('Symlink rejected: ' + name)
    if not q.is_file():
        raise ValueError('Missing regular file: ' + name)
    return q


def verify(root, manifest):
    if manifest['schema'] != 1:
        raise ValueError('Unsupported manifest schema')
    names = set()
    result = []
    for entry in manifest['archives']:
        name = entry['name']
        if PurePosixPath(name).name != name or name in ('', '.', '..') or name in names:
            raise ValueError('Invalid/duplicate archive name')
        names.add(name)
        h = hashlib.sha256()
        total = 0
        seen_parts = set()
        if not entry['parts']:
            raise ValueError('Empty part list')
        for part in entry['parts']:
            if part['path'] in seen_parts:
                raise ValueError('Duplicate archive part')
            seen_parts.add(part['path'])
            data = safe_file(root, part['path']).read_bytes()
            if len(data) != part['bytes'] or digest(data) != part['sha256']:
                raise ValueError('Part integrity failure: ' + part['path'])
            h.update(data)
            total += len(data)
        if total != entry['bytes'] or h.hexdigest() != entry['sha256']:
            raise ValueError('Archive integrity failure: ' + name)
        result.append({'name': name, 'bytes': total, 'sha256': h.hexdigest()})
    for entry in manifest['companions']:
        data = safe_file(root, entry['path']).read_bytes()
        if len(data) != entry['bytes'] or digest(data) != entry['sha256']:
            raise ValueError('Companion integrity failure: ' + entry['path'])
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--restore-to', type=Path)
    args = ap.parse_args()
    root = args.root.resolve()
    manifest = json.loads((root / 'BACKUP_MANIFEST.json').read_text())
    checked = verify(root, manifest)
    if args.restore_to:
        # No overwriting an existing destination, even when it is empty.
        args.restore_to.mkdir(parents=False, exist_ok=False)
        for entry in manifest['archives']:
            out = args.restore_to / entry['name']
            with out.open('xb') as handle:
                for part in entry['parts']:
                    handle.write(safe_file(root, part['path']).read_bytes())
            if out.stat().st_size != entry['bytes'] or digest(out.read_bytes()) != entry['sha256']:
                raise ValueError('Restored archive readback failed: ' + entry['name'])
    print(json.dumps({'passed': True, 'proof_verification': False,
                      'archives_verified': checked,
                      'companions_verified': len(manifest['companions']),
                      'restore_to': str(args.restore_to) if args.restore_to else None}, indent=2))


if __name__ == '__main__':
    main()
