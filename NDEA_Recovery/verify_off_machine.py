"""Check explicitly listed backup copies on the current Colab VM."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import zipfile

root = Path('/content')
inputs_path = root / 'NDEA_BACKUP_INPUTS.json'
receipt_path = root / 'NDEA_OFF_MACHINE_BACKUP_RECEIPT.json'
inputs_bytes = inputs_path.read_bytes()
inputs = json.loads(inputs_bytes)
record = {
    'passed': False,
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'session': inputs['session'],
    'vm_id': inputs['vm_id'],
    'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
    'inputs_sha256': hashlib.sha256(inputs_bytes).hexdigest(),
    'storage': 'Temporary Colab VM filesystem; not permanent cloud storage.',
    'files': {},
}
try:
    if record['boot_id'] != inputs['expected_boot_id']:
        raise ValueError('Unexpected Colab boot identity')
    names = set()
    for item in inputs['files']:
        name = item['remote_name']
        if Path(name).name != name or name in names or name in {'.', '..'}:
            raise ValueError('Unsafe or duplicate backup filename')
        names.add(name)
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise ValueError('Missing or symlinked backup: ' + name)
        digest = hashlib.sha256()
        with path.open('rb') as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b''):
                digest.update(chunk)
        if digest.hexdigest() != item['sha256'] or path.stat().st_size != item['bytes']:
            raise ValueError('Backup hash or byte-count mismatch: ' + name)
        members = None
        if path.suffix == '.zip':
            with zipfile.ZipFile(path) as archive:
                bad = archive.testzip()
                if bad is not None:
                    raise ValueError('ZIP CRC failure: ' + bad)
                members = len(archive.infolist())
        record['files'][name] = {
            'sha256': digest.hexdigest(), 'bytes': path.stat().st_size,
            'zip_members_crc_checked': members, 'remote_path': str(path),
        }
    if not names:
        raise ValueError('Empty backup inventory')
    record['passed'] = True
except Exception as error:
    record['error'] = repr(error)
    raise
finally:
    temporary = receipt_path.with_suffix('.json.tmp')
    with temporary.open('w') as stream:
        stream.write(json.dumps(record, indent=2) + '\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, receipt_path)
    print(json.dumps(record), flush=True)
