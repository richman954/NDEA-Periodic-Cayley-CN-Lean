#!/usr/bin/env python3
"""Create, verify, or restore a selected completed-release recovery bundle.

Only the explicit release allowlist and its checksum/receipt companions are
read. Originals are never modified. Creation atomically publishes a directory
containing the checked ZIP, its manifest, inventory, checksum and receipt.
"""
import argparse
import datetime
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import tempfile
import uuid
import zipfile

ORIGINAL_HOME = Path('/home/richman954')
OFF = 'NDEA_Evolve_offruntime/'
EXP003 = OFF+'exp003/final_delivery_20260906/'
EXP004 = OFF+'exp004/releases/20260907_verified_final/'
PRIMARY = [
    'Exp001_Independent_Review_Packet_v1.zip',
    'Exp002_Independent_Review_Packet_v1.zip',
    'Exp005_Independent_Verification_Packet_20260908.zip',
    *[f'Exp{i:03}_Verified_Review_Packet_20260908.zip' for i in range(6, 13)],
    'Experiments_001-007_Recap_and_File_Index_20260908.zip',
    'Experiments_001-008_Fresh_VM_Recheck_20260908.zip',
    EXP003+'NDEA_Evolve_exp003_step1_final_evidence.tar.gz',
    EXP004+'exp004_verified_final_source.tar.gz',
]
COMPANIONS = [
    EXP003+'DELIVERY_SHA256SUMS',
    EXP003+'NDEA_Evolve_exp003_step1_delivery_spec.json',
    EXP003+'NDEA_Evolve_exp003_step1_final_delivery_receipt.json',
    EXP003+'NDEA_Evolve_exp003_step1_final.bundle',
    EXP004+'DELIVERY_RECEIPT.json',
    EXP004+'exp004_verified_final.bundle',
    *[OFF+f'exp{i:03}/evidence/FINAL_PACKET_RECEIPT.json' for i in range(6, 13)],
    OFF+'exp008/independent_checks/colab_r2_20260908/FINAL_PACKET_RECEIPT.json',
]
MANIFEST = '_recovery/MANIFEST.json'
INVENTORY = '_recovery/INVENTORY.md'
SCOPE = ('Selected completed release/review packets for Experiments 001–012, '
         'the 001–007 recap, the 001–008 fresh-VM recheck, explicit Exp003/004 '
         'release archives and Git bundles, and available checksum/receipt companions. '
         'This is not a backup of every historical intermediate file, current '
         'working tree, build cache, compiler installation, or account credential. '
         'Current task-state checkpoints are maintained separately.')


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2, ensure_ascii=False)+'\n').encode()


def safe_name(name):
    p = PurePosixPath(name)
    return bool(name) and not p.is_absolute() and str(p) == name and \
        not any(part in {'.', '..'} for part in p.parts) and '\\' not in name and '\0' not in name


def durable_write(path, data):
    with path.open('xb') as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())


def sync_directory(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def replace_metadata(path, data):
    """Publish the current-generation pointer while retaining immutable generations."""
    temporary = path.with_name('.'+path.name+'.'+uuid.uuid4().hex+'.tmp')
    try:
        durable_write(temporary, data)
        os.replace(temporary, path)
        sync_directory(path.parent)
    finally:
        if temporary.exists():
            temporary.unlink()


def checked_payload(source_root):
    names = set(PRIMARY+COMPANIONS)
    for name in PRIMARY:
        for suffix in ['.sha256', '.sha256.txt']:
            if (source_root/(name+suffix)).is_file():
                names.add(name+suffix)
    payload = {}
    for name in sorted(names):
        require(safe_name(name), 'Unsafe source path: '+name)
        p = source_root/name
        require(p.is_file() and not p.is_symlink(), 'Missing regular release file: '+name)
        require(p.resolve().is_relative_to(source_root.resolve()), 'Source escapes selected root')
        payload[name] = p.read_bytes()
    checked_receipts = []
    for name in COMPANIONS:
        if not name.endswith('FINAL_PACKET_RECEIPT.json'):
            continue
        receipt = json.loads(payload[name])
        require(receipt.get('passed') is True, 'Packet receipt is not accepted: '+name)
        archive_name = Path(receipt['archive']).name
        expected = receipt.get('archive_sha256', receipt.get('sha256'))
        require(archive_name in payload and digest(payload[archive_name]) == expected,
                'Packet receipt archive pin differs: '+name)
        size = receipt.get('archive_bytes', receipt.get('bytes'))
        if size is not None:
            require(len(payload[archive_name]) == size, 'Packet receipt size differs: '+name)
        checked_receipts.append(name)
    exp3 = json.loads(payload[EXP003+'NDEA_Evolve_exp003_step1_final_delivery_receipt.json'])
    exp4 = json.loads(payload[EXP004+'DELIVERY_RECEIPT.json'])
    require(exp3['status'] == 'PASS' and exp4.get('passed') is True, 'Unaccepted Exp003/004 delivery')
    for receipt in [exp3, exp4]:
        for row in receipt['artifacts'].values():
            name = str(Path(row['path']).relative_to(ORIGINAL_HOME))
            require(name in payload and digest(payload[name]) == row['sha256'] and
                    len(payload[name]) == row['size_bytes'], 'Delivery artifact pin differs: '+name)
    checksum_lines = 0
    for name, data in payload.items():
        if not (name.endswith(('.sha256', '.sha256.txt')) or name.endswith('/DELIVERY_SHA256SUMS')):
            continue
        for line in data.decode().splitlines():
            if not line.strip():
                continue
            match = re.fullmatch(r'([0-9a-f]{64})\s+\*?(.+)', line)
            require(match is not None, 'Unsupported checksum line: '+name)
            relative = str(PurePosixPath(name).parent/match[2])
            require(relative in payload and digest(payload[relative]) == match[1],
                    'Adjacent checksum differs: '+relative)
            checksum_lines += 1
    inner_zips = 0
    for name in PRIMARY:
        if name.endswith('.zip'):
            with zipfile.ZipFile(io.BytesIO(payload[name])) as z:
                require(z.testzip() is None, 'Original packet ZIP CRC failure: '+name)
                require(len(z.namelist()) == len(set(z.namelist())), 'Duplicate original ZIP member: '+name)
            inner_zips += 1
    script_name = 'NDEA_Recovery/archive_releases.py'
    payload[script_name] = Path(__file__).read_bytes()
    return payload, {'accepted_packet_receipts_checked': len(checked_receipts),
                     'exp003_exp004_delivery_receipts_checked': 2,
                     'adjacent_checksum_lines_checked': checksum_lines,
                     'original_zip_crc_checks': inner_zips}


def verify_archive(archive, expected_sha256=None):
    raw = archive.read_bytes()
    archive_hash = digest(raw)
    if expected_sha256 is not None:
        require(archive_hash == expected_sha256, 'Recovery archive SHA-256 mismatch')
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        infos = z.infolist()
        names = [p.filename for p in infos]
        require(len(names) == len(set(names)) and MANIFEST in names, 'Recovery ZIP coverage/manifest failure')
        for item in infos:
            require(safe_name(item.filename) and not item.is_dir() and
                    not stat.S_ISLNK(item.external_attr >> 16), 'Unsafe recovery ZIP entry')
        require(z.testzip() is None, 'Recovery ZIP CRC failure')
        manifest_raw = z.read(MANIFEST)
        manifest = json.loads(manifest_raw)
        require(manifest['schema'] == 'ndea.completed_release_backup.v1', 'Unsupported manifest schema')
        require(set(names) == set(manifest['files']) | {MANIFEST}, 'Recovery manifest coverage mismatch')
        required = set(PRIMARY+COMPANIONS+[INVENTORY, 'NDEA_Recovery/archive_releases.py'])
        require(required.issubset(manifest['files']), 'Required release/receipt coverage missing')
        for name, row in manifest['files'].items():
            data = z.read(name)
            require(len(data) == row['bytes'] and digest(data) == row['sha256'],
                    'Recovery member hash/size mismatch: '+name)
    return {'passed': True, 'archive_sha256': archive_hash, 'archive_bytes': len(raw),
            'manifest_sha256': digest(manifest_raw), 'payload_files': len(manifest['files']),
            'zip_members': len(names), 'crc_checked': True, 'all_payload_hashes_checked': True}


def create(source_root, output_dir):
    payload, source_checks = checked_payload(source_root)
    source_hashes = {n: digest(b) for n, b in payload.items() if n != 'NDEA_Recovery/archive_releases.py'}
    utc = datetime.datetime.now(datetime.timezone.utc)
    tag = utc.strftime('%Y%m%dT%H%M%S.%fZ')+'_'+uuid.uuid4().hex[:8]
    basename = 'NDEA_Completed_Releases_001-012_'+tag
    inventory = '# Completed-release recovery inventory\n\n'+SCOPE+'\n\n'
    inventory += 'Created '+utc.isoformat()+'. Originals are preserved byte-for-byte.\n\n'
    inventory += 'Archive member paths match their paths relative to `/home/richman954`. '
    inventory += 'Restore into a new directory and inspect before moving files into an existing workspace.\n\n'
    inventory += '| Relative path | Bytes | SHA-256 |\n|---|---:|---|\n'
    for name, data in sorted(payload.items()):
        inventory += f'| `{name}` | {len(data)} | `{digest(data)}` |\n'
    inventory += '\nThe manifest covers this inventory too. The manifest itself is bound by '
    inventory += 'the external receipt and ZIP checksum, avoiding a self-hash cycle.\n'
    inventory += '\nVerify or restore using the accompanying script:\n\n```sh\n'
    inventory += 'python3 -B archive_releases.py verify /path/to/bundle.zip --sha256 EXPECTED_SHA256\n'
    inventory += 'python3 -B archive_releases.py restore /path/to/bundle.zip --sha256 EXPECTED_SHA256 --destination /path/to/new-directory\n```\n'
    payload[INVENTORY] = inventory.encode()
    manifest = {'schema': 'ndea.completed_release_backup.v1', 'utc': utc.isoformat(),
                'original_root': str(ORIGINAL_HOME), 'scope': SCOPE,
                'files': {n: {'bytes': len(b), 'sha256': digest(b)} for n, b in sorted(payload.items())}}
    payload[MANIFEST] = json_bytes(manifest)
    output_dir.mkdir(parents=True, exist_ok=True)
    final = output_dir/basename
    require(not final.exists(), 'Recovery generation already exists')
    stage = Path(tempfile.mkdtemp(prefix='.building_', dir=output_dir))
    try:
        archive = stage/(basename+'.zip')
        with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
            for name, data in sorted(payload.items()):
                compression = zipfile.ZIP_STORED if name.endswith(('.zip', '.tar.gz')) else zipfile.ZIP_DEFLATED
                z.writestr(name, data, compress_type=compression)
        with archive.open('rb') as f:
            os.fsync(f.fileno())
        checked = verify_archive(archive)
        with zipfile.ZipFile(archive) as z:
            require(all(z.read(n) == b for n, b in payload.items()), 'Recovery ZIP exact readback mismatch')
        for name, expected in source_hashes.items():
            require(digest((source_root/name).read_bytes()) == expected, 'Original changed during packaging: '+name)
        require(digest(Path(__file__).read_bytes()) == manifest['files']['NDEA_Recovery/archive_releases.py']['sha256'],
                'Recovery script changed during packaging')
        receipt = {**checked, 'utc': utc.isoformat(), 'archive': str(final/archive.name),
                   'source_checks': source_checks, 'originals_unchanged': True,
                   'exact_zip_readback': True, 'scope': SCOPE,
                   'publication': 'Generation directory atomically renamed after complete validation; receipt and checksum are outside ZIP.'}
        durable_write(stage/'MANIFEST.json', payload[MANIFEST])
        durable_write(stage/'INVENTORY.md', payload[INVENTORY])
        durable_write(stage/'RECEIPT.json', json_bytes(receipt))
        durable_write(stage/(archive.name+'.sha256'), (checked['archive_sha256']+'  '+archive.name+'\n').encode())
        sync_directory(stage)
        os.rename(stage, final)
        sync_directory(output_dir)
        replace_metadata(output_dir.parent/'RELEASE_INVENTORY.json', json_bytes({
            'archive': receipt['archive'], 'archive_sha256': receipt['archive_sha256'],
            'inventory_path': str(final/'INVENTORY.md'), 'manifest': manifest}))
        replace_metadata(output_dir.parent/'RELEASE_ARCHIVE_RECEIPT.json', json_bytes(receipt))
        return receipt
    finally:
        if stage.exists():
            shutil.rmtree(stage)


def restore(archive, expected_sha256, destination):
    require(not destination.exists() and not destination.is_symlink(), 'Restore destination must not exist')
    require(not any(p.is_symlink() for p in destination.parents),
            'Restore destination must not have symlinked ancestors')
    checked = verify_archive(archive, expected_sha256)
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix='.restoring_', dir=destination.parent))
    try:
        with zipfile.ZipFile(archive) as z:
            manifest = json.loads(z.read(MANIFEST))
            for name, row in manifest['files'].items():
                require(safe_name(name), 'Unsafe restore name')
                data = z.read(name)
                require(digest(data) == row['sha256'], 'Archive changed during restore')
                p = stage/name
                p.parent.mkdir(parents=True, exist_ok=True)
                durable_write(p, data)
            durable_write(stage/MANIFEST, z.read(MANIFEST))
        require(digest(archive.read_bytes()) == checked['archive_sha256'], 'Archive changed during restore')
        for name, row in manifest['files'].items():
            require(digest((stage/name).read_bytes()) == row['sha256'], 'Restored file differs')
        for current, dirs, files in os.walk(stage, topdown=False):
            sync_directory(Path(current))
        require(not destination.exists() and not destination.is_symlink(), 'Restore destination appeared during restore')
        os.rename(stage, destination)
        sync_directory(destination.parent)
        return {**checked, 'restored_to': str(destination), 'restored_payload_hashes_checked': True}
    finally:
        if stage.exists():
            shutil.rmtree(stage)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    make = commands.add_parser('create')
    make.add_argument('--source-root', type=Path, default=ORIGINAL_HOME)
    make.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parent/'releases')
    for command in ['verify', 'restore']:
        sub = commands.add_parser(command)
        sub.add_argument('archive', type=Path)
        sub.add_argument('--sha256', required=True)
        if command == 'restore':
            sub.add_argument('--destination', type=Path, required=True)
    args = parser.parse_args()
    if args.command == 'create':
        result = create(args.source_root.resolve(), args.output_dir.resolve())
    elif args.command == 'verify':
        result = verify_archive(args.archive, args.sha256)
    else:
        result = restore(args.archive, args.sha256, args.destination.absolute())
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
