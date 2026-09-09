"""Publish a verified, conveniently named Chromebook backup folder."""
from pathlib import Path, PurePosixPath
import datetime
import hashlib
import importlib.util
import io
import json
import os
import re
import shutil
import stat
import tempfile
import uuid
import zipfile

root = Path(__file__).resolve().parent
home = root.parent
sha = lambda b: hashlib.sha256(b).hexdigest()

def dump(value):
    return (json.dumps(value, indent=2) + '\n').encode()

def write(path, data):
    with path.open('xb') as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())

def sync_dir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)

def load_tool(name):
    spec = importlib.util.spec_from_file_location(name, root / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def read_regular(path):
    if path.is_symlink():
        raise ValueError('Source must not be a symlink: ' + str(path))
    return path.read_bytes()

def frozen_json(path):
    data = read_regular(path)
    return data, json.loads(data)

def copy_pinned(source, destination, expected_sha256):
    """Validate the bytes being copied against the selected receipt hash."""
    data = read_regular(source)
    if sha(data) != expected_sha256:
        raise ValueError('Selected archive changed before copying: ' + str(source))
    write(destination, data)
    if sha(destination.read_bytes()) != expected_sha256:
        raise ValueError('Copy readback mismatch: ' + str(destination))
    return {'sha256': expected_sha256, 'bytes': len(data), 'original': str(source)}

def copy_frozen(destination, data, original=None):
    write(destination, data)
    if destination.read_bytes() != data:
        raise ValueError('Frozen metadata readback mismatch: ' + str(destination))
    row = {'sha256': sha(data), 'bytes': len(data)}
    if original is not None:
        row['original'] = str(original)
        row['selection'] = 'Exact bytes captured before copying; live pointer may advance later.'
    return row

def validate_checkpoint_binding(checked, selected, active_name, packet_bytes, qualification_bytes):
    """Recovery must contain this active experiment's exact sealed receipts."""
    manifest = checked['manifest']
    if (manifest.get('active_experiment') != active_name
            or selected.get('active_experiment') != active_name):
        raise ValueError('Selected checkpoint belongs to another active experiment')
    if not manifest.get('final_packet_receipt_captured'):
        raise ValueError('Take a final checkpoint after sealing the active experiment')
    prefix = 'NDEA_Evolve_offruntime/' + active_name + '/evidence/'
    for name, data in [('FINAL_PACKET_RECEIPT.json', packet_bytes),
                       ('FINAL_VERIFICATION.json', qualification_bytes)]:
        row = manifest['files'].get(prefix + name)
        if row is None or row.get('sha256') != sha(data) or row.get('bytes') != len(data):
            raise ValueError('Checkpoint does not contain the current sealed receipt: ' + name)

def verify_sealed_packet(data, experiment, packet_receipt, qualification_bytes):
    """Read every sealed ZIP member and bind its accepted qualification to the receipt."""
    qualification = json.loads(qualification_bytes)
    if (not isinstance(packet_receipt, dict) or not isinstance(qualification, dict)
            or packet_receipt.get('passed') is not True or qualification.get('passed') is not True):
        raise ValueError('Supplemental experiment is not sealed and accepted: ' + experiment)
    if (sha(data) != packet_receipt.get('archive_sha256')
            or len(data) != packet_receipt.get('archive_bytes')):
        raise ValueError('Supplemental archive checksum/size mismatch: ' + experiment)
    prefix = experiment + '/'
    manifest_name = prefix + 'PACKET_MANIFEST.json'
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            names = set()
            for item in archive.infolist():
                path = PurePosixPath(item.filename)
                mode = stat.S_IFMT(item.external_attr >> 16)
                if (item.is_dir() or mode not in (0, stat.S_IFREG) or item.flag_bits & 1
                        or path.is_absolute() or '..' in path.parts or '\\' in item.filename
                        or str(path) != item.filename or not item.filename.startswith(prefix)
                        or item.filename in names):
                    raise ValueError('Unsafe or duplicate supplemental ZIP member: ' + item.filename)
                names.add(item.filename)
            if manifest_name not in names or archive.testzip() is not None:
                raise ValueError('Supplemental manifest missing or ZIP CRC failure: ' + experiment)
            manifest_bytes = archive.read(manifest_name)
            manifest = json.loads(manifest_bytes)
            if (not isinstance(manifest, dict) or not manifest
                    or 'PACKET_MANIFEST.json' in manifest
                    or sha(manifest_bytes) != packet_receipt.get('manifest_sha256')
                    or len(manifest) != packet_receipt.get('manifest_entries')
                    or len(names) != packet_receipt.get('verified_zip_files')
                    or names != {prefix + name for name in manifest} | {manifest_name}):
                raise ValueError('Supplemental manifest pin/coverage mismatch: ' + experiment)
            for name, digest in manifest.items():
                if sha(archive.read(prefix + name)) != digest:
                    raise ValueError('Supplemental payload hash mismatch: ' + experiment + '/' + name)
            if (prefix + 'evidence/FINAL_VERIFICATION.json' not in names
                    or archive.read(prefix + 'evidence/FINAL_VERIFICATION.json') != qualification_bytes):
                raise ValueError('Supplemental sealed qualification differs from ZIP: ' + experiment)
    except (zipfile.BadZipFile, RuntimeError, KeyError, TypeError) as error:
        raise ValueError('Invalid supplemental packet: ' + experiment) from error
    return {'archive_sha256': sha(data), 'archive_bytes': len(data),
            'manifest_sha256': sha(manifest_bytes), 'payload_files_verified': len(manifest),
            'zip_members_verified': len(names), 'crc_and_payload_hashes_verified': True}

def select_supplemental_packets(project, active_name):
    """Require every sealed packet after the 001–012 base and before the active one."""
    if re.fullmatch(r'exp[0-9]{3}', active_name) is None:
        raise ValueError('Invalid active experiment name')
    selected = []
    for number in range(13, int(active_name[3:])):
        name = f'exp{number:03d}'
        experiment = project / name
        if experiment.is_symlink() or not experiment.is_dir():
            raise ValueError('Missing supplemental experiment: ' + name)
        packet_path = experiment / 'evidence/FINAL_PACKET_RECEIPT.json'
        qualification_path = experiment / 'evidence/FINAL_VERIFICATION.json'
        try:
            packet_bytes, packet_receipt = frozen_json(packet_path)
            qualification_bytes, qualification = frozen_json(qualification_path)
            packet = Path(packet_receipt['archive'])
            checked = verify_sealed_packet(read_regular(packet), name, packet_receipt, qualification_bytes)
        except (OSError, KeyError, TypeError) as error:
            raise ValueError('Missing or invalid supplemental sealed evidence: ' + name) from error
        selected.append({'experiment': name, 'packet': packet,
                         'copy_name': name.capitalize() + '_Verified_Review_Packet.zip',
                         'packet_receipt_path': packet_path, 'packet_receipt_bytes': packet_bytes,
                         'qualification_path': qualification_path, 'qualification_bytes': qualification_bytes,
                         'packet_receipt_sha256': sha(packet_bytes),
                         'qualification_sha256': sha(qualification_bytes),
                         'verification': checked})
    return selected

def validate_supplementals_unchanged(selected):
    for item in selected:
        if (read_regular(item['packet_receipt_path']) != item['packet_receipt_bytes']
                or read_regular(item['qualification_path']) != item['qualification_bytes']):
            raise ValueError('Supplemental sealed receipts changed during copy: ' + item['experiment'])
        if sha(read_regular(item['packet'])) != item['verification']['archive_sha256']:
            raise ValueError('Supplemental archive changed during copy: ' + item['experiment'])

def main():
    if root.name != 'NDEA_Recovery' or not (home / 'NDEA_Evolve_offruntime').is_dir():
        raise ValueError('Run publisher only from original/restored NDEA_Recovery beside the project')
    selected_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    state_bytes, state = frozen_json(root / 'TASK_STATE.json')
    checkpoint_tool = load_tool('checkpoint')
    active = checkpoint_tool.active_experiment(root / 'TASK_STATE.json')
    if read_regular(root / 'TASK_STATE.json') != state_bytes:
        raise ValueError('Task state changed during active-experiment selection')
    release_bytes, release = frozen_json(root / 'RELEASE_ARCHIVE_RECEIPT.json')
    checkpoint_bytes, checkpoint = frozen_json(root / 'LATEST_CHECKPOINT.json')
    active_name = active.name
    active_label = 'Experiment ' + active_name.removeprefix('exp')
    packet_bytes, packet_receipt = frozen_json(active / 'evidence/FINAL_PACKET_RECEIPT.json')
    qualification_bytes, qualification = frozen_json(active / 'evidence/FINAL_VERIFICATION.json')
    if (packet_receipt.get('passed') is not True or qualification.get('passed') is not True
            or release.get('passed') is not True):
        raise ValueError('Active experiment is not sealed and accepted')
    packet = Path(packet_receipt['archive'])
    if sha(read_regular(packet)) != packet_receipt['archive_sha256']:
        raise ValueError('Active review packet checksum mismatch')
    supplemental = select_supplemental_packets(home / 'NDEA_Evolve_offruntime', active_name)
    packet_copy_name = active_name.capitalize() + '_Verified_Review_Packet.zip'
    dated_bytes, dated = frozen_json(Path(checkpoint['receipt']))
    if (sha(dated_bytes) != checkpoint['receipt_sha256']
            or dated['archive'] != checkpoint['archive']
            or dated['archive_sha256'] != checkpoint['archive_sha256']):
        raise ValueError('Checkpoint pointer and dated receipt disagree')
    checked = checkpoint_tool.verify_archive(Path(checkpoint['archive']), checkpoint['archive_sha256'])
    validate_checkpoint_binding(checked, checkpoint, active_name, packet_bytes, qualification_bytes)
    load_tool('archive_releases').verify_archive(Path(release['archive']), release['archive_sha256'])
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%d_%H%M%SZ')
    downloads = home / 'Downloads'
    if downloads.is_symlink():
        raise ValueError('Downloads must not be a symlink')
    downloads.mkdir(exist_ok=True)
    destination = downloads / ('NDEA_Backup_' + stamp + '_' + uuid.uuid4().hex[:6])
    stage = Path(tempfile.mkdtemp(prefix='.ndea-copy-', dir=downloads))
    archives = {
        'COMPLETED_RELEASES_001-012.zip': (Path(release['archive']), release['archive_sha256']),
        'CURRENT_RECOVERY.zip': (Path(checkpoint['archive']), checkpoint['archive_sha256']),
        packet_copy_name: (packet, packet_receipt['archive_sha256']),
    }
    frozen = {
        'CHECKPOINT_RECEIPT.json': (checkpoint_bytes, root / 'LATEST_CHECKPOINT.json'),
        'CHECKPOINT_DATED_RECEIPT.json': (dated_bytes, Path(checkpoint['receipt'])),
        'RELEASE_RECEIPT.json': (release_bytes, root / 'RELEASE_ARCHIVE_RECEIPT.json'),
        'ACTIVE_PACKET_RECEIPT.json': (packet_bytes, active / 'evidence/FINAL_PACKET_RECEIPT.json'),
        'ACTIVE_VERIFICATION.json': (qualification_bytes, active / 'evidence/FINAL_VERIFICATION.json'),
    }
    supplemental_coverage = []
    for item in supplemental:
        name = item['experiment'].capitalize()
        archives[item['copy_name']] = (item['packet'], item['verification']['archive_sha256'])
        frozen[name + '_PACKET_RECEIPT.json'] = (item['packet_receipt_bytes'], item['packet_receipt_path'])
        frozen[name + '_VERIFICATION.json'] = (item['qualification_bytes'], item['qualification_path'])
        supplemental_coverage.append({'experiment': item['experiment'], 'archive': item['copy_name'],
                                      'packet_receipt': name + '_PACKET_RECEIPT.json',
                                      'qualification': name + '_VERIFICATION.json',
                                      'packet_receipt_sha256': item['packet_receipt_sha256'],
                                      'qualification_sha256': item['qualification_sha256'],
                                      **item['verification']})
    supplemental_names = [item['experiment'] for item in supplemental]
    supplemental_text = ('Supplemental sealed packets cover ' + ', '.join(supplemental_names) + '.\n'
        '    Each supplemental ZIP has its exact packet receipt and final verification\n'
        '    saved alongside it; ZIP CRC, complete manifest coverage and every payload\n'
        '    hash were checked against the sealed receipt before copying.'
        if supplemental else 'No supplemental packet is needed between the 001–012 base and the active experiment.')
    sources = {
        'checkpoint.py': root / 'checkpoint.py',
        'archive_releases.py': root / 'archive_releases.py',
        'make_local_copy.py': root / 'make_local_copy.py',
        'START_HERE.md': root / 'START_HERE.md',
        'RECOVERY_POLICY.md': root / 'RECOVERY_POLICY.md',
        'RECOVERY_REVIEW.md': root / 'RECOVERY_REVIEW.md',
        'NDEA_STARTUP_INSTRUCTIONS.md': home / 'AGENTS.md',
    }
    try:
        rows = {}
        for name, (source, digest) in archives.items():
            rows[name] = copy_pinned(source, stage / name, digest)
        for name, (data, source) in frozen.items():
            rows[name] = copy_frozen(stage / name, data, source)
        for name, source in sources.items():
            rows[name] = copy_frozen(stage / name, read_regular(source), source)
        state['active_task'] = 'Verified Chromebook backup folder prepared; ' + active_label + ' is complete.'
        state['remaining'] = []
        state['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        state['last_updated_utc'] = state['utc']
        state['recovery']['local_download_folder'] = str(destination)
        state['recovery']['permanent_storage'] = 'Verified local Chromebook copies are the chosen backup destination. Google Drive backup was canceled by the user.'
        state['recovery']['local_backup_receipt'] = str(root / 'LOCAL_BACKUP_RECEIPT.json')
        state['recovery'].pop('optional_follow_up', None)
        data = dump(state)
        write(stage / 'TASK_STATE.json', data)
        rows['TASK_STATE.json'] = {'sha256': sha(data), 'bytes': len(data)}
        text = f'''NDEA CHROMEBOOK BACKUP — {stamp}

    Find this folder in Files > Linux files > Downloads > {destination.name}.
    These are real copies stored on this Chromebook, the user-selected backup
    location. Google Drive backup was canceled; do not mount Drive or resume the
    transfer unless the user asks again. Preserve the original project and archives.

    COMPLETED_RELEASES_001-012.zip contains the preserved release packets, evidence
    and checksum/receipt companions through Experiment 012 (40 payload files).
    {supplemental_text}
    Together with the active packet, completed packet coverage is contiguous
    from Experiment 001 through {active_label}. Historical intermediate files
    are included only where the preserved packets or current checkpoint contain them.
    CURRENT_RECOVERY.zip is the newest checkpoint selected at {selected_utc}.
    It contains the selected experiment, notes, tools and task state, including
    the exact current sealed packet and verification receipts. A live watcher
    may publish a newer checkpoint later without changing this pinned selection.
    Compiler/build caches are excluded. The separately saved
    TASK_STATE.json reflects preparation of this convenience folder; older state
    inside a recovery snapshot should be interpreted using actual result receipts.
    {packet_copy_name} is included separately for convenient review of {active_label}.
    ACTIVE_PACKET_RECEIPT.json records its sealed archive hash.

    {active_label} passed {qualification['audits']} audits locally and on a separate fresh Colab VM.
    The original archives were preserved; this folder is not a new proof check.

    VERIFY (open a Linux terminal in this folder):
      sha256sum -c SHA256SUMS
      python3 -B checkpoint.py --verify CURRENT_RECOVERY.zip --sha256 {checkpoint['archive_sha256']}
      python3 -B archive_releases.py verify COMPLETED_RELEASES_001-012.zip --sha256 {release['archive_sha256']}

    RESTORE ONLY WHEN NEEDED, into two NEW directories:
      python3 -B checkpoint.py --restore CURRENT_RECOVERY.zip --sha256 {checkpoint['archive_sha256']} --restore-to /home/richman954/NDEA_Restored_Workspace
      python3 -B archive_releases.py restore COMPLETED_RELEASES_001-012.zip --sha256 {release['archive_sha256']} --destination /home/richman954/NDEA_Restored_Releases

    Both destinations must not already exist. Read the restored START_HERE.md,
    inspect actual result receipts, and remap saved absolute paths before resuming.
    Supplemental and active review ZIPs are separate preserved packets; their
    contents can be inspected with a ZIP viewer. Keep their accompanying receipts.
    Use the checkpoint.py and archive_releases.py copies HERE for verify/restore
    only. For future snapshots or publishing, use the original/restored utilities
    in NDEA_Recovery beside NDEA_Evolve_offruntime. The preserved make_local_copy.py
    is publisher source for that location; do not execute it in this Downloads
    folder. Do not run checkpoint.py --once or --watch from this folder either.
    '''
        data = text.encode()
        write(stage / 'README.txt', data)
        rows['README.txt'] = {'sha256': sha(data), 'bytes': len(data)}
        manifest = {'passed': True, 'utc': state['utc'], 'selected_utc': selected_utc,
                    'active_experiment': active_name, 'folder': str(destination),
                    'files': rows, 'supplemental_packets': supplemental_coverage,
                    'completed_packet_coverage': {'base': 'exp001–exp012',
                        'supplemental': supplemental_names, 'active': active_name, 'contiguous': True},
                    'scope': 'Verified local Chromebook copies; no Google Drive copy claimed. Historical intermediate files are limited to those included in the preserved packets and selected checkpoint.'}
        data = dump(manifest)
        write(stage / 'BACKUP_MANIFEST.json', data)
        hashes = {name: row['sha256'] for name, row in rows.items()}
        hashes['BACKUP_MANIFEST.json'] = sha(data)
        checksum = ''.join(f'{digest}  {name}\n' for name, digest in sorted(hashes.items())).encode()
        write(stage / 'SHA256SUMS', checksum)
        for name, digest in hashes.items():
            if sha((stage / name).read_bytes()) != digest:
                raise ValueError('Final copy mismatch: ' + name)
        for name, source in sources.items():
            if sha(read_regular(source)) != rows[name]['sha256']:
                raise ValueError('Original changed during copy: ' + str(source))
        for source, digest in archives.values():
            if sha(read_regular(source)) != digest:
                raise ValueError('Original archive changed during copy: ' + str(source))
        if read_regular(root / 'TASK_STATE.json') != state_bytes:
            raise ValueError('Task state changed during copy; retry with the current task')
        if (read_regular(active / 'evidence/FINAL_PACKET_RECEIPT.json') != packet_bytes
                or read_regular(active / 'evidence/FINAL_VERIFICATION.json') != qualification_bytes):
            raise ValueError('Active sealed receipts changed during copy')
        validate_supplementals_unchanged(supplemental)
        sync_dir(stage)
        os.rename(stage, destination)
        sync_dir(downloads)
        receipt = {'passed': True, 'utc': state['utc'], 'selected_utc': selected_utc,
                   'active_experiment': active_name, 'folder': str(destination),
                   'files_verified': len(hashes), 'bytes': sum(p.stat().st_size for p in destination.iterdir()),
                   'manifest_sha256': hashes['BACKUP_MANIFEST.json'],
                   'checksum_sha256': sha(checksum), 'current_recovery_sha256': checkpoint['archive_sha256'],
                   'completed_releases_sha256': release['archive_sha256'],
                   'active_packet_sha256': packet_receipt['archive_sha256'],
                   'active_packet_receipt_sha256': sha(packet_bytes),
                   'supplemental_packets': supplemental_coverage,
                   'completed_packet_coverage': manifest['completed_packet_coverage'],
                   'selected_checkpoint_receipt_sha256': sha(checkpoint_bytes),
                   'selected_receipts_copied_exactly': True, 'original_archives_unchanged': True,
                   'originals_unchanged': True, 'google_drive_copy_completed': False}
        for name, value in [('LOCAL_BACKUP_RECEIPT.json', receipt), ('TASK_STATE.json', state)]:
            temporary = root / ('.pending-local-' + uuid.uuid4().hex)
            write(temporary, dump(value))
            os.replace(temporary, root / name)
        sync_dir(root)
        print(json.dumps(receipt), flush=True)
    finally:
        if stage.exists():
            shutil.rmtree(stage)


if __name__ == '__main__':
    main()
