"""Focused pin/receipt race regressions; no real backup publication."""
import copy
import contextlib
import datetime
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import zipfile

import make_local_copy as publisher


def zip_bytes(text):
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, 'w') as archive:
        archive.writestr('fixture.txt', text)
    return stream.getvalue()


def rejected(action):
    try:
        action()
    except ValueError:
        return True
    raise AssertionError('Mismatched selection was accepted')


def sealed_fixture(project, number):
    name = f'exp{number:03d}'
    experiment = project / name
    evidence = experiment / 'evidence'
    evidence.mkdir(parents=True)
    qualification = publisher.dump({'passed': True, 'audits': number, 'source_sha256': '1' * 64})
    payload = {'evidence/FINAL_VERIFICATION.json': qualification,
               'lean/Example.lean': b'theorem accepted_fixture : True := by trivial\n'}
    manifest = publisher.dump({key: publisher.sha(value) for key, value in payload.items()})
    payload['PACKET_MANIFEST.json'] = manifest
    packet = project.parent / (name.capitalize() + '_fixture.zip')
    with zipfile.ZipFile(packet, 'w') as archive:
        for key, value in payload.items():
            archive.writestr(name + '/' + key, value)
    receipt = {'passed': True, 'archive': str(packet), 'archive_sha256': publisher.sha(packet.read_bytes()),
               'archive_bytes': packet.stat().st_size, 'manifest_sha256': publisher.sha(manifest),
               'manifest_entries': len(payload) - 1, 'verified_zip_files': len(payload)}
    packet_path = evidence / 'FINAL_PACKET_RECEIPT.json'
    qualification_path = evidence / 'FINAL_VERIFICATION.json'
    packet_path.write_bytes(publisher.dump(receipt))
    qualification_path.write_bytes(qualification)
    return experiment, packet, packet_path, qualification_path


def supplemental_cases(temporary, cases):
    project = temporary / 'NDEA_Evolve_offruntime'
    project.mkdir()
    exp13, packet13, receipt13, qualification13 = sealed_fixture(project, 13)
    assert publisher.select_supplemental_packets(project, 'exp013') == []
    selected = publisher.select_supplemental_packets(project, 'exp014')
    assert [row['experiment'] for row in selected] == ['exp013']
    assert selected[0]['verification']['payload_files_verified'] == 2
    cases['exp014_selection_includes_verified_exp013'] = True
    cases['missing_intermediate_experiment_rejected'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp015'))
    exp14, packet14, receipt14, qualification14 = sealed_fixture(project, 14)
    selected = publisher.select_supplemental_packets(project, 'exp015')
    assert [row['experiment'] for row in selected] == ['exp013', 'exp014']
    cases['all_intermediate_packets_selected_without_gaps'] = True
    packet_meta = receipt13.read_bytes()
    qualification_meta = qualification13.read_bytes()
    packet_data = packet13.read_bytes()
    receipt13.unlink()
    cases['missing_supplemental_packet_receipt_rejected'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp014'))
    receipt13.write_bytes(packet_meta)
    bad = json.loads(packet_meta)
    bad['passed'] = False
    receipt13.write_bytes(publisher.dump(bad))
    cases['unaccepted_supplemental_packet_rejected'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp014'))
    receipt13.write_bytes(packet_meta)
    bad = json.loads(qualification_meta)
    bad['passed'] = False
    qualification13.write_bytes(publisher.dump(bad))
    cases['unaccepted_supplemental_qualification_rejected'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp014'))
    qualification13.write_bytes(qualification_meta)
    packet13.write_bytes(packet_data + b'changed')
    cases['changed_supplemental_archive_rejected'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp014'))
    packet13.write_bytes(packet_data)
    with zipfile.ZipFile(io.BytesIO(packet_data)) as archive:
        members = {name: archive.read(name) for name in archive.namelist()}
    members['exp013/lean/Example.lean'] = b'changed proof payload with valid ZIP CRC\n'
    with zipfile.ZipFile(packet13, 'w') as archive:
        for name, data in members.items():
            archive.writestr(name, data)
    bad = json.loads(packet_meta)
    bad.update(archive_sha256=publisher.sha(packet13.read_bytes()), archive_bytes=packet13.stat().st_size)
    receipt13.write_bytes(publisher.dump(bad))
    cases['valid_crc_but_changed_supplemental_payload_rejected'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp014'))
    packet13.write_bytes(packet_data)
    receipt13.write_bytes(packet_meta)
    bad = json.loads(qualification_meta)
    bad['audits'] += 1
    qualification13.write_bytes(publisher.dump(bad))
    cases['external_qualification_must_match_embedded_accepted_bytes'] = rejected(
        lambda: publisher.select_supplemental_packets(project, 'exp014'))
    qualification13.write_bytes(qualification_meta)
    copies = temporary / 'copies'
    copies.mkdir()
    selected = publisher.select_supplemental_packets(project, 'exp015')
    for item in selected:
        publisher.copy_pinned(item['packet'], copies / item['copy_name'],
                              item['verification']['archive_sha256'])
        publisher.copy_frozen(copies / (item['experiment'] + '_receipt.json'),
                              item['packet_receipt_bytes'], item['packet_receipt_path'])
        publisher.copy_frozen(copies / (item['experiment'] + '_verification.json'),
                              item['qualification_bytes'], item['qualification_path'])
        assert (copies / (item['experiment'] + '_receipt.json')).read_bytes() == item['packet_receipt_path'].read_bytes()
        assert (copies / (item['experiment'] + '_verification.json')).read_bytes() == item['qualification_path'].read_bytes()
    publisher.validate_supplementals_unchanged(selected)
    cases['supplemental_archives_and_metadata_copied_exactly'] = True
    receipt13.write_bytes(packet_meta + b' ')
    cases['supplemental_receipt_changed_after_selection_rejected'] = rejected(
        lambda: publisher.validate_supplementals_unchanged(selected))
    receipt13.write_bytes(packet_meta)
    packet13.write_bytes(packet_data + b' ')
    cases['supplemental_archive_changed_after_selection_rejected'] = rejected(
        lambda: publisher.validate_supplementals_unchanged(selected))
    packet13.write_bytes(packet_data)
    return project


def publication_fixture(temporary, project, cases):
    """Exercise the full publisher in a temporary home, with stubbed older bundle verifiers."""
    recovery = temporary / 'NDEA_Recovery'
    recovery.mkdir()
    active, packet, packet_path, qualification_path = sealed_fixture(project, 15)
    state = {'active_experiment': 'exp015', 'recovery': {}}
    (recovery / 'TASK_STATE.json').write_bytes(publisher.dump(state))
    base = temporary / 'base.zip'
    base.write_bytes(zip_bytes('stand-in for separately tested base release bundle'))
    release = {'passed': True, 'archive': str(base), 'archive_sha256': publisher.sha(base.read_bytes())}
    (recovery / 'RELEASE_ARCHIVE_RECEIPT.json').write_bytes(publisher.dump(release))
    checkpoint_archive = temporary / 'checkpoint.zip'
    checkpoint_archive.write_bytes(zip_bytes('stand-in for separately tested checkpoint archive'))
    dated_path = recovery / 'dated.json'
    dated = {'archive': str(checkpoint_archive), 'archive_sha256': publisher.sha(checkpoint_archive.read_bytes())}
    dated_path.write_bytes(publisher.dump(dated))
    selected = {**dated, 'receipt': str(dated_path), 'receipt_sha256': publisher.sha(dated_path.read_bytes()),
                'active_experiment': 'exp015'}
    pointer = recovery / 'LATEST_CHECKPOINT.json'
    pointer.write_bytes(publisher.dump(selected))
    prefix = 'NDEA_Evolve_offruntime/exp015/evidence/'
    manifest = {'active_experiment': 'exp015', 'final_packet_receipt_captured': True,
                'files': {prefix + path.name: {'sha256': publisher.sha(path.read_bytes()),
                                             'bytes': len(path.read_bytes())}
                          for path in [packet_path, qualification_path]}}
    advanced = {**selected, 'archive': str(temporary / 'later-checkpoint.zip')}
    def check_checkpoint(path, digest):
        assert path == checkpoint_archive and publisher.sha(path.read_bytes()) == digest
        pointer.write_bytes(publisher.dump(advanced))
        return {'manifest': manifest}
    def check_releases(path, digest):
        assert path == base and publisher.sha(path.read_bytes()) == digest
        return {'passed': True}
    tools = {'checkpoint': SimpleNamespace(active_experiment=lambda _: active, verify_archive=check_checkpoint),
             'archive_releases': SimpleNamespace(verify_archive=check_releases)}
    for name in ['checkpoint.py', 'archive_releases.py', 'make_local_copy.py',
                 'START_HERE.md', 'RECOVERY_POLICY.md', 'RECOVERY_REVIEW.md']:
        (recovery / name).write_text('fixture preserved utility or note\n')
    (temporary / 'AGENTS.md').write_text('fixture startup instructions\n')
    original_root, original_home, original_loader = publisher.root, publisher.home, publisher.load_tool
    try:
        publisher.root, publisher.home = recovery, temporary
        publisher.load_tool = lambda name: tools[name]
        with contextlib.redirect_stdout(io.StringIO()):
            publisher.main()
    finally:
        publisher.root, publisher.home, publisher.load_tool = original_root, original_home, original_loader
    receipt = json.loads((recovery / 'LOCAL_BACKUP_RECEIPT.json').read_text())
    folder = Path(receipt['folder'])
    assert folder.parent == temporary / 'Downloads'
    assert receipt['completed_packet_coverage']['supplemental'] == ['exp013', 'exp014']
    assert receipt['completed_packet_coverage']['active'] == 'exp015'
    assert receipt['completed_packet_coverage']['contiguous'] is True
    backup_manifest = json.loads((folder / 'BACKUP_MANIFEST.json').read_text())
    for name, row in backup_manifest['files'].items():
        assert publisher.sha((folder / name).read_bytes()) == row['sha256']
    for number in [13, 14]:
        name = f'Exp{number:03d}'
        original = project / f'exp{number:03d}' / 'evidence'
        assert (folder / (name + '_PACKET_RECEIPT.json')).read_bytes() == (original / 'FINAL_PACKET_RECEIPT.json').read_bytes()
        assert (folder / (name + '_VERIFICATION.json')).read_bytes() == (original / 'FINAL_VERIFICATION.json').read_bytes()
        assert (folder / (name + '_Verified_Review_Packet.zip')).is_file()
    assert 'exp013, exp014' in (folder / 'README.txt').read_text()
    assert json.loads((folder / 'CHECKPOINT_RECEIPT.json').read_text()) == selected
    assert json.loads(pointer.read_text()) == advanced
    cases['full_temporary_publication_includes_gap_free_packets_receipts_and_readme'] = True
    cases['full_publication_preserves_moving_checkpoint_pointer_selection'] = True


def main():
    cases = {}
    with tempfile.TemporaryDirectory(prefix='local-copy-test-', dir=publisher.root) as temporary:
        root = Path(temporary)
        source = root / 'selected.zip'
        original = zip_bytes('selected verified archive')
        replacement = zip_bytes('later changed archive')
        source.write_bytes(original)
        digest = publisher.sha(original)
        row = publisher.copy_pinned(source, root / 'correct.zip', digest)
        assert row['sha256'] == digest
        assert (root / 'correct.zip').read_bytes() == source.read_bytes() == original
        cases['pinned_archive_copy_and_original_verified'] = True
        cases['archive_receipt_hash_mismatch_rejected'] = rejected(
            lambda: publisher.copy_pinned(source, root / 'bad-pin.zip', '0' * 64))
        assert not (root / 'bad-pin.zip').exists()
        source.write_bytes(replacement)
        cases['archive_changed_between_selection_and_copy_rejected'] = rejected(
            lambda: publisher.copy_pinned(source, root / 'changed.zip', digest))
        assert not (root / 'changed.zip').exists()
        source.write_bytes(original)
        later = root / 'later.zip'
        later.write_bytes(replacement)
        pointer = root / 'LATEST_CHECKPOINT.json'
        selected = {'archive': str(source), 'archive_sha256': digest, 'active_experiment': 'exp013'}
        pointer.write_bytes(publisher.dump(selected))
        frozen_bytes, frozen = publisher.frozen_json(pointer)
        advanced = {'archive': str(later), 'archive_sha256': publisher.sha(replacement),
                    'active_experiment': 'exp013'}
        pointer.write_bytes(publisher.dump(advanced))
        publisher.copy_pinned(Path(frozen['archive']), root / 'CURRENT_RECOVERY.zip', frozen['archive_sha256'])
        publisher.copy_frozen(root / 'CHECKPOINT_RECEIPT.json', frozen_bytes, pointer)
        copied = json.loads((root / 'CHECKPOINT_RECEIPT.json').read_text())
        assert copied == selected and json.loads(pointer.read_text()) == advanced
        assert copied['archive_sha256'] == publisher.sha((root / 'CURRENT_RECOVERY.zip').read_bytes())
        cases['watcher_pointer_advance_keeps_selected_archive_receipt_pair'] = True
        packet = publisher.dump({'passed': True, 'archive_sha256': digest})
        qualification = publisher.dump({'passed': True, 'audits': 64})
        prefix = 'NDEA_Evolve_offruntime/exp013/evidence/'
        manifest = {'active_experiment': 'exp013', 'final_packet_receipt_captured': True,
                    'files': {prefix + name: {'sha256': publisher.sha(data), 'bytes': len(data)}
                              for name, data in [('FINAL_PACKET_RECEIPT.json', packet),
                                                 ('FINAL_VERIFICATION.json', qualification)]}}
        checked = {'manifest': manifest}
        publisher.validate_checkpoint_binding(checked, selected, 'exp013', packet, qualification)
        cases['matching_active_sealed_receipts_accepted'] = True
        cases['wrong_active_experiment_rejected'] = rejected(
            lambda: publisher.validate_checkpoint_binding(checked, selected, 'exp012', packet, qualification))
        cases['stale_sealed_packet_receipt_rejected'] = rejected(
            lambda: publisher.validate_checkpoint_binding(checked, selected, 'exp013', packet + b' ', qualification))
        unfinished = copy.deepcopy(checked)
        unfinished['manifest']['final_packet_receipt_captured'] = False
        cases['preseal_checkpoint_rejected'] = rejected(
            lambda: publisher.validate_checkpoint_binding(unfinished, selected, 'exp013', packet, qualification))
        supplemental_home = root / 'supplemental-home'
        supplemental_home.mkdir()
        project = supplemental_cases(supplemental_home, cases)
        publication_fixture(supplemental_home, project, cases)
    report = {'passed': True, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'publisher_sha256': publisher.sha(Path(publisher.__file__).read_bytes()),
              'test_sha256': publisher.sha(Path(__file__).read_bytes()),
              'cases': cases, 'checks_passed': len(cases),
              'real_backup_published': False,
              'scope': 'Original eight pin/race regressions plus contiguous supplemental selection, complete sealed ZIP validation, mutated/missing/unaccepted evidence rejection, and full publication inside a temporary home. Older base/checkpoint verifiers are stubbed only in that integration fixture; supplemental validation is real. No real Downloads publication.'}
    target = publisher.root / 'LOCAL_COPY_TEST_RESULT.json'
    temporary = publisher.root / '.pending-local-copy-test.json'
    if temporary.exists():
        raise FileExistsError(temporary)
    publisher.write(temporary, publisher.dump(report))
    temporary.replace(target)
    publisher.sync_dir(publisher.root)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
