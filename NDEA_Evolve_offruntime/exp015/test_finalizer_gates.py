"""Exercise finalizer rejection gates in synthetic isolated copies; never seal a packet."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
checks = []


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def mutate_json(path, **changes):
    value = json.loads(path.read_text())
    value.update(changes)
    write_json(path, value)


def prepare_fixture(fixture):
    for directory in ['lean', 'evidence/local_combined', 'predecessor_sources',
                      'verification_tools', 'remote_check/downloaded_evidence/final_verification',
                      'fixture_output']:
        (fixture/directory).mkdir(parents=True, exist_ok=True)
    for name in ['make_combined.py', 'remote_check/check_download.py',
                 'predecessor_sources/Exp014Combined.lean', 'lean/Exp014Foundation.lean',
                 'verification_tools/verify_exp005.py']:
        shutil.copyfile(root/name, fixture/name)
    finalizer = (root/'finalize.py').read_text()
    anchor = "archive=Path('/home/richman954')/"
    if finalizer.count(anchor) != 1:
        raise RuntimeError('Finalizer archive destination fixture needs review')
    # Only relocate archive output. Every acceptance/rejection condition is unchanged.
    (fixture/'finalize.py').write_text(finalizer.replace(anchor, "archive=(root/'fixture_output')/"))
    spec = importlib.util.spec_from_file_location('exp015_finalizer_fixture_generator', fixture/'make_combined.py')
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    for name in generator.MODULES:
        (fixture/'lean'/(name+'.lean')).write_text(
            'import GenericClassical\nnamespace NDEAEvolve.Exp015\n'
            f'theorem fixture_{name} : True := by trivial\nend NDEAEvolve.Exp015\n')
    source, inputs = generator.build(fixture)
    (fixture/'lean/Exp015Combined.lean').write_text(source)
    write_json(fixture/'evidence/FINAL_INPUTS.json', inputs)
    local = fixture/'evidence/local_combined/RESULT.json'
    remote = fixture/'remote_check/downloaded_evidence/final_verification/RESULT.json'
    for path in [local, remote]:
        write_json(path, {'passed': True, 'fixture_only': True})
    evidence_archive = fixture/'remote_check/fixture_evidence.tar.gz'
    evidence_archive.write_bytes(b'Synthetic export checksum fixture; not proof evidence.\n')
    write_json(fixture/'remote_check/EXPORT_RECEIPT.json', {
        'archive': '/content/exp015_check/fixture_evidence.tar.gz', 'passed': True,
        'sha256': sha(evidence_archive), 'bytes': evidence_archive.stat().st_size,
        'payload_files': 1})
    write_json(fixture/'remote_check/FINAL_TRANSFER_CHECK.json', {
        'passed': True, 'fixture_only': True,
        'accepted_local_files': {'evidence/local_combined/RESULT.json': sha(local)},
        'accepted_independent_files': {'final_verification/RESULT.json': sha(remote)},
        'checker_sha256': sha(fixture/'remote_check/check_download.py'),
        'archive_sha256': sha(evidence_archive), 'verified_payload_files': 1,
        'bootstrap_verification': {'passed': True}, 'source_sha256': inputs['source_sha256']})
    (fixture/'REVIEW.md').write_text('Synthetic review fixture, not an accepted mathematical review.\n')
    documents = ['MATHEMATICAL_DERIVATION.md', 'REPRODUCE.md', 'SAVED_FILES.md', 'INFRASTRUCTURE_REVIEW.md']
    for name in documents:
        (fixture/name).write_text('Synthetic document fixture.\n')
    write_json(fixture/'evidence/REVIEW_CHECK.json', {
        'passed': True, 'fixture_only': True, 'current_source_hashes': inputs['source_hashes'],
        'public_catalog_total': len(inputs['expected_audits']), 'review_sha256': sha(fixture/'REVIEW.md'),
        'reviewed_tool_hashes': {'finalize.py': sha(fixture/'finalize.py')},
        'reviewed_document_hashes': {name: sha(fixture/name) for name in documents}})


cases = [
    ('sealed_manifest_rejected', lambda p: (p/'PACKET_MANIFEST.json').write_text('{}'), 'Packet or sealed manifest already exists'),
    ('unaccepted_transfer_rejected', lambda p: mutate_json(p/'remote_check/FINAL_TRANSFER_CHECK.json', passed=False), 'Unaccepted transfer check'),
    ('unaccepted_local_rejected', lambda p: mutate_json(p/'evidence/local_combined/RESULT.json', passed=False), 'Unaccepted local check'),
    ('unaccepted_independent_rejected', lambda p: mutate_json(p/'remote_check/downloaded_evidence/final_verification/RESULT.json', passed=False), 'Unaccepted independent check'),
    ('unbound_accepted_bytes_rejected', lambda p: mutate_json(p/'remote_check/FINAL_TRANSFER_CHECK.json', accepted_local_files={}), 'Receiving checker did not bind accepted evidence bytes'),
    ('changed_receiver_rejected', lambda p: mutate_json(p/'remote_check/FINAL_TRANSFER_CHECK.json', checker_sha256='0'*64), 'Receiving checker changed after acceptance'),
    ('unaccepted_export_rejected', lambda p: mutate_json(p/'remote_check/EXPORT_RECEIPT.json', passed=False), 'Export receipt/archive mismatch'),
    ('changed_export_archive_rejected', lambda p: (p/'remote_check/fixture_evidence.tar.gz').write_bytes(b'changed'), 'Export receipt/archive mismatch'),
    ('unaccepted_bootstrap_rejected', lambda p: mutate_json(p/'remote_check/FINAL_TRANSFER_CHECK.json', bootstrap_verification={'passed': False}), 'Fresh bootstrap was not accepted'),
    ('changed_bound_local_bytes_rejected', lambda p: mutate_json(p/'evidence/local_combined/RESULT.json', changed=True), 'Locally accepted evidence changed'),
    ('changed_bound_independent_bytes_rejected', lambda p: mutate_json(p/'remote_check/downloaded_evidence/final_verification/RESULT.json', changed=True), 'Independent accepted evidence changed'),
    ('changed_combined_source_rejected', lambda p: (p/'lean/Exp015Combined.lean').write_text('changed'), 'Final source changed'),
    ('unaccepted_review_rejected', lambda p: mutate_json(p/'evidence/REVIEW_CHECK.json', passed=False), 'Review does not cover the current proof/catalog'),
    ('changed_review_text_rejected', lambda p: (p/'REVIEW.md').write_text('changed'), 'Reviewed review/tool bytes changed'),
    ('changed_reviewed_tool_rejected', lambda p: mutate_json(p/'evidence/REVIEW_CHECK.json', reviewed_tool_hashes={'finalize.py': '0'*64}), 'Reviewed review/tool bytes changed'),
    ('unreviewed_finalizer_rejected', lambda p: mutate_json(p/'evidence/REVIEW_CHECK.json', reviewed_tool_hashes={}), 'Finalizer itself was not reviewed'),
    ('missing_document_review_rejected', lambda p: mutate_json(p/'evidence/REVIEW_CHECK.json', reviewed_document_hashes={}), 'Reviewed document coverage or bytes changed'),
    ('changed_reviewed_document_rejected', lambda p: (p/'REPRODUCE.md').write_text('changed'), 'Reviewed document coverage or bytes changed'),
    ('missing_modular_proof_rejected_after_other_fixture_gates', lambda p: None, 'No accepted modular check'),
]
with tempfile.TemporaryDirectory(prefix='exp015_finalizer_gates_') as temporary:
    for index, (label, mutation, expected_error) in enumerate(cases):
        fixture = Path(temporary)/str(index)
        prepare_fixture(fixture)
        mutation(fixture)
        before = {str(p.relative_to(fixture)): sha(p) for p in fixture.rglob('*') if p.is_file()}
        result = subprocess.run([sys.executable, '-B', str(fixture/'finalize.py')],
                                text=True, capture_output=True)
        after = {str(p.relative_to(fixture)): sha(p) for p in fixture.rglob('*') if p.is_file()}
        if result.returncode == 0 or expected_error not in result.stderr or before != after:
            raise RuntimeError('Finalizer rejection fixture failed: '+label+'\n'+result.stderr)
        checks.append(label)

record = {'passed': True, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'checks': checks, 'check_count': len(checks), 'finalizer_sha256': sha(root/'finalize.py'),
          'script_sha256': sha(Path(__file__)),
          'scope': 'Synthetic isolated copies exercise unchanged finalizer gates; only archive output '
                   'is relocated into the fixture. Every case rejects before any write, including a '
                   'fixture passing earlier protocol/review gates but lacking modular proof. No '
                   'packet is created and no synthetic input is accepted as proof evidence.'}
write_json(root/'evidence/FINALIZER_GATE_TESTS.json', record)
print(json.dumps(record))
