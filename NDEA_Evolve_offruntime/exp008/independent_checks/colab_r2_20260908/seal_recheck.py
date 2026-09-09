"""Qualify and seal the accepted second-VM recheck without changing old releases.

Run only after check_download.py succeeds, the predecessor checker writes the
new PREDECESSOR_PRESERVATION.json, and REPORT.md is complete. Outputs are created
exclusively. A failed packaging attempt is retained and is never overwritten.
"""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import stat
import sys
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DELIVERY_ROOT = ROOT.parent.parent
PACKET_NAME = 'Experiments_001-008_Fresh_VM_Recheck_20260908'
COMBINED_SHA = '5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0'
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
ORIGINAL_ARCHIVE_SHA = '8e2b429c161443901be17a585562af2ce5f920b44283044ba3e5f14bd99330a7'
ORIGINAL_MANIFEST_SHA = '537f3608ee3bdb96fadab042026ec722ec3c8957a1f0b1edf86be051b79ce4bd'
EXPECTED_PREDECESSORS = {
    'exp005_frozen': 889,
    'exp006_local_verified': 21,
    'exp006_final_packet': 99,
    'exp007_final_packet': 217,
}
EXCLUDED_DIRS = {'__pycache__', 'build', 'dependencies', 'cache', 'caches',
                 '.cache', 'cache_client', '.git', '.lake', '.pytest_cache', 'lib'}
EXCLUDED_SUFFIXES = {'.pyc', '.pyo', '.olean', '.ilean', '.ir', '.o', '.so'}
EXTERNAL_OUTPUTS = {'PACKET_MANIFEST.json', 'FINAL_PACKET_RECEIPT.json'}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    require(path.is_file() and not path.is_symlink(), 'Missing or nonregular file: ' + str(path))
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def exact_int(value, expected, message):
    require(type(value) is int and value == expected, message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object)


def json_bytes(value):
    return (json.dumps(value, indent=2, allow_nan=False) + '\n').encode()


def exclusive_write(path, value):
    with path.open('xb') as stream:
        stream.write(value)


def elapsed(value):
    require(type(value) in {int, float} and math.isfinite(value) and value >= 0,
            'Invalid compiler elapsed time')
    return value


def check_old_seal(receiver):
    baseline = read_json(HERE / 'SEALED_BASELINE.json')
    require(baseline.get('passed') is True, 'Original sealed baseline was not accepted')
    exact_int(baseline['payload_files_checked'], 254, 'Original baseline payload count differs')
    receipt = read_json(ROOT / 'evidence/FINAL_PACKET_RECEIPT.json')
    require(receipt == baseline['packet'] and receipt.get('passed') is True,
            'Original Experiment 008 packet receipt changed')
    exact_int(receipt['manifest_entries'], 254, 'Original packet manifest count differs')
    exact_int(receipt['verified_file_count'], 255, 'Original packet member count differs')
    manifest_path = ROOT / 'PACKET_MANIFEST.json'
    manifest_bytes = manifest_path.read_bytes()
    require(sha(manifest_bytes) == receipt['manifest_sha256'] == ORIGINAL_MANIFEST_SHA,
            'Original Experiment 008 manifest changed')
    manifest = read_json(manifest_path)
    receiver.valid_hashes(manifest, 'Original Experiment 008 payload')
    exact_int(len(manifest), 254, 'Original current payload count differs')
    for name, digest in manifest.items():
        require(sha_file(ROOT / name) == digest, 'Original sealed payload changed: ' + name)
    archive = Path(receipt['archive'])
    require(archive == DELIVERY_ROOT / 'Exp008_Verified_Review_Packet_20260908.zip',
            'Original sealed archive path differs')
    require(sha_file(archive) == receipt['archive_sha256'] == ORIGINAL_ARCHIVE_SHA,
            'Original Experiment 008 archive changed')
    exact_int(archive.stat().st_size, receipt['archive_bytes'], 'Original archive byte count differs')
    prefix = 'Exp008_Verified_Review_Packet_20260908/'
    with zipfile.ZipFile(archive) as packet:
        names = packet.namelist()
        require(len(names) == len(set(names)) == 255, 'Original archive duplicate/member count')
        require(set(names) == {prefix + name for name in manifest} | {prefix + 'PACKET_MANIFEST.json'},
                'Original archive member coverage differs')
        require(packet.testzip() is None, 'Original archive CRC failure')
        require(packet.read(prefix + 'PACKET_MANIFEST.json') == manifest_bytes,
                'Original archived manifest bytes differ')
        for name, digest in manifest.items():
            require(sha(packet.read(prefix + name)) == digest, 'Original archived payload differs: ' + name)
    return {'passed': True, 'baseline_sha256': sha_file(HERE / 'SEALED_BASELINE.json'),
            'archive': str(archive), 'archive_sha256': ORIGINAL_ARCHIVE_SHA,
            'manifest_sha256': ORIGINAL_MANIFEST_SHA, 'current_payload_hashes_verified': 254,
            'archive_members_verified': 255,
            'original_packet_receipt_sha256': sha_file(ROOT / 'evidence/FINAL_PACKET_RECEIPT.json')}


def check_predecessors(receiver):
    path = HERE / 'PREDECESSOR_PRESERVATION.json'
    record = read_json(path)
    require(record.get('passed') is True, 'New predecessor preservation check is incomplete')
    rows = record['checks']
    require(len(rows) == len(EXPECTED_PREDECESSORS) and
            {row['name'] for row in rows} == set(EXPECTED_PREDECESSORS),
            'Predecessor check coverage differs')
    accepted = {row['name']: row for row in read_json(ROOT / 'evidence/PREDECESSOR_PRESERVATION.json')['checks']}
    for row in rows:
        expected = EXPECTED_PREDECESSORS[row['name']]
        previous = accepted[row['name']]
        require(row.get('passed') is True and row['failures'] == [], 'A predecessor check failed')
        for key in ['expected_entry_count', 'entry_count', 'matched_entry_count']:
            exact_int(row[key], expected, 'Predecessor count differs: ' + row['name'])
        require(row['root'] == previous['root'] and row['manifest_path'] == previous['manifest_path'],
                'Predecessor source/manifest location differs')
        manifest_path = Path(row['manifest_path'])
        digest = sha_file(manifest_path)
        require(digest == row['expected_manifest_sha256'] == row['manifest_sha256_before'] ==
                row['manifest_sha256_after'] == previous['expected_manifest_sha256'],
                'Predecessor manifest identity differs')
        if manifest_path.suffix == '.json':
            parsed = read_json(manifest_path)
            entries = parsed.get('files', parsed)
        else:
            entries = {}
            for line in manifest_path.read_text().splitlines():
                if not line.strip():
                    continue
                value, name = line.split(maxsplit=1)
                name = name.removeprefix('*')
                require(name not in entries, 'Duplicate predecessor manifest entry')
                entries[name] = value
        receiver.valid_hashes(entries, 'Predecessor payload')
        exact_int(len(entries), expected, 'Predecessor actual entry count differs')
        for name, value in entries.items():
            require(sha_file(Path(row['root']) / name) == value, 'Predecessor payload changed: ' + name)
    return {'passed': True, 'receipt_sha256': sha_file(path),
            'start_utc': record['start_utc'], 'end_utc': record['end_utc'],
            'checks': [{'name': row['name'], 'entries_verified': row['entry_count'],
                        'manifest_sha256': row['manifest_sha256_after']} for row in rows]}


def select_payload():
    selected = {}
    for current, directories, names in os.walk(HERE, followlinks=False):
        directories[:] = sorted(name for name in directories
                                if name not in EXCLUDED_DIRS and not (Path(current) / name).is_symlink())
        for name in sorted(names):
            path = Path(current) / name
            relative = path.relative_to(HERE).as_posix()
            if relative in EXTERNAL_OUTPUTS or path.suffix in EXCLUDED_SUFFIXES:
                continue
            if not stat.S_ISREG(path.lstat().st_mode):
                continue
            selected[relative] = sha_file(path)
    return dict(sorted(selected.items()))


def main():
    archive = DELIVERY_ROOT / (PACKET_NAME + '.zip')
    checksum = archive.with_suffix('.zip.sha256')
    outputs = [HERE / 'FINAL_VERIFICATION.json', HERE / 'PACKET_MANIFEST.json',
               HERE / 'FINAL_PACKET_RECEIPT.json', archive, checksum]
    require(all(not path.exists() and not path.is_symlink() for path in outputs),
            'A qualification/packet output already exists; preserve the existing attempt')
    report_path = HERE / 'REPORT.md'
    require(report_path.is_file() and not report_path.is_symlink(), 'Completed REPORT.md is missing')
    require(report_path.read_text().strip() and not re.search(r'\bPENDING\b', report_path.read_text(), re.I),
            'REPORT.md is empty or still marked PENDING')
    transfer = read_json(HERE / 'FINAL_TRANSFER_CHECK.json')
    comparison = read_json(HERE / 'CROSS_ENVIRONMENT_COMPARISON.json')
    require(transfer.get('passed') is True and comparison.get('passed') is True,
            'Transfer or cross-environment comparison is incomplete')
    for key, value in [('sealed_source_audits', 90), ('retained_chain_public_audits', 332),
                       ('complete_unique_public_audits', 473), ('false_claims_rejected', 13)]:
        exact_int(transfer[key], value, 'Transferred verification count differs: ' + key)
    require(transfer['sealed_source_sha256'] == comparison['combined_sha256'] == COMBINED_SHA,
            'Transferred combined source identity differs')
    require(comparison.get('distinct_vm_allocation') is True and
            comparison['fresh_vm_id'] != comparison['previous_vm_id'], 'Fresh allocation not established')
    exact_int(comparison['new_dependency_artifact_count'], 9868, 'Exact-proof dependency count differs')
    require(comparison.get('historical_superset_matches_all_9868_final_artifacts') is True,
            'Historical/full proof library comparison incomplete')
    require(set(comparison['original_environments']) == {'original_local', 'original_independent'},
            'Original environment comparison coverage differs')
    for row in comparison['original_environments'].values():
        exact_int(row['identical_artifact_hashes'], 9868, 'Cross-environment hash count differs')
        require(row.get('same_source_and_90_audits') is True, 'Original proof comparison failed')

    receiving_path = HERE / 'check_download.py'
    require(sha_file(receiving_path) == transfer['receiving_checker_sha256'], 'Receiving checker changed')
    spec = importlib.util.spec_from_file_location('accepted_receiving_checker', receiving_path)
    receiver = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = receiver
    spec.loader.exec_module(receiver)
    evidence = HERE / 'downloaded_evidence/recheck_evidence'
    require(transfer['evidence_root'] == str(evidence) and evidence.is_dir() and not evidence.is_symlink(),
            'Accepted evidence directory differs or is missing')
    evidence_manifest = read_json(evidence / 'EVIDENCE_SHA256.json')
    receiver.valid_hashes(evidence_manifest, 'Received evidence manifest')
    require(sha_file(evidence / 'EVIDENCE_SHA256.json') == transfer['manifest_sha256'],
            'Received evidence manifest changed')
    exact_int(len(evidence_manifest), transfer['evidence_files_checked'], 'Received evidence count differs')
    for name, digest in evidence_manifest.items():
        require(sha_file(evidence / name) == digest, 'Accepted evidence file changed: ' + name)
    export = read_json(HERE / 'EXPORT_RECEIPT.json')
    require(export.get('passed') is True and export['archive_sha256'] == transfer['archive_sha256'] and
            export['manifest_sha256'] == transfer['manifest_sha256'], 'Export/transfer receipt differs')
    export_archive = HERE / Path(export['archive']).name
    require(sha_file(export_archive) == export['archive_sha256'], 'Downloaded evidence archive changed')
    exact_int(export_archive.stat().st_size, export['archive_bytes'], 'Downloaded evidence archive size differs')

    final_path = evidence / 'final_verification/RESULT.json'
    suite_path = evidence / 'historical_verification/RESULT.json'
    require(sha_file(final_path) == transfer['final_result_sha256'] and
            sha_file(suite_path) == transfer['suite_result_sha256'], 'Accepted result receipt changed')
    final, suite = read_json(final_path), read_json(suite_path)
    require(final.get('passed') is True and suite.get('passed') is True and
            final.get('reconstruction_verified') is True, 'Returned verification incomplete')
    exact_int(final['exit_code'], 0, 'Exact sealed proof compiler failed')
    require(final['compiler_sha256'] == suite['compiler_sha256'] == COMPILER_SHA,
            'Accepted compiler identities differ')
    require(final['source_sha256_before'] == final['source_sha256_after'] == COMBINED_SHA ==
            sha_file(ROOT / 'lean/Exp008Combined.lean') ==
            sha_file(evidence / 'final_source/lean/Exp008Combined.lean'), 'Accepted exact source changed')
    final_inputs = read_json(ROOT / 'evidence/FINAL_INPUTS.json')
    require(final_inputs['source_sha256'] == COMBINED_SHA and
            final['source_hashes'] == final_inputs['source_hashes'], 'Accepted source-module catalog differs')
    for name, digest in final_inputs['source_hashes'].items():
        require(sha_file(ROOT / name) == digest == sha_file(evidence / 'final_source' / name),
                'Accepted source module changed: ' + name)
    final_upload = read_json(HERE / 'reused_inputs/FINAL_UPLOAD.json')
    require(read_json(evidence / 'FINAL_UPLOAD.json') == final_upload, 'Returned final upload request changed')
    for name, digest in final_upload['files'].items():
        require(sha_file(ROOT / name) == digest == sha_file(evidence / 'final_source' / name),
                'Accepted final verification input changed: ' + name)
    require(sha_file(HERE / 'reused_inputs' / Path(final_upload['archive']).name) == final_upload['sha256'],
            'Uploaded final source archive changed')
    require(final['runner_sha256'] == final_upload['files']['verify_combined.py'] == sha_file(ROOT / 'verify_combined.py'),
            'Exact proof runner identity differs')
    require(sha_file(final_path.parent / 'combined.log') == final['log_sha256'], 'Exact proof log changed')
    final_audits = receiver.parsed_axioms((final_path.parent / 'combined.log').read_text(),
                                        final_inputs['expected_audits'])
    exact_int(len(final_audits), 90, 'Exact proof audit coverage differs')
    require(final_audits == final['axiom_audits'], 'Exact proof reported audits differ from the log')

    suite_upload = read_json(HERE / 'SUITE_UPLOAD.json')
    inputs = read_json(HERE / 'SUITE_INPUTS.json')
    require(read_json(evidence / 'SUITE_UPLOAD.json') == suite_upload and
            read_json(evidence / 'historical_source/SUITE_INPUTS.json') == inputs,
            'Returned suite upload/catalog differs')
    require(sha_file(HERE / Path(suite_upload['archive']).name) == suite_upload['sha256'],
            'Uploaded suite archive changed')
    for name, digest in suite_upload['files'].items():
        require(sha_file(HERE / 'suite_payload' / name) == digest ==
                sha_file(evidence / 'historical_source' / name), 'Pinned suite input changed: ' + name)
        if name.startswith('historical_inputs/') or name in {
                'ALL_PUBLIC_THEOREMS.json', 'ADDITIONAL_AXIOM_PRINTS.lean.txt', 'build_audit_inventory.py'}:
            require(sha_file(HERE / name) == digest, 'Current suite original changed: ' + name)
    require(suite['source_hashes'] == inputs['source_files'] and
            suite['inputs_sha256'] == sha_file(HERE / 'SUITE_INPUTS.json'), 'Suite executed catalog differs')
    require(suite['runner_sha256'] == suite_upload['runner_sha256'] == sha_file(HERE / 'verify_suite.py') ==
            sha_file(evidence / 'verify_suite.py'), 'Historical proof runner changed')
    require(final['dependency_pins'] == suite['dependency_pins'], 'Independent dependency revisions differ')
    for path, row in [(final_path, final), (suite_path, suite)]:
        require(sha_file(path.parent / 'DEPENDENCY_ARTIFACTS.json') == row['dependency_manifest_sha256'],
                'Accepted library manifest changed')

    cases, results = inputs['checks'], suite['checks']
    require(len(cases) == len(results) == 9 and
            [row['name'] for row in cases] == [row['name'] for row in results] and
            len({row['name'] for row in cases}) == 9, 'Independent suite check coverage differs')
    positive_names = [name for case in cases if case['expectation'] == 'pass' for name in case['expected_audits']]
    require(len(positive_names) == len(set(positive_names)) == inputs['public_audits'] == 473,
            'Public audit union/uniqueness differs')
    require(set(final_inputs['expected_audits']) <= set(positive_names), 'Suite omits a sealed theorem audit')
    positive, rejected = [], []
    for case, row in zip(cases, results):
        require(row.get('passed') is True and row['expectation'] == case['expectation'] and row['file'] == case['file'],
                'Historical check not accepted: ' + case['name'])
        source_path = evidence / 'historical_source' / case['file']
        require(sha_file(source_path) == case['source_sha256'] == row['source_sha256_before'] == row['source_sha256_after'],
                'Historical accepted source changed')
        receiver.check_command(row['command'], 'historical_source/' + case['file'])
        log_path = suite_path.parent / (case['name'] + '.log')
        require(sha_file(log_path) == row['log_sha256'], 'Historical accepted compiler log changed')
        text = log_path.read_text()
        duration = elapsed(row['elapsed_seconds'])
        if case['expectation'] == 'pass':
            exact_int(row['exit_code'], 0, 'Historical positive source failed')
            audited = receiver.parsed_axioms(text, case['expected_audits'])
            require(audited == row['axiom_audits'] and row['errors'] == [], 'Historical positive audit report differs')
            positive.append({'name': case['name'], 'audits': len(audited), 'source_sha256': case['source_sha256'],
                             'log_sha256': row['log_sha256'], 'elapsed_seconds': duration})
        elif case['expectation'] == 'reject':
            exact_int(row['exit_code'], 1, 'Historical rejection did not exit normally with code 1')
            errors = receiver.ERROR.findall(text)
            exact_int(len(errors), case['expected_error_count'], 'Historical rejection count differs')
            require([int(error[1]) for error in errors] == case['expected_error_lines'], 'Historical rejection locations differ')
            require(receiver.IMPORT_FAILURE.search(text) is None and
                    all(fragment in text for fragment in case['expected_diagnostic_fragments']),
                    'Historical rejection reason differs')
            require(case['expected_audits'] == [] and row['axiom_audits'] == {} and
                    not receiver.AXIOMS.findall(text) and not receiver.NO_AXIOMS.findall(text),
                    'Historical rejection claims theorem acceptance')
            parsed = []
            for path, line, column, message in errors:
                require(path == str(receiver.REMOTE_ROOT / 'historical_source' / case['file']) and
                        any(lo <= int(line) <= hi for lo, hi in case['error_line_ranges']) and
                        any(re.search(pattern, message) for pattern in case['allowed_diagnostic_patterns']),
                        'Historical rejection diagnostic differs from its exact control')
                parsed.append({'file': path, 'line': int(line), 'column': int(column), 'message': message})
            require(row['errors'] == parsed, 'Historical rejection report differs from its log')
            rejected.append({'name': case['name'], 'errors': len(errors), 'source_sha256': case['source_sha256'],
                             'log_sha256': row['log_sha256'], 'elapsed_seconds': duration})
        else:
            raise RuntimeError('Unknown historical expectation')
    require(len(positive) == 3 and len(rejected) == 6 and sum(row['errors'] for row in rejected) == 13,
            'Positive/rejection suite totals differ')
    require(positive == transfer['positive_checks'] and rejected == transfer['expected_rejection_checks'],
            'Transfer counters, source/log identities, or timings differ')
    numeric = transfer.get('numeric_recheck')
    require(isinstance(numeric, dict) and numeric.get('passed') is True, 'Required numerical recheck missing')
    if numeric is not None:
        require(numeric.get('passed') is True, 'Fresh numerical recheck is incomplete')
        numeric_path = final_path.parent / 'NUMERICAL_RESULT.json'
        numeric_result = read_json(numeric_path)
        require(numeric_result.get('passed') is True and
                sha_file(numeric_path) == numeric['result_sha256'], 'Fresh numerical receipt differs')
        exact_int(numeric_result['exit_code'], 0, 'Fresh numerical diagnostics failed')
        require(numeric['source_sha256'] == numeric_result['source_sha256_before'] ==
                numeric_result['source_sha256_after'] == sha_file(ROOT / 'numerical_checks.py') ==
                sha_file(HERE / 'numerical_checks.py') == sha_file(final_path.parent / 'numerical_checks.py'),
                'Fresh numerical source identity differs')
        require(sha_file(final_path.parent / 'numerical.log') == numeric['log_sha256'] ==
                numeric_result['log_sha256'] and
                sha_file(final_path.parent / 'evidence/numerical_checks.json') == numeric['data_sha256'] ==
                numeric_result['data_sha256'], 'Fresh numerical evidence hashes differ')
        data = read_json(final_path.parent / 'evidence/numerical_checks.json')
        counts = {'stage_checks': 60, 'global_checks': 20, 'joint_refinement': 7,
                  'temporal_refinement': 6, 'lie_refinement': 6}
        require(numeric['case_counts'] == counts, 'Fresh numerical count catalog differs')
        for key, count in counts.items():
            exact_int(len(data[key]), count, 'Fresh numerical case count differs: ' + key)
        orders = {key: data[key][-1]['observed_order'] for key in
                  ['joint_refinement', 'temporal_refinement', 'lie_refinement']}
        require(numeric['finest_observed_orders'] == orders and
                orders['joint_refinement'] > 1.99 and orders['temporal_refinement'] > 1.99 and
                0.97 < orders['lie_refinement'] < 1.03, 'Fresh numerical order summary differs')
        require(numeric['aliasing_detected'] is True and data['controls']['aliasing_detected'] is True,
                'Fresh numerical aliasing summary differs')
        require(elapsed(numeric_result['elapsed_seconds']) == elapsed(numeric['elapsed_seconds']),
                'Fresh numerical elapsed time differs')
    original = check_old_seal(receiver)
    predecessors = check_predecessors(receiver)
    start = datetime.now(timezone.utc).isoformat()
    report_hash = sha_file(report_path)
    qualification = {
        'passed': True, 'qualified_utc': start, 'scope': 'Additional independently allocated Colab CPU proof recheck through Experiments 001–008.',
        'sealed_source_sha256': COMBINED_SHA, 'sealed_source_audits': 90,
        'retained_chain_public_audits': 332, 'additional_public_audits': 141,
        'complete_unique_public_audits': 473, 'false_claims_rejected': 13,
        'anonymous_exp001_examples_checked': 4, 'compiler_sha256': COMPILER_SHA,
        'dependency_pins': final['dependency_pins'], 'source_hashes': final_inputs['source_hashes'],
        'fresh_vm_id': comparison['fresh_vm_id'], 'previous_vm_id': comparison['previous_vm_id'],
        'distinct_vm_allocation': True,
        'final_result': str(final_path.relative_to(HERE)), 'final_result_sha256': sha_file(final_path),
        'suite_result': str(suite_path.relative_to(HERE)), 'suite_result_sha256': sha_file(suite_path),
        'exact_check': {'start_utc': final['start_utc'], 'end_utc': final['end_utc'],
                        'elapsed_seconds': elapsed(final['elapsed_seconds']), 'log_sha256': final['log_sha256']},
        'suite_start_utc': suite['start_utc'], 'suite_end_utc': suite['end_utc'],
        'suite_compiler_elapsed_seconds': sum(row['elapsed_seconds'] for row in positive + rejected),
        'positive_checks': positive, 'expected_rejection_checks': rejected,
        'numeric_recheck': numeric,
        'transfer_utc': transfer['utc'], 'evidence_files_checked': transfer['evidence_files_checked'],
        'bootstrap_commands_verified': transfer['bootstrap_commands_verified'],
        'evidence_archive': str(export_archive.relative_to(HERE)), 'evidence_archive_sha256': transfer['archive_sha256'],
        'evidence_manifest_sha256': transfer['manifest_sha256'],
        'final_transfer_check_sha256': sha_file(HERE / 'FINAL_TRANSFER_CHECK.json'),
        'cross_environment_comparison_sha256': sha_file(HERE / 'CROSS_ENVIRONMENT_COMPARISON.json'),
        'original_exp008_preservation': original, 'predecessor_preservation': predecessors,
        'final_upload_sha256': sha_file(HERE / 'reused_inputs/FINAL_UPLOAD.json'),
        'suite_upload_sha256': sha_file(HERE / 'SUITE_UPLOAD.json'),
        'suite_inputs_sha256': sha_file(HERE / 'SUITE_INPUTS.json'),
        'checker_sha256': {'receiving_checker': sha_file(receiving_path),
                           'exact_runner': final['runner_sha256'], 'suite_runner': suite['runner_sha256'],
                           'predecessor_checker': sha_file(ROOT / 'check_predecessors.py'),
                           'sealing_checker': sha_file(Path(__file__))},
        'report_sha256': report_hash,
        'qualification': 'Accepted compiler logs and source/evidence hashes were checked again before packaging. '
                         'The second VM uses independently downloaded compatible libraries, which remain trusted inputs; '
                         'Lean and Mathlib were not rebuilt from source. The required numeric_recheck records '
                         'fresh execution of the unchanged Experiment 008 diagnostics. Earlier numerical and '
                         'validator suites are preserved without a claim that they were rerun.'}
    exclusive_write(HERE / 'FINAL_VERIFICATION.json', json_bytes(qualification))
    payload = select_payload()
    require('FINAL_VERIFICATION.json' in payload and payload['REPORT.md'] == report_hash,
            'Qualification or completed report not selected')
    manifest_bytes = json_bytes(payload)
    manifest_path = HERE / 'PACKET_MANIFEST.json'
    exclusive_write(manifest_path, manifest_bytes)
    require(manifest_path.read_bytes() == manifest_bytes, 'Manifest bytes differ before packaging')
    prefix = PACKET_NAME + '/'
    with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as packet:
        for name in payload:
            packet.write(HERE / name, prefix + name)
        packet.write(manifest_path, prefix + 'PACKET_MANIFEST.json')
    with zipfile.ZipFile(archive) as packet:
        names = packet.namelist()
        require(len(names) == len(set(names)) == len(payload) + 1, 'New archive duplicate/member count')
        require(set(names) == {prefix + name for name in payload} | {prefix + 'PACKET_MANIFEST.json'},
                'New archive member coverage differs')
        require(packet.testzip() is None, 'New archive CRC failure')
        require(packet.read(prefix + 'PACKET_MANIFEST.json') == manifest_bytes, 'Packaged manifest bytes differ')
        for name, digest in payload.items():
            require(sha(packet.read(prefix + name)) == digest, 'Packaged payload hash differs: ' + name)
    require(select_payload() == payload, 'Packet source coverage or hashes changed during packaging')
    require(manifest_path.read_bytes() == manifest_bytes, 'Manifest changed during packaging')
    require(check_old_seal(receiver) == original, 'Original Experiment 008 changed during packaging')
    require(check_predecessors(receiver) == predecessors, 'Predecessors changed during packaging')
    receipt = {'passed': True, 'sealed_utc': datetime.now(timezone.utc).isoformat(),
               'archive': str(archive), 'archive_sha256': sha_file(archive),
               'archive_bytes': archive.stat().st_size, 'manifest_entries': len(payload),
               'manifest_sha256': sha(manifest_bytes), 'verified_file_count': len(payload) + 1,
               'final_verification_sha256': payload['FINAL_VERIFICATION.json'],
               'report_sha256': report_hash, 'sealed_source_sha256': COMBINED_SHA,
               'complete_unique_public_audits': 473, 'false_claims_rejected': 13,
               'original_exp008_payload_preserved': 254,
               'qualification': 'Every archive member, SHA-256, exact manifest byte, and CRC was checked. '
                                'The packet receipt and neighboring ZIP checksum remain outside the archive '
                                'to avoid a self-hash cycle. Earlier archives were preserved.'}
    exclusive_write(HERE / 'FINAL_PACKET_RECEIPT.json', json_bytes(receipt))
    exclusive_write(checksum, (receipt['archive_sha256'] + '  ' + archive.name + '\n').encode())
    print(json.dumps(receipt, indent=2, allow_nan=False))


if __name__ == '__main__':
    main()
