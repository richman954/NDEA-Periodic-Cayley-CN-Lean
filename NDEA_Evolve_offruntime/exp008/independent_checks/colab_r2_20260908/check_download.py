"""Validate the fresh-VM evidence transfer before extracting any file.

This receiving check reparses the compiler logs and verifies source, runner,
launch, library, allocation, and archive identities. It does not run Lean.
All output is confined to this new r2 evidence directory.
"""
from datetime import datetime, timezone
import ast
import hashlib
import importlib.util
import json
import math
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REMOTE_ROOT = PurePosixPath('/content/exp008_check')
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
COMBINED_SHA = '5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ERROR = re.compile(r'^(.+):(\d+):(\d+): error: ([^\n]*)', re.M)
AXIOMS = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")
IMPORT_FAILURE = re.compile(
    r'unknown module prefix|unknown module|object file .+ does not exist|'
    r'failed to (?:load|import)|unknown identifier|failed to synthesize|'
    r'no such file or directory|permission denied|'
    r'command not found|invalid option|unrecognized option|segmentation fault|'
    r'out of memory|maximum (?:recursion depth|number of heartbeats)|PANIC', re.I)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    return sha(path.read_bytes())


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def parse_json(data):
    return json.loads(data, object_pairs_hook=unique_object)


def read_json(path):
    return parse_json(path.read_bytes())


def safe_relative(name):
    require(isinstance(name, str) and name and '\\' not in name, 'Invalid relative path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and all(part not in {'', '.', '..'} for part in name.split('/')),
            'Unsafe relative path: ' + name)
    require(str(path) == name, 'Noncanonical relative path: ' + name)
    return path


def read_archive(path, prefix=None):
    files = {}
    with tarfile.open(path) as archive:
        for member in archive.getmembers():
            require(member.isfile() and not member.issym() and not member.islnk(),
                    'Nonregular archive member: ' + member.name)
            member_path = safe_relative(member.name)
            if prefix is not None:
                require(len(member_path.parts) > 1 and member_path.parts[0] == prefix,
                        'Unexpected archive prefix: ' + member.name)
                name = str(PurePosixPath(*member_path.parts[1:]))
            else:
                name = member.name
            require(name not in files, 'Duplicate archive member: ' + name)
            stream = archive.extractfile(member)
            require(stream is not None, 'Unreadable archive member: ' + name)
            files[name] = stream.read()
    for name in files:
        for parent in PurePosixPath(name).parents:
            require(str(parent) not in files, 'File/directory collision: ' + name)
    return files


def file_member(remote_path):
    path = PurePosixPath(remote_path)
    require(path.is_relative_to(REMOTE_ROOT), 'Unexpected remote path: ' + remote_path)
    return str(path.relative_to(REMOTE_ROOT))


def valid_hashes(mapping, label):
    require(isinstance(mapping, dict) and bool(mapping), label + ': empty hash mapping')
    for name, digest in mapping.items():
        safe_relative(name)
        require(isinstance(digest, str) and re.fullmatch(r'[0-9a-f]{64}', digest),
                label + ': malformed digest for ' + name)


def parsed_axioms(text, expected):
    require(expected and len(expected) == len(set(expected)), 'Empty or duplicate expected audit names')
    require(not re.search(r'\berror:|\bsorryAx\b|declaration uses .sorry.', text),
            'Positive compiler log contains an error or placeholder')
    rows = AXIOMS.findall(text) + [(name, '') for name in NO_AXIOMS.findall(text)]
    audit = {}
    for name, raw in rows:
        require(name not in audit, 'Duplicate compiler axiom row: ' + name)
        values = [part.strip() for part in raw.split(',') if part.strip()]
        require(len(values) == len(set(values)) and set(values) <= ALLOWED_AXIOMS,
                'Unexpected or duplicate axioms for ' + name)
        audit[name] = sorted(values)
    require(set(audit) == set(expected), 'Compiler audit coverage mismatch')
    return audit


def check_command(command, source):
    require(isinstance(command, list) and len(command) == 4 and command[1:3] == ['-j', '1'],
            'Unexpected Lean command shape')
    require(command[0] == str(REMOTE_ROOT / 'lean-4.31.0-linux/bin/lean') and
            command[-1] == str(REMOTE_ROOT / source), 'Lean command source/compiler mismatch')


def exact_int(value, expected, label):
    require(type(value) is int and value == expected, label)


def main():
    receipt = read_json(HERE / 'EXPORT_RECEIPT.json')
    archive_path = HERE / PurePosixPath(receipt['archive']).name
    require(sha_file(archive_path) == receipt['archive_sha256'], 'Evidence archive SHA mismatch')
    files = read_archive(archive_path, 'recheck_evidence')
    manifest_bytes = files['EVIDENCE_SHA256.json']
    manifest = parse_json(manifest_bytes)
    valid_hashes(manifest, 'Evidence manifest')
    require(sha(manifest_bytes) == receipt['manifest_sha256'], 'Evidence manifest SHA mismatch')
    require(set(manifest) == set(files) - {'EVIDENCE_SHA256.json'}, 'Evidence manifest coverage mismatch')
    exact_int(receipt['files'], len(manifest), 'Evidence receipt file count mismatch')
    for name, digest in manifest.items():
        require(sha(files[name]) == digest, 'Evidence file hash mismatch: ' + name)

    def exported_json(name):
        return parse_json(files[name])

    # The receiving side pins both uploaded archives and every archived input.
    reused = read_json(HERE / 'REUSED_INPUTS.json')
    for original, item in reused.items():
        require(sha_file(HERE / item['copied_as']) == item['sha256'] == sha_file(ROOT / original),
                'Reused source input changed: ' + original)
        basename = PurePosixPath(original).name
        if basename.endswith('.py') or basename == 'FINAL_UPLOAD.json':
            require(sha(files[basename]) == item['sha256'], 'Exported reused tool/input differs: ' + basename)

    tools_upload = read_json(HERE / 'TOOLS_UPLOAD.json')
    tools_archive = HERE / PurePosixPath(tools_upload['archive']).name
    require(sha_file(tools_archive) == tools_upload['sha256'], 'Uploaded tool archive SHA differs')
    tool_payload = read_archive(tools_archive)
    require(set(tool_payload) == set(tools_upload['files']), 'Uploaded tool catalog coverage differs')
    for name, digest in tools_upload['files'].items():
        current = HERE / name
        if not current.is_file():
            current = HERE / 'reused_inputs' / name
        require(sha(tool_payload[name]) == digest == sha_file(current) and files[name] == tool_payload[name],
                'Uploaded/exported/current execution tool differs: ' + name)

    upload = read_json(HERE / 'reused_inputs/FINAL_UPLOAD.json')
    require(exported_json('FINAL_UPLOAD.json') == upload, 'Remote final upload request differs')
    final_archive_path = HERE / 'reused_inputs' / PurePosixPath(upload['archive']).name
    require(sha_file(final_archive_path) == upload['sha256'], 'Final upload archive changed')
    final_payload = read_archive(final_archive_path)
    require(parse_json(final_payload['FINAL_TRANSFER_INPUTS.json']) == upload['files'],
            'Final upload manifest differs from request')
    require(set(final_payload) == set(upload['files']) | {'FINAL_TRANSFER_INPUTS.json'},
            'Final upload payload coverage mismatch')
    for name, data in final_payload.items():
        require(files['final_source/' + name] == data, 'Returned final source/input differs: ' + name)
        if name in upload['files']:
            require(sha(data) == upload['files'][name] == sha_file(ROOT / name),
                    'Final input differs from current sealed input: ' + name)

    inputs = read_json(ROOT / 'evidence/FINAL_INPUTS.json')
    require(exported_json('final_source/evidence/FINAL_INPUTS.json') == inputs,
            'Returned sealed source catalog differs')
    source = files['final_source/lean/Exp008Combined.lean']
    require(sha(source) == COMBINED_SHA == inputs['source_sha256'] == upload['combined_sha256'],
            'Sealed combined source pin mismatch')
    result = exported_json('final_verification/RESULT.json')
    require(result.get('passed') is True and result.get('reconstruction_verified') is True,
            'Final exact sealed source check incomplete')
    exact_int(result['exit_code'], 0, 'Final exact source compiler failed')
    require(result['source_sha256_before'] == result['source_sha256_after'] == COMBINED_SHA and
            result['source_hashes'] == inputs['source_hashes'], 'Final source identities differ')
    require(result['compiler_sha256'] == COMPILER_SHA and
            result['runner_sha256'] == upload['files']['verify_combined.py'],
            'Final compiler or runner pin differs')
    check_command(result['command'], 'final_source/lean/Exp008Combined.lean')
    expected_path = str(REMOTE_ROOT / 'final_verification/dependencies') + ':' + str(
        REMOTE_ROOT / 'lean-4.31.0-linux/lib/lean')
    require(result['lean_path'] == expected_path, 'Final import path differs or includes project artifacts')
    launch = exported_json('FINAL_LAUNCH.json')
    require(launch['runner_sha256'] == result['runner_sha256'] and
            launch['source_archive_sha256'] == upload['sha256'] and
            launch['combined_sha256'] == COMBINED_SHA, 'Final launch pins differ')
    require(launch['command'][1:3] == ['-u', '-B'] and
            launch['command'][3] == str(REMOTE_ROOT / 'final_source/verify_combined.py'),
            'Final launched runner differs')
    log = files['final_verification/combined.log']
    require(sha(log) == result['log_sha256'], 'Final compiler log SHA differs')
    exact_int(len(inputs['expected_audits']), 90, 'Sealed final catalog no longer has 90 audits')
    final_audits = parsed_axioms(log.decode(), inputs['expected_audits'])
    require(final_audits == result['axiom_audits'], 'Final reported audits differ from compiler log')

    # Compare the entire dependency manifest, not just its size or selected files.
    dependency_bytes = files['final_verification/DEPENDENCY_ARTIFACTS.json']
    dependencies = parse_json(dependency_bytes)
    valid_hashes(dependencies, 'Final dependency artifacts')
    require(sha(dependency_bytes) == result['dependency_manifest_sha256'], 'Final dependency manifest SHA differs')
    exact_int(result['dependency_artifacts'], 9868, 'Final dependency receipt count differs')
    exact_int(len(dependencies), 9868, 'Final dependency manifest count differs')
    old_environments = {
        'original_local': ROOT / 'evidence/local_combined',
        'original_independent': ROOT / 'remote_check/downloaded_evidence/exp008_independent_evidence/final_verification',
    }
    comparisons = {}
    for label, path in old_environments.items():
        old_result = read_json(path / 'RESULT.json')
        old_bytes = (path / 'DEPENDENCY_ARTIFACTS.json').read_bytes()
        old_log = (path / 'combined.log').read_bytes()
        require(old_result.get('passed') is True and type(old_result['exit_code']) is int and old_result['exit_code'] == 0,
                label + ': old final result not accepted')
        require(old_result['source_sha256_before'] == old_result['source_sha256_after'] == COMBINED_SHA,
                label + ': old checked source identity differs')
        require(sha(old_bytes) == old_result['dependency_manifest_sha256'] and
                parse_json(old_bytes) == dependencies, label + ': dependency artifact hashes differ')
        require(sha(old_log) == old_result['log_sha256'] and
                parsed_axioms(old_log.decode(), inputs['expected_audits']) == old_result['axiom_audits'] == final_audits,
                label + ': old compiler audits differ')
        comparisons[label] = {'result_sha256': sha_file(path / 'RESULT.json'),
                              'dependency_manifest_sha256': sha(old_bytes),
                              'identical_artifact_hashes': len(dependencies),
                              'same_source_and_90_audits': True}

    # Fresh allocation and bootstrap are evidenced separately from theorem checks.
    fresh = read_json(HERE / 'FRESH_VM.json')
    allocation = read_json(HERE / 'VM_ALLOCATION.json')
    require(files['FRESH_VM.json'] == (HERE / 'FRESH_VM.json').read_bytes(), 'Returned fresh-VM record differs')
    require(fresh.get('passed') is True and fresh.get('fresh_root') is True and fresh['prior_project_paths'] == [],
            'Fresh-VM initialization did not start from an empty project root')
    require(allocation.get('distinct_allocation') is True and allocation['vm_id'] != allocation['previous_vm_id'] and
            allocation['session'] == fresh['session'] and allocation['hardware'] == 'CPU',
            'Fresh VM allocation identity differs or is not distinct')
    bootstrap_payload = read_archive(HERE / 'reused_inputs/bootstrap_inputs.tar.gz')
    for name, data in bootstrap_payload.items():
        require(files['inputs/' + name] == data, 'Bootstrap returned input differs: ' + name)
    bootstrap = exported_json('bootstrap/RESULT.json')
    bootstrap_inputs = parse_json(bootstrap_payload['INPUT_HASHES.json'])
    require(bootstrap.get('passed') is True and bootstrap['compiler_sha256'] == COMPILER_SHA,
            'Bootstrap did not complete with the pinned compiler')
    require(bootstrap['input_hashes'] == bootstrap_inputs, 'Bootstrap input catalog differs')
    for name, digest in bootstrap_inputs.items():
        require(sha(bootstrap_payload[name]) == digest, 'Bootstrap helper/input pin mismatch: ' + name)
    pins = parse_json(bootstrap_payload['lake-manifest.json'])['packages']
    require(bootstrap['dependency_pins'] == result['dependency_pins'] == pins,
            'Bootstrap/final dependency source revisions differ')
    require(isinstance(bootstrap['commands'], list) and bootstrap['commands'], 'Bootstrap has no completed commands')
    seen_logs = set()
    for command in bootstrap['commands']:
        exact_int(command['exit_code'], 0, 'Bootstrap command failed: ' + command['label'])
        member = file_member(command['log'])
        require(member.startswith('bootstrap/') and member not in seen_logs, 'Bootstrap log path is invalid/duplicate')
        seen_logs.add(member)
        require(sha(files[member]) == command['log_sha256'], 'Bootstrap command log SHA mismatch: ' + member)

    # This run uses the new full-cache fetcher; the preserved old targeted-cache
    # script is historical input and is not identified as the executed fetcher.
    require(files['start_full_cache.py'] == (HERE / 'start_full_cache.py').read_bytes(),
            'Executed full-cache launcher copy differs')
    launcher_ast = ast.parse(files['start_full_cache.py'].decode())
    job_literals = [ast.literal_eval(node.value) for node in launcher_ast.body if isinstance(node, ast.Assign)
                    and any(isinstance(target, ast.Name) and target.id == 'code' for target in node.targets)]
    require(len(job_literals) == 1 and files['fetch_extra_imports.py'] == job_literals[0].encode(),
            'Full-cache executed job differs from the pinned launcher body')
    extra = exported_json('EXTRA_IMPORTS.json')
    exact_int(extra['exit_code'], 0, 'Full historical dependency cache fetch failed')
    require(extra['modules'] == ['Mathlib'] and extra['command'] == [
        str(REMOTE_ROOT / 'lean-4.31.0-linux/bin/lean'), '-j', '1', '--run',
        str(REMOTE_ROOT / 'mathlib/Cache/Main.lean'), 'get', 'Mathlib'],
        'Full historical cache fetch command differs')
    require(sha(files['extra_imports.log']) == extra['log_sha256'],
            'Full historical cache fetch log SHA differs')

    # The suite contract and all actual source bytes are independently received.
    suite_upload = read_json(HERE / 'SUITE_UPLOAD.json')
    require(exported_json('SUITE_UPLOAD.json') == suite_upload, 'Historical suite upload request differs')
    suite_archive = HERE / PurePosixPath(suite_upload['archive']).name
    require(sha_file(suite_archive) == suite_upload['sha256'], 'Historical suite input archive SHA differs')
    suite_payload = read_archive(suite_archive)
    valid_hashes(suite_upload['files'], 'Historical suite upload hashes')
    require(set(suite_payload) == set(suite_upload['files']), 'Historical suite payload coverage differs')
    for name, digest in suite_upload['files'].items():
        require(sha(suite_payload[name]) == digest == sha_file(HERE / 'suite_payload' / name) and
                files['historical_source/' + name] == suite_payload[name],
                'Historical source differs from uploaded bytes: ' + name)
        if name.startswith('historical_inputs/') or name in {
                'ALL_PUBLIC_THEOREMS.json', 'ADDITIONAL_AXIOM_PRINTS.lean.txt', 'build_audit_inventory.py'}:
            require((HERE / name).read_bytes() == suite_payload[name],
                    'Current original historical/inventory input differs: ' + name)
    suite_inputs = read_json(HERE / 'SUITE_INPUTS.json')
    require(parse_json(suite_payload['SUITE_INPUTS.json']) == suite_inputs,
            'Historical suite contract differs from local input catalog')
    valid_hashes(suite_inputs['source_files'], 'Historical suite source pins')
    for name, digest in suite_inputs['source_files'].items():
        require(sha(suite_payload[name]) == digest, 'Historical source catalog SHA mismatch: ' + name)
    suite = exported_json('historical_verification/RESULT.json')
    require(suite.get('passed') is True, 'Historical suite did not complete')
    require(sha(files['verify_suite.py']) == sha_file(HERE / 'verify_suite.py') == suite['runner_sha256'],
            'Historical suite runner identity mismatch')
    require(suite_upload['runner_sha256'] == suite['runner_sha256'], 'Suite upload runner pin differs')
    historical_launch = exported_json('HISTORICAL_LAUNCH.json')
    require(historical_launch['source_archive_sha256'] == suite_upload['sha256'] and
            historical_launch['runner_sha256'] == suite['runner_sha256'] and
            historical_launch['inputs_sha256'] == sha(suite_payload['SUITE_INPUTS.json']),
            'Historical launch pins differ')
    require(historical_launch['command'][1:] == ['-u', '-B', str(REMOTE_ROOT / 'verify_suite.py')],
            'Historical launch command differs')
    require(suite['compiler_sha256'] == COMPILER_SHA, 'Historical suite compiler differs')
    require(suite['source_hashes'] == suite_inputs['source_files'] and
            suite['inputs_sha256'] == sha(suite_payload['SUITE_INPUTS.json']),
            'Historical executed source/catalog pins differ')
    require(suite['dependency_pins'] == pins, 'Historical dependency source pins differ')
    require(suite['lean_path'] == str(REMOTE_ROOT / 'historical_verification/dependencies') + ':' + str(
        REMOTE_ROOT / 'lean-4.31.0-linux/lib/lean'), 'Historical import path contains unexpected artifacts')
    suite_dependency_bytes = files['historical_verification/DEPENDENCY_ARTIFACTS.json']
    suite_dependencies = parse_json(suite_dependency_bytes)
    valid_hashes(suite_dependencies, 'Historical suite dependencies')
    require(sha(suite_dependency_bytes) == suite['dependency_manifest_sha256'],
            'Historical dependency manifest SHA mismatch')
    exact_int(suite['dependency_artifacts'], len(suite_dependencies), 'Historical artifact count differs')
    require(not any(name.startswith('NDEAEvolve/') for name in suite_dependencies),
            'Historical dependency cache includes project artifacts')
    require(all(suite_dependencies.get(name) == digest for name, digest in dependencies.items()),
            'Historical dependency cache changes or omits a final-proof dependency artifact')

    specs = suite_inputs['checks']
    rows = suite['checks']
    require(len(specs) == len({item['name'] for item in specs}) and
            len(rows) == len({item['name'] for item in rows}) and
            [row['name'] for row in rows] == [item['name'] for item in specs],
            'Historical check name/order/coverage mismatch')
    positive_names = [name for case in specs if case['expectation'] == 'pass' for name in case['expected_audits']]
    require(len(positive_names) == len(set(positive_names)) == suite_inputs['public_audits'] == 473,
            'Complete historical/retained audit count or uniqueness differs')
    require(sum(case.get('expected_error_count', 0) for case in specs) ==
            suite_inputs['expected_false_claim_rejections'] == 13,
            'Complete expected-false-claim rejection count differs')
    inventory = read_json(HERE / 'ALL_PUBLIC_THEOREMS.json')
    require(inventory['combined_sha256'] == COMBINED_SHA and inventory['public_declarations'] == 332,
            'Retained public inventory identity differs')
    complete_names = inventory['expected_complete_audit_names']
    spec_lexer = importlib.util.spec_from_file_location('local_sealed_lexer', ROOT / 'verification_tools/verify_exp005.py')
    lexer = importlib.util.module_from_spec(spec_lexer)
    sys.modules[spec_lexer.name] = lexer
    spec_lexer.loader.exec_module(lexer)
    positive_results, negative_results, complete_overlay_count = [], [], 0
    for check, row in zip(specs, rows):
        name, source_name = check['name'], check['file']
        source_bytes = suite_payload[source_name]
        require(row['file'] == source_name and row['expectation'] == check['expectation'] and
                row.get('passed') is True, 'Incomplete or wrong historical check: ' + name)
        require(check['source_sha256'] == sha(source_bytes) == row['source_sha256_before'] == row['source_sha256_after'],
                'Historical checked source changed: ' + name)
        check_command(row['command'], 'historical_source/' + source_name)
        log_bytes = files['historical_verification/' + name + '.log']
        require(sha(log_bytes) == row['log_sha256'], 'Historical log SHA mismatch: ' + name)
        text = log_bytes.decode()
        clean_source = lexer.code_only(source_bytes.decode())
        actual_prints = re.findall(r'^\s*#print axioms (\S+)\s*$', clean_source, re.M)
        require(len(actual_prints) == len(set(actual_prints)) == len(check['expected_audits']) and
                set(actual_prints) == set(check['expected_audits']),
                'Historical source audit directives differ: ' + name)
        if check['expectation'] == 'pass':
            exact_int(row['exit_code'], 0, 'Positive historical compiler failed: ' + name)
            audited = parsed_axioms(text, check['expected_audits'])
            require(audited == row['axiom_audits'], 'Historical compiler/report axiom disagreement: ' + name)
            require(not ERROR.findall(text) and row['errors'] == [], 'Positive historical errors present: ' + name)
            if set(check['expected_audits']) == set(complete_names):
                require(source_bytes.startswith(source), 'Retained audit overlay changed the sealed source prefix')
                suffix = lexer.code_only(source_bytes[len(source):].decode())
                require(not re.sub(r'^\s*#print axioms \S+\s*$', '', suffix, flags=re.M).strip(),
                        'Retained audit overlay contains executable code beyond axiom prints')
                require(re.findall(r'^\s*#print axioms (\S+)\s*$', suffix, re.M) == inventory['additional_audit_names'],
                        'Retained overlay supplemental audit list differs')
                complete_overlay_count += 1
            positive_results.append({'name': name, 'audits': len(audited), 'source_sha256': sha(source_bytes),
                                     'log_sha256': sha(log_bytes), 'elapsed_seconds': row['elapsed_seconds']})
        elif check['expectation'] == 'reject':
            exact_int(row['exit_code'], 1, 'Expected ordinary Lean proof rejection: ' + name)
            require(check['expected_audits'] == [] and actual_prints == [] and not AXIOMS.findall(text) and
                    not NO_AXIOMS.findall(text), 'Expected rejection contains an axiom audit: ' + name)
            require(IMPORT_FAILURE.search(text) is None, 'Expected rejection is an import/tool/resource failure: ' + name)
            errors = ERROR.findall(text)
            exact_int(check['expected_error_count'], len(errors), 'Expected rejection diagnostic count differs: ' + name)
            require(errors, 'Expected rejection produced no located Lean errors: ' + name)
            require([int(error[1]) for error in errors] == check['expected_error_lines'],
                    'Expected rejection exact error lines differ: ' + name)
            require(all(fragment in text for fragment in check['expected_diagnostic_fragments']),
                    'Expected rejection explanatory diagnostic differs: ' + name)
            for path, line, column, message in errors:
                require(path == str(REMOTE_ROOT / 'historical_source' / source_name),
                        'Expected rejection error comes from a different source: ' + name)
                require(any(low <= int(line) <= high for low, high in check['error_line_ranges']),
                        'Expected rejection error is outside intended theorem lines: ' + name)
                require(any(re.search(pattern, message) for pattern in check['allowed_diagnostic_patterns']),
                        'Expected rejection has an unapproved diagnostic: ' + name + ': ' + message)
            parsed_errors = [{'file': path, 'line': int(line), 'column': int(column), 'message': message}
                             for path, line, column, message in errors]
            require(row['errors'] == parsed_errors and row['axiom_audits'] == {},
                    'Reported rejection diagnostics or axiom rows differ: ' + name)
            negative_results.append({'name': name, 'errors': len(errors), 'source_sha256': sha(source_bytes),
                                     'log_sha256': sha(log_bytes), 'elapsed_seconds': row['elapsed_seconds']})
        else:
            raise RuntimeError('Unknown historical expectation: ' + str(check['expectation']))
    exact_int(complete_overlay_count, 1, 'Exactly one complete retained-source overlay is required')

    # Rerun evidence for the unchanged latest floating-point diagnostics is
    # separate from the theorem proofs and from older Julia/Python test suites.
    numerical_source = files['final_verification/numerical_checks.py']
    numerical_source_sha = sha(numerical_source)
    require(numerical_source == (ROOT / 'numerical_checks.py').read_bytes() ==
            (HERE / 'numerical_checks.py').read_bytes(), 'Fresh numerical script differs from sealed/current code')
    numerical_result = exported_json('final_verification/NUMERICAL_RESULT.json')
    require(numerical_result.get('passed') is True, 'Fresh numerical diagnostics did not pass')
    exact_int(numerical_result['exit_code'], 0, 'Fresh numerical diagnostics process failed')
    require(numerical_result['source_sha256_before'] == numerical_result['source_sha256_after'] == numerical_source_sha,
            'Fresh numerical script changed during execution')
    require(len(numerical_result['command']) == 3 and numerical_result['command'][1:] == [
        '-B', str(REMOTE_ROOT / 'final_verification/numerical_checks.py')],
        'Fresh numerical diagnostics command differs')
    numerical_log = files['final_verification/numerical.log']
    numerical_bytes = files['final_verification/evidence/numerical_checks.json']
    require(sha(numerical_log) == numerical_result['log_sha256'] and
            sha(numerical_bytes) == numerical_result['data_sha256'], 'Fresh numerical log/data SHA differs')
    numerical = parse_json(numerical_bytes)
    previous_numerical = read_json(ROOT / 'evidence/numerical_checks.json')
    require(numerical.get('passed') is True and previous_numerical.get('passed') is True,
            'Fresh or previous numerical diagnostics are not accepted')
    require(numerical['source_sha256'] == previous_numerical['source_sha256'] == numerical_source_sha,
            'Numerical data names a different diagnostic script')
    require(numerical['schema'] == previous_numerical['schema'] == 'ndea.exp008.finite-fourier-diagnostics.v1',
            'Numerical diagnostic data schema differs')

    def finite_numbers(value):
        if isinstance(value, dict):
            return all(finite_numbers(item) for item in value.values())
        if isinstance(value, list):
            return all(finite_numbers(item) for item in value)
        return math.isfinite(value) if isinstance(value, float) else True

    require(finite_numbers(numerical), 'Numerical diagnostics contain NaN or infinity')
    for key in ['M', 'frequencies', 'coefficients', 'Ct', 'Cs']:
        require(numerical[key] == previous_numerical[key], 'Numerical input/constant differs: ' + key)
    require(math.isclose(numerical['coefficient_l2_norm'], previous_numerical['coefficient_l2_norm'],
                         rel_tol=1e-12, abs_tol=1e-14) and numerical['coefficient_l2_norm'] > 0,
            'Numerical coefficient norm differs')
    numeric_counts = {'stage_checks': 60, 'global_checks': 20, 'joint_refinement': 7,
                      'temporal_refinement': 6, 'lie_refinement': 6}
    numeric_parameters = {'stage_checks': ['d', 't', 'k'], 'global_checks': ['d', 'N', 'k', 'h'],
                          'joint_refinement': ['d', 'N', 'h', 'k'],
                          'temporal_refinement': ['N', 'k'], 'lie_refinement': ['N', 'k']}
    for key, count in numeric_counts.items():
        require(isinstance(numerical[key], list) and len(numerical[key]) == len(previous_numerical[key]) == count,
                'Numerical sample count differs: ' + key)
        for new_row, old_row in zip(numerical[key], previous_numerical[key]):
            require(all(new_row[field] == old_row[field] for field in numeric_parameters[key]),
                    'Numerical sample parameters differ: ' + key)
    require(numerical['controls']['aliasing_detected'] is True,
            'Fresh numerical aliasing control was not detected')
    for row in numerical['stage_checks']:
        require(0 <= row['budget'] <= row['bound'] + 1e-10, 'Fresh numerical stage exceeds its bound')
    for key in ['global_checks', 'joint_refinement']:
        require(all(0 < row['error'] <= row['bound'] + 1e-10 for row in numerical[key]),
                'Fresh numerical error exceeds its bound: ' + key)
    observed_orders = {}
    for key in ['joint_refinement', 'temporal_refinement', 'lie_refinement']:
        points = numerical[key]
        for before, after in zip(points, points[1:]):
            require(before['error'] > 0 and after['error'] > 0, 'Refinement error is not positive')
            require(math.isclose(math.log2(before['error'] / after['error']), after['observed_order'],
                                 rel_tol=1e-10, abs_tol=1e-10), 'Reported refinement order differs from errors')
        observed_orders[key] = points[-1]['observed_order']
    require(observed_orders['joint_refinement'] > 1.99 and observed_orders['temporal_refinement'] > 1.99,
            'Fresh symmetric diagnostics do not show second-order refinement')
    require(0.97 < observed_orders['lie_refinement'] < 1.03,
            'Fresh Lie sensitivity diagnostic does not show first-order refinement')
    numeric_recheck = {'passed': True, 'source_sha256': numerical_source_sha,
                       'result_sha256': sha(files['final_verification/NUMERICAL_RESULT.json']),
                       'data_sha256': sha(numerical_bytes), 'log_sha256': sha(numerical_log),
                       'case_counts': numeric_counts, 'finest_observed_orders': observed_orders,
                       'aliasing_detected': True, 'same_inputs_and_constants': True,
                       'elapsed_seconds': numerical_result['elapsed_seconds'],
                       'qualification': 'Fresh execution of the unchanged Experiment 008 floating-point diagnostics; supporting evidence, not a theorem proof or a rerun of every historical numerical/validator suite.'}

    # No output is written before all evidence/content checks have passed.
    output = HERE / 'downloaded_evidence/recheck_evidence'
    require(not output.exists(), 'Extraction destination already exists')
    require(not (HERE / 'downloaded_evidence').is_symlink(), 'Extraction parent is a symlink')
    for target in ['FINAL_TRANSFER_CHECK.json', 'CROSS_ENVIRONMENT_COMPARISON.json']:
        require(not (HERE / target).exists(), 'Refusing to overwrite a previous accepted receipt: ' + target)
    output.mkdir(parents=True, exist_ok=False)
    for name, data in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    now = datetime.now(timezone.utc).isoformat()
    comparison = {'passed': True, 'utc': now, 'combined_sha256': COMBINED_SHA,
                  'fresh_vm_id': allocation['vm_id'], 'previous_vm_id': allocation['previous_vm_id'],
                  'distinct_vm_allocation': True, 'new_dependency_artifact_count': len(dependencies),
                  'new_dependency_manifest_sha256': sha(dependency_bytes),
                  'original_environments': comparisons,
                  'historical_dependency_artifact_count': len(suite_dependencies),
                  'historical_superset_matches_all_9868_final_artifacts': True,
                  'qualification': 'All three exact sealed-source checks agree on source, 90 audits, and all 9868 external artifact hashes. Compatible compiled libraries remain trusted inputs.'}
    report = {'passed': True, 'utc': now, 'archive_sha256': receipt['archive_sha256'],
              'manifest_sha256': receipt['manifest_sha256'], 'evidence_files_checked': len(manifest),
              'sealed_source_sha256': COMBINED_SHA, 'sealed_source_audits': len(final_audits),
              'retained_chain_public_audits': len(complete_names),
              'complete_unique_public_audits': len(positive_names),
              'false_claims_rejected': sum(item['errors'] for item in negative_results),
              'numeric_recheck': numeric_recheck,
              'positive_checks': positive_results, 'expected_rejection_checks': negative_results,
              'bootstrap_commands_verified': len(bootstrap['commands']),
              'final_result_sha256': sha(files['final_verification/RESULT.json']),
              'suite_result_sha256': sha(files['historical_verification/RESULT.json']),
              'receiving_checker_sha256': sha_file(Path(__file__)), 'evidence_root': str(output),
              'qualification': 'Archive/input hashes and independent compiler diagnostics were checked before extraction. This receiving check does not rerun Lean.'}
    (HERE / 'CROSS_ENVIRONMENT_COMPARISON.json').write_text(json.dumps(comparison, indent=2) + '\n')
    (HERE / 'FINAL_TRANSFER_CHECK.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
