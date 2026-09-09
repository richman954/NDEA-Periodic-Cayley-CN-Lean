"""Independent read-only check of the sealed Exp015 packet and accepted evidence."""
import datetime
import hashlib
import json
import re
import tarfile
import zipfile
from pathlib import Path, PurePosixPath

ROOT = Path('/home/richman954/NDEA_Evolve_offruntime/exp015')
REMOTE = ROOT / 'remote_check/downloaded_evidence'
OUTPUT = Path('/tmp/exp015_final_readback.json')
SOURCE_MODULES = ('ScalarSqrtEstimate', 'SpatialL2', 'ResidualField', 'ForcedStability',
                  'ResidualEstimate', 'VariablePotentialBridge', 'Controls')
PREDECESSOR_SHA256 = '40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee'
FOUNDATION_SHA256 = '9d8ac0dfcba35dec86ea229657defc88da01f94ddfece9b8f119f52120a4d8c6'
EXTERNAL_PREFIXES = ('Mathlib.', 'Lean.', 'Std.', 'Init.')

def digest(data):
    return hashlib.sha256(data).hexdigest()

def sha(path):
    return digest(Path(path).read_bytes())

def read(path):
    return json.loads(Path(path).read_text())

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def safe_name(name):
    p = PurePosixPath(name)
    return not p.is_absolute() and '..' not in p.parts and str(p) == name

def code_without_comments_or_strings(source):
    """Keep code and line boundaries, masking Lean nested comments and strings."""
    output, index, depth, in_string = [], 0, 0, False
    while index < len(source):
        pair, character = source[index:index + 2], source[index]
        if depth:
            if pair == '/-':
                depth += 1
                output.extend('  ')
                index += 2
            elif pair == '-/':
                depth -= 1
                output.extend('  ')
                index += 2
            else:
                output.append('\n' if character == '\n' else ' ')
                index += 1
        elif in_string:
            if character == '\\' and index + 1 < len(source):
                output.extend('  ')
                index += 2
            else:
                if character == '"':
                    in_string = False
                output.append('\n' if character == '\n' else ' ')
                index += 1
        elif pair == '--':
            end = source.find('\n', index)
            end = len(source) if end == -1 else end
            output.extend(' ' * (end - index))
            index = end
        elif pair == '/-':
            depth = 1
            output.extend('  ')
            index += 2
        elif character == '"':
            in_string = True
            output.append(' ')
            index += 1
        else:
            output.append(character)
            index += 1
    require(depth == 0 and not in_string, 'Unterminated comment/string')
    return ''.join(output)

def source_public_names(source, module):
    """Read the actual public theorem/lemma declarations without project code."""
    names, scopes = [], []
    for raw_line in code_without_comments_or_strings(source).splitlines():
        line = raw_line.strip()
        namespace = re.fullmatch(r'namespace\s+(\S+)', line)
        section = re.fullmatch(r'section(?:\s+(\S+))?', line)
        ending = re.fullmatch(r'end(?:\s+(\S+))?', line)
        if namespace:
            scopes.append(('namespace', namespace.group(1)))
        elif section:
            scopes.append(('section', section.group(1)))
        elif ending:
            require(bool(scopes), 'Unmatched scope ending in ' + module)
            kind, name = scopes.pop()
            if ending.group(1) is not None:
                require(ending.group(1) == name, 'Named scope ending mismatch in ' + module)
        statement = re.match(r'^(?:@\[[^\]]*\]\s*)*'
                             r'(?:(private|protected)\s+)?(?:theorem|lemma)\s+([^\s(:]+)', line)
        if statement and statement.group(1) != 'private':
            namespaces = [name for kind, name in scopes if kind == 'namespace']
            full_name = '.'.join(namespaces + [statement.group(2)])
            require(full_name.startswith('NDEAEvolve.Exp015.'), 'Unexpected new theorem namespace')
            names.append(full_name)
        elif re.match(r'^(?:@\[[^\]]*\]\s*)*(?:public\s+|noncomputable\s+|nonrec\s+)*'
                      r'(?:theorem|lemma)\b', line) and not statement:
            raise AssertionError('Unrecognized theorem declaration format in ' + module + ': ' + line)
    require(not scopes, 'Unclosed scope in ' + module)
    require(names and len(names) == len(set(names)), 'Empty/duplicate module catalog')
    return names

def reconstruct_source_catalog():
    retained = ROOT / 'predecessor_sources/Exp014Combined.lean'
    original = ROOT.parent / 'exp014/lean/Exp014Combined.lean'
    require(sha(retained) == sha(original) == PREDECESSOR_SHA256, 'Exact Exp014 predecessor source changed')
    source = retained.read_bytes()
    old_audits = re.findall(rb'^#print axioms (\S+)', source, re.M)
    require(len(old_audits) == len(set(old_audits)) == 143 and
            all(name.startswith(b'NDEAEvolve.Exp014.') for name in old_audits), 'Old audit catalog changed')
    foundation = re.sub(rb'^#print axioms .*\n', b'', source, flags=re.M)
    require(digest(foundation) == FOUNDATION_SHA256 and
            (ROOT / 'lean/Exp014Foundation.lean').read_bytes() == foundation,
            'Exact derived predecessor foundation changed')
    names, counts, imports, bodies = [], {}, set(), []
    hashes = {'predecessor_sources/Exp014Combined.lean': PREDECESSOR_SHA256}
    for module in ('Exp014Foundation',) + SOURCE_MODULES:
        relative = 'lean/' + module + '.lean'
        text = (ROOT / relative).read_text()
        hashes[relative] = sha(ROOT / relative)
        clean = code_without_comments_or_strings(text)
        for imported in re.findall(r'^import\s+(\S+)', clean, re.M):
            if imported.startswith(EXTERNAL_PREFIXES):
                imports.add(imported)
        if module in SOURCE_MODULES:
            module_names = source_public_names(text, module)
            names.extend(module_names)
            counts[module] = len(module_names)
        body = re.sub(r'^(?:import |#print axioms |#check ).*\n', '', text, flags=re.M)
        bodies.append('-- SOURCE ' + relative + ' SHA256 ' + hashes[relative] + '\n' + body)
    require(len(names) == len(set(names)), 'Duplicate cross-module public theorem names')
    combined = ('\n'.join('import ' + name for name in sorted(imports)) + '\n\n' +
                '\n\n'.join(bodies) + '\n\n' +
                '\n'.join('#print axioms ' + name for name in names) + '\n').encode()
    return names, counts, hashes, combined

def main():
    receipt = read(ROOT / 'evidence/FINAL_PACKET_RECEIPT.json')
    archive = Path(receipt['archive'])
    manifest_bytes = (ROOT / 'PACKET_MANIFEST.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    require(receipt['passed'] is True, 'Unaccepted packet receipt')
    require(sha(archive) == receipt['archive_sha256'], 'Packet SHA256 mismatch')
    require(archive.stat().st_size == receipt['archive_bytes'], 'Packet size mismatch')
    require(digest(manifest_bytes) == receipt['manifest_sha256'], 'Manifest SHA256 mismatch')
    require(len(manifest) == receipt['manifest_entries'], 'Manifest entry count mismatch')
    checksum = Path(str(archive) + '.sha256').read_text().strip()
    require(checksum == receipt['archive_sha256'] + '  ' + archive.name, 'Adjacent checksum mismatch')
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        expected_names = {'exp015/' + n for n in manifest} | {'exp015/PACKET_MANIFEST.json'}
        require(len(names) == len(set(names)) == receipt['verified_zip_files'], 'ZIP duplicate/count mismatch')
        require(set(names) == expected_names, 'ZIP member coverage mismatch')
        require(all(safe_name(n) for n in names), 'Unsafe ZIP name')
        require(z.testzip() is None, 'ZIP CRC failure')
        require(z.read('exp015/PACKET_MANIFEST.json') == manifest_bytes, 'Manifest byte mismatch')
        for name, expected in manifest.items():
            require(safe_name(name), 'Unsafe payload path')
            current = ROOT / name
            require(current.is_file() and not current.is_symlink(), 'Missing/symlink payload: ' + name)
            data = z.read('exp015/' + name)
            require(digest(data) == expected == sha(current), 'Payload SHA256 mismatch: ' + name)
            require(data == current.read_bytes(), 'Payload byte mismatch: ' + name)

    inputs = read(ROOT / 'evidence/FINAL_INPUTS.json')
    final = read(ROOT / 'evidence/FINAL_VERIFICATION.json')
    transfer = read(ROOT / 'remote_check/FINAL_TRANSFER_CHECK.json')
    local = read(ROOT / 'evidence/local_combined/RESULT.json')
    remote = read(REMOTE / 'final_verification/RESULT.json')
    expected = set(inputs['expected_audits'])
    derived, per_module, reconstructed_hashes, reconstructed_combined = reconstruct_source_catalog()
    audit_count = len(derived)
    require(len(expected) == len(inputs['expected_audits']) == audit_count, 'Unexpected audit catalog')
    require(inputs['expected_audits'] == derived, 'Input catalog differs from independent source scan')
    require(inputs['source_hashes'] == reconstructed_hashes, 'Input source map differs from independent reconstruction')
    require((ROOT / 'lean/Exp015Combined.lean').read_bytes() == reconstructed_combined, 'Combined source differs from independent reconstruction')
    require(final['passed'] and transfer['passed'], 'Unaccepted final/transfer result')
    require(final['audits'] == transfer['audits_verified'] == audit_count, 'Final/transfer audit count mismatch')
    require(final['expected_audits'] == inputs['expected_audits'], 'Final catalog mismatch')
    require(final['source_hashes'] == inputs['source_hashes'], 'Final source map mismatch')
    combined_hash = sha(ROOT / 'lean/Exp015Combined.lean')
    require(combined_hash == inputs['source_sha256'] == final['source_sha256'] == transfer['source_sha256'],
            'Combined source binding mismatch')
    for name, expected_hash in inputs['source_hashes'].items():
        require(sha(ROOT / name) == expected_hash, 'Frozen source mismatch: ' + name)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for label, result, base in [('local', local, ROOT / 'evidence/local_combined'),
                                ('independent', remote, REMOTE / 'final_verification')]:
        require(result['passed'] and result['exit_code'] == 0 and result['reconstruction_verified'],
                'Unaccepted proof result: ' + label)
        require(result['source_sha256_before'] == result['source_sha256_after'] == combined_hash,
                'Proof source hash mismatch: ' + label)
        require(result['source_hashes'] == inputs['source_hashes'], 'Proof module map mismatch: ' + label)
        require(result['runner_sha256'] == sha(ROOT / 'verify_combined.py'), 'Verifier binding mismatch')
        log = (base / 'combined.log').read_bytes()
        require(digest(log) == result['log_sha256'], 'Compiler log hash mismatch: ' + label)
        matches = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log.decode(), re.M)
        empty = re.findall(r"^'([^']+)' does not depend on any axioms", log.decode(), re.M)
        names = [n for n, _ in matches] + empty
        require(len(names) == len(set(names)) == audit_count and set(names) == expected, 'Compiler audit coverage mismatch')
        audits = {name: sorted(a.strip() for a in axioms.split(',') if a.strip()) for name, axioms in matches}
        audits.update({name: [] for name in empty})
        require(audits == result['axiom_audits'], 'Audit report differs from log')
        require(all(set(axioms) <= allowed for axioms in audits.values()), 'Unexpected axiom')
        require(sha(base / 'DEPENDENCY_ARTIFACTS.json') == result['dependency_manifest_sha256'],
                'Dependency manifest binding mismatch')
    require(local['axiom_audits'] == remote['axiom_audits'], 'Cross-environment audit mismatch')
    require(local['compiler_sha256'] == remote['compiler_sha256'] ==
            'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'Compiler pin mismatch')
    require(local['dependency_pins'] == remote['dependency_pins'], 'Dependency source pin mismatch')
    local_dependencies = read(ROOT / 'evidence/local_combined/DEPENDENCY_ARTIFACTS.json')
    require(local_dependencies == read(REMOTE / 'final_verification/DEPENDENCY_ARTIFACTS.json'),
            'Cross-environment dependency manifests differ')
    require(len(local_dependencies) == transfer['dependency_artifacts_agree'] ==
            local['dependency_artifacts'] == remote['dependency_artifacts'], 'Artifact count mismatch')
    for field, path in [('local_result_sha256', ROOT / 'evidence/local_combined/RESULT.json'),
                        ('independent_result_sha256', REMOTE / 'final_verification/RESULT.json'),
                        ('transfer_receipt_sha256', ROOT / 'remote_check/FINAL_TRANSFER_CHECK.json'),
                        ('review_receipt_sha256', ROOT / 'evidence/REVIEW_CHECK.json'),
                        ('predecessor_receipt_sha256', ROOT / 'evidence/PREDECESSOR_PRESERVATION.json')]:
        require(final[field] == sha(path), 'Final qualification binding mismatch: ' + field)
    review = read(ROOT / 'evidence/REVIEW_CHECK.json')
    require(review['passed'] and review['current_source_hashes'] == reconstructed_hashes and
            review['public_catalog_total'] == audit_count, 'Frozen source review binding mismatch')
    require(sha(ROOT / 'REVIEW.md') == review['review_sha256'], 'Review text changed')
    for field in ('reviewed_tool_hashes', 'reviewed_document_hashes'):
        require(bool(review[field]), 'Missing exact review coverage')
        for name, expected_hash in review[field].items():
            require(safe_name(name) and sha(ROOT / name) == expected_hash, 'Reviewed bytes changed: ' + name)
    require(transfer['checker_sha256'] == sha(ROOT / 'remote_check/check_download.py'), 'Receiving checker changed')
    for field, base in [('accepted_local_files', ROOT), ('accepted_independent_files', REMOTE)]:
        require(bool(transfer[field]), 'Empty accepted file map')
        for name, expected_hash in transfer[field].items():
            require(safe_name(name) and sha(base / name) == expected_hash, 'Accepted file mismatch: ' + name)
    export = read(ROOT / 'remote_check/EXPORT_RECEIPT.json')
    evidence_archive = ROOT / 'remote_check' / Path(export['archive']).name
    require(export['passed'] and sha(evidence_archive) == export['sha256'] ==
            transfer['archive_sha256'] == final['independent_archive_sha256'], 'Evidence archive binding mismatch')
    require(evidence_archive.stat().st_size == export['bytes'], 'Evidence archive size mismatch')
    tar_files = {}
    with tarfile.open(evidence_archive) as tar:
        for entry in tar.getmembers():
            require(entry.isfile() and safe_name(entry.name) and entry.name not in tar_files, 'Unsafe tar member')
            tar_files[entry.name] = tar.extractfile(entry).read()
    evidence_manifest = json.loads(tar_files['EVIDENCE_SHA256.json'])
    require(set(evidence_manifest) == set(tar_files) - {'EVIDENCE_SHA256.json'}, 'Evidence manifest coverage mismatch')
    require(len(evidence_manifest) == export['payload_files'] == transfer['verified_payload_files'], 'Evidence count mismatch')
    require(set(tar_files) == set(transfer['accepted_independent_files']), 'Accepted tar coverage mismatch')
    for name, data in tar_files.items():
        require(data == (REMOTE / name).read_bytes(), 'Evidence tar/current byte mismatch')
        if name in evidence_manifest:
            require(digest(data) == evidence_manifest[name], 'Evidence manifest hash mismatch')
    request = read(ROOT / 'remote_check/FINAL_UPLOAD.json')
    require(request == read(REMOTE / 'FINAL_UPLOAD.json'), 'Independent upload request differs')
    delivered_inputs = read(REMOTE / 'final_source/FINAL_TRANSFER_INPUTS.json')
    require(delivered_inputs == request['files'], 'Delivered source catalog differs from upload request')
    require(set(delivered_inputs) == {name.removeprefix('final_source/') for name in tar_files
            if name.startswith('final_source/')} - {'FINAL_TRANSFER_INPUTS.json'}, 'Delivered input coverage mismatch')
    for name, expected_hash in delivered_inputs.items():
        require(sha(ROOT / name) == sha(REMOTE / 'final_source' / name) == expected_hash,
                'Transferred source/tool input differs: ' + name)
    require(inputs == read(REMOTE / 'final_source/evidence/FINAL_INPUTS.json'), 'Transferred final catalog differs')
    launch = read(REMOTE / 'FINAL_LAUNCH.json')
    require(launch['combined_sha256'] == combined_hash and launch['source_archive_sha256'] == request['sha256']
            and launch['runner_sha256'] == sha(ROOT / 'verify_combined.py'), 'Final launch binding mismatch')
    require(remote['command'] == ['/content/exp015_check/lean-4.31.0-linux/bin/lean', '-j', '1',
            '/content/exp015_check/final_source/lean/Exp015Combined.lean'], 'Unexpected independent Lean command')
    require(remote['lean_path'] == '/content/exp015_check/final_verification/dependencies:'
            '/content/exp015_check/lean-4.31.0-linux/lib/lean', 'Independent import path includes unqualified inputs')
    require(set(final['accepted_modular_receipts']) == {'lean/' + name + '.lean' for name in SOURCE_MODULES}, 'Unexpected modular count')
    for name, path in final['accepted_modular_receipts'].items():
        module = read(ROOT / path)
        require(module['exit_code'] == 0 and module['sources_unchanged'] and
                module['source_sha256_before'] == module['source_sha256_after'] == inputs['source_hashes'][name],
                'Modular source binding mismatch')
        require(sha(module['log']) == module['log_sha256'], 'Modular log mismatch')
        require(bool(module['output_sha256']) and all(sha(path) == expected_hash
                for path, expected_hash in module['output_sha256'].items()), 'Modular artifact mismatch')
    bootstrap = transfer['bootstrap_verification']
    environment = read(REMOTE / 'ENVIRONMENT.json')
    allocation = read(ROOT / 'remote_check/VM_ALLOCATION.json')
    require(bootstrap['passed'] and environment['passed'] and environment['fresh_root'] and
            environment['prior_project_paths'] == [] and allocation['distinct_allocation'], 'Fresh allocation absent')
    require(bootstrap['vm_id'] == allocation['vm_id'] not in allocation['previous_vm_ids'], 'VM identity is not distinct')
    require(bootstrap['boot_id'] == environment['boot_id'], 'Boot identity mismatch')
    require(bootstrap == final['bootstrap_verification'], 'Final bootstrap binding mismatch')
    require((REMOTE / 'ENVIRONMENT.json').read_bytes() == (ROOT / 'remote_check/ENVIRONMENT_EXPECTED.json').read_bytes(),
            'Expected and received environment bytes differ')
    require(environment['session'] == allocation['session'] == bootstrap['session'] == 'exp015-independent-check'
            and environment['root'] == allocation['root'] == '/content/exp015_check', 'Runtime session/root mismatch')
    bootstrap_result = read(REMOTE / 'bootstrap/RESULT.json')
    require(bootstrap_result['passed'] and bootstrap_result.get('error') is None and
            bootstrap_result['compiler_sha256'] == remote['compiler_sha256'] and
            bootstrap_result['dependency_pins'] == remote['dependency_pins'], 'Bootstrap result/pin mismatch')
    commands = bootstrap_result['commands']
    require(len(commands) == bootstrap['commands_verified'], 'Bootstrap command count mismatch')
    command_logs = []
    for row in commands:
        log_path = PurePosixPath(row['log'])
        require(log_path.is_relative_to('/content/exp015_check'), 'Unexpected bootstrap log path')
        relative = str(log_path.relative_to('/content/exp015_check'))
        require(row['exit_code'] == 0 and sha(REMOTE / relative) == row['log_sha256'], 'Bootstrap command/log failure')
        command_logs.append(relative)
    require(len(command_logs) == len(set(command_logs)), 'Duplicate bootstrap command logs')
    require(set(command_logs) == {name for name in tar_files if name.startswith('bootstrap/') and name.endswith('.log')},
            'Bootstrap command log coverage mismatch')
    def utc(value):
        stamp = datetime.datetime.fromisoformat(value)
        require(stamp.tzinfo is not None, 'Missing timestamp timezone')
        return stamp.astimezone(datetime.timezone.utc)
    require(utc(environment['utc']) <= utc(bootstrap_result['start_utc']) <= utc(bootstrap_result['end_utc']) <=
            utc(remote['start_utc']) <= utc(remote['end_utc']), 'Independent runtime chronology mismatch')
    report = {
        'passed': True,
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'validator_sha256': sha(__file__),
        'archive': str(archive),
        'archive_sha256': receipt['archive_sha256'],
        'archive_bytes': receipt['archive_bytes'],
        'manifest_sha256': receipt['manifest_sha256'],
        'packet_payloads_verified': len(manifest),
        'zip_members_verified': len(manifest) + 1,
        'all_packet_payloads_match_current_files': True,
        'zip_crc_passed': True,
        'combined_sha256': combined_hash,
        'source_derived_audit_count': audit_count,
        'source_derived_per_module_counts': per_module,
        'pinned_exp014_predecessor_sha256': PREDECESSOR_SHA256,
        'pinned_exp014_derived_foundation_sha256': FOUNDATION_SHA256,
        'combined_reconstruction_independently_verified': True,
        'local_audits': len(local['axiom_audits']),
        'independent_audits': len(remote['axiom_audits']),
        'compiler_logs_independently_parsed': True,
        'allowed_axioms_only': sorted(allowed),
        'accepted_local_files_verified': len(transfer['accepted_local_files']),
        'accepted_independent_files_verified': len(transfer['accepted_independent_files']),
        'independent_evidence_payloads_verified': len(evidence_manifest),
        'external_artifact_hashes_agree': len(local_dependencies),
        'accepted_modules': len(final['accepted_modular_receipts']),
        'bootstrap_command_logs_verified': len(command_logs),
        'fresh_vm_id': bootstrap['vm_id'],
        'fresh_boot_id': bootstrap['boot_id'],
        'qualification': final['qualification'],
        'scope': 'Independent local readback and receipt binding check; no new Lean run and no writes to sealed sources or packet.'
    }
    OUTPUT.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
