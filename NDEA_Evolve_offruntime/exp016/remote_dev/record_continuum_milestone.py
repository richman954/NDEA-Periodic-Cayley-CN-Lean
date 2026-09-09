"""Read back this additive development milestone; do not run or qualify proofs."""
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HOME = Path('/home/richman954')
PROJECT = HOME / 'NDEA_Evolve_offruntime'
ROOT = PROJECT / 'exp016'
EVIDENCE = ROOT / 'evidence'
NAMES = ['SpatialL2Operator', 'ContinuumPotentialStability', 'PotentialErrorTransfer']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def publish(path, value):
    with path.open('x') as out:
        out.write(json.dumps(value, indent=2) + '\n')


def main():
    utc = datetime.now(timezone.utc).isoformat()
    baseline = read(ROOT / 'BASELINE.json')
    sealed = {'utc': utc, 'passed': True, 'baseline_sha256': digest(ROOT / 'BASELINE.json'),
              'experiments': {}}
    for name, expected in baseline['experiments'].items():
        exp = PROJECT / name
        receipt = exp / 'evidence/FINAL_PACKET_RECEIPT.json'
        assert digest(receipt) == expected['final_packet_receipt_sha256']
        packet = read(receipt)
        assert packet['manifest_sha256'] == expected['packet_manifest_sha256']
        assert digest(exp / 'PACKET_MANIFEST.json') == expected['packet_manifest_sha256']
        assert digest(packet['archive']) == expected['archive_sha256']
        for rel, sha in expected['payload_sha256'].items():
            assert digest(exp / rel) == sha, (name, rel)
        sealed['experiments'][name] = {
            'payload_files_verified': len(expected['payload_sha256']),
            'all_payload_sha256_match': True, 'final_packet_receipt_unchanged': True,
            'packet_manifest_unchanged': True, 'archive_sha256_matches': True}
    clone = HOME / 'NDEA_GitHub_Backup/exp016_potential_readback'
    checkpoint = clone / 'NDEA_Evolve_offruntime/exp016/POTENTIAL_CHECKPOINT.json'
    remote = read(HOME / 'NDEA_GitHub_Backup/EXP016_POTENTIAL_ALL_TREE_READBACK.json')
    assert remote['passed'] and digest(checkpoint) == remote['catalog_sha256']
    for spec, expected in [('HEAD', remote['commit']), ('HEAD^{tree}', remote['tree'])]:
        assert subprocess.run(['git', '--no-optional-locks', '-C', str(clone), 'rev-parse', spec],
            check=True, capture_output=True, text=True).stdout.strip() == expected
    old = read(checkpoint)
    old_sources = {}
    for name, item in old['modules'].items():
        source = ROOT / 'lean' / (name + '.lean')
        clone_source = clone / source.relative_to(HOME)
        assert digest(source) == digest(clone_source) == item['source_sha256'], name
        old_sources[name] = digest(source)
    entries = []
    for name in NAMES:
        receipts = sorted(EVIDENCE.glob('remote_development/*_' + name + '/RESULT.json'))
        assert len(receipts) == 1, (name, receipts)
        receipt = receipts[0]
        result = read(receipt)
        validation = read(receipt.parent / 'WORKFLOW_VALIDATION.json')
        source = ROOT / 'lean' / (name + '.lean')
        log = receipt.parent / 'compiler.log'
        artifact = ROOT / 'build/lib/lean' / (name + '.olean')
        assert result['exit_code'] == 0 and result['sources_unchanged'] and result['imports_unchanged']
        assert digest(source) == result['source_sha256_before'] == result['source_sha256_after']
        assert digest(log) == result['log_sha256']
        assert digest(artifact) == result['output_sha256']
        assert validation['passed'] and validation['standard_axioms_only']
        assert validation['module'] == result['module'] == name
        assert validation['source_sha256'] == digest(source)
        assert validation['artifact_sha256'] == digest(artifact)
        assert validation['independent_qualification'] is False
        assert result['independent_qualification'] is False
        assert validation['receipt_sha256'] == digest(receipt)
        assert 'error:' not in log.read_text() and 'sorryAx' not in log.read_text()
        audits = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log.read_text(), re.M)
        assert len(audits) == validation['explicit_axiom_audit_count']
        assert {n for n, _ in audits} == set(validation['explicit_axiom_audit_names'])
        assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
            for _, a in audits)
        entries.append({'module': name, 'source': str(source), 'source_sha256': digest(source),
            'receipt': str(receipt), 'receipt_sha256': digest(receipt),
            'log': str(log), 'log_sha256': digest(log), 'artifact_sha256': digest(artifact),
            'compiler_exit': 0, 'elapsed_seconds': result['elapsed_seconds'],
            'lock_wait_seconds': result['lock_wait_seconds'], 'sources_unchanged': True,
            'imports_unchanged': True, 'explicit_transitive_axiom_audits': dict(audits),
            'errors': 0, 'warnings': validation['warning_count'],
            'runner_sha256': result['runner_sha256'],
            'lean_binary_sha256': result['lean_binary_sha256'],
            'workflow_validation': str(receipt.parent / 'WORKFLOW_VALIDATION.json'),
            'workflow_validation_sha256': digest(receipt.parent / 'WORKFLOW_VALIDATION.json')})
    sealed_path = EVIDENCE / 'SEALED_PREDECESSOR_READBACK_CONTINUUM.json'
    publish(sealed_path, sealed)
    report = {'utc': utc, 'development_only': True, 'independent_qualification': False,
        'sealed': False, 'new_modules': entries,
        'explicit_standard_axiom_reports': sum(len(e['explicit_transitive_axiom_audits']) for e in entries),
        'style_warnings': sum(e['warnings'] for e in entries), 'errors': 0,
        'previous_accepted_sources_readback': {'passed': True, 'source_count': len(old_sources),
            'checkpoint': str(checkpoint), 'checkpoint_sha256': digest(checkpoint),
            'clone_commit': remote['commit'],
            'all_current_and_clone_source_sha256_match_checkpoint': True, 'source_sha256': old_sources},
        'sealed_predecessor_readback': str(sealed_path),
        'sealed_predecessor_readback_sha256': digest(sealed_path),
        'scope': 'Actual continuum two-potential stability with arbitrary initial mismatch; '
            'paired actual sampled ordered-trajectory/continuum cutoff error transfer at grid times. '
            'No smooth-core solver convergence, partial-slab potential transfer, combined qualification or seal.'}
    target = EVIDENCE / 'CONTINUUM_MILESTONE_LOCAL.json'
    publish(target, report)
    print(json.dumps({'passed': True, 'receipt': str(target), 'sha256': digest(target),
        'new_modules': NAMES, 'audits': report['explicit_standard_axiom_reports'],
        'warnings': report['style_warnings'], 'errors': 0, 'old_sources_unchanged': len(old_sources),
        'sealed_payloads_unchanged': sum(e['payload_files_verified'] for e in sealed['experiments'].values()),
        'independent_qualification': False}, indent=2))


if __name__ == '__main__':
    main()
