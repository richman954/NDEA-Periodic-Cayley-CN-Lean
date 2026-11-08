#!/usr/bin/env python3
"""Re-audit two independently scheduled jobs; not an independent kernel."""
import argparse
import json
from pathlib import Path
import evidence_audit as evidence


def compare(repo: Path, folder: Path) -> dict:
    roots = sorted(p.parent for p in folder.rglob('EVIDENCE_AUDIT.json'))
    evidence.require(len(roots) == 2, 'Exactly two completed replica receipts are required')
    checked = [evidence.audit(repo, root) for root in roots]
    plans = [json.loads((root/'plan.json').read_text()) for root in roots]
    records = [json.loads((root/'verification.json').read_text()) for root in roots]
    for root, actual in zip(roots, checked):
        evidence.require(json.loads((root/'EVIDENCE_AUDIT.json').read_text()) == actual,
                         'Downloaded receipt disagrees with new audit')
    for field in ('commit', 'pins', 'sources'):
        evidence.require(plans[0][field] == plans[1][field], 'Replicas disagree on ' + field)
    for field in ('binary_hashes', 'external_package_revisions', 'checked_declarations'):
        evidence.require(records[0][field] == records[1][field], 'Replicas disagree on ' + field)
    evidence.require(records[0]['runner'] and records[1]['runner'] and
                     records[0]['runner'] != records[1]['runner'], 'Distinct runner records required')
    result = {'status': 'TWO_FRESH_RUNS_AND_EVIDENCE_AUDITS_PASS',
              'commit': checked[0]['commit'], 'project_modules': checked[0]['project_modules'],
              'audited_declarations': checked[0]['audited_declarations'],
              'replica_manifest_sha256': [c['manifest_sha256'] for c in checked],
              'runners': [r['runner'] for r in records],
              'independent_kernel': False, 'exp016_sealed': False,
              'limits': 'Same pinned kernel and verifier code; not independent implementation or semantic review.'}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--artifacts', type=Path, required=True)
    args = parser.parse_args()
    result = compare(args.repo, args.artifacts)
    output = args.artifacts/'REPRODUCIBILITY.json'
    evidence.require(not output.exists(), 'Do not overwrite reproducibility evidence')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
