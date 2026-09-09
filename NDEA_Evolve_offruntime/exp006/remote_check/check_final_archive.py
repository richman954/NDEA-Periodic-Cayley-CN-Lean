"""Verify transferred Exp006 evidence against the locally checked source."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('archive',type=Path)
    p.add_argument('--sha256',required=True)
    p.add_argument('--extract-to',type=Path,required=True)
    args=p.parse_args()
    root=Path(__file__).resolve().parent.parent
    require(sha(args.archive.read_bytes())==args.sha256,'Archive checksum mismatch')
    files={}
    with tarfile.open(args.archive) as t:
        for m in t.getmembers():
            path=PurePosixPath(m.name)
            require(m.isfile() and not path.is_absolute() and '..' not in path.parts
                    and m.name not in files,'Unsafe or duplicate archive member')
            files[m.name]=t.extractfile(m).read()
    manifest=json.loads(files['EVIDENCE_SHA256.json'])['files']
    require(set(manifest)==set(files)-{'EVIDENCE_SHA256.json'},'Manifest coverage mismatch')
    for name,digest in manifest.items():require(sha(files[name])==digest,'Evidence hash mismatch: '+name)
    result=json.loads(files['final_verification/RESULT.json'])
    local=json.loads((root/'evidence/FINAL_VERIFICATION.json').read_text())
    expected=set(json.loads((root/'evidence/EXPECTED_FINAL_THEOREMS.json').read_text()))
    require(local['passed'] and result['passed'] and result['exit_code']==0,'Incomplete local/remote check')
    source_hash=sha((root/'lean/CombinedVerification.lean').read_bytes())
    require(source_hash==local['combined_sha256']==result['source_sha256_before']==result['source_sha256_after']
            ==sha(files['CombinedVerification.lean']),'Checked sources do not match')
    require(len(expected)==41 and set(result['expected_audits'])==set(result['axiom_audits'])==expected,
            'Expected audit coverage mismatch')
    log=files['final_verification/combined.log']
    require(sha(log)==result['log_sha256'],'Compiler log hash mismatch')
    text=log.decode()
    require(re.search(r'\berror:|\bsorryAx\b',text) is None,'Compiler error or placeholder')
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
    rows += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
    audit={}
    for name,dependencies in rows:
        require(name not in audit,'Duplicate axiom audit')
        values=set(filter(None,(x.strip() for x in dependencies.split(','))))
        require(values<={'propext','Classical.choice','Quot.sound'},'Unexpected axiom')
        audit[name]=sorted(values)
    require(set(audit)==expected and audit==result['axiom_audits'],'Compiler/report audit mismatch')
    require(sha(files['final_verification/DEPENDENCY_ARTIFACTS.json'])
            ==result['dependency_artifact_manifest_sha256'],'Dependency manifest hash mismatch')
    for name,digest in local['source_sha256'].items():
        require(sha((root/'lean'/Path(name).name).read_bytes())==digest,'Local source changed')
    args.extract_to.mkdir(exist_ok=False)
    for name,data in files.items():
        target=args.extract_to/name
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(data)
    report={'passed':True,'archive_sha256':args.sha256,'evidence_files_verified':len(manifest),
            'local_and_remote_source_sha256':source_hash,'axiom_audits_verified':len(audit),
            'remote_elapsed_seconds':result['elapsed_seconds'],
            'scope':'Transfer hashes and agreement with local checked source/audits; no Lean rerun by this script.'}
    (Path(__file__).parent/'FINAL_TRANSFER_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__=='__main__':
    main()
