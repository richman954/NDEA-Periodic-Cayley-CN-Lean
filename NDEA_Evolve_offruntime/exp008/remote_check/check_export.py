"""Validate independent transfer hashes, complete source identity, and axiom audits."""
from pathlib import Path,PurePosixPath
import hashlib,importlib.util,json,tarfile

remote=Path(__file__).resolve().parent;root=remote.parent
record=json.loads((remote/'EXPORT_RECEIPT.json').read_text())
archive=remote/Path(record['archive']).name
sha=lambda data:hashlib.sha256(data).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
require(sha(archive.read_bytes())==record['archive_sha256'],'Archive hash mismatch')
files={}
with tarfile.open(archive) as tar:
    for item in tar.getmembers():
        path=PurePosixPath(item.name)
        require(item.isfile() and not path.is_absolute() and '..' not in path.parts
                and len(path.parts)>1 and path.parts[0]=='exp008_independent_evidence','Unsafe archive member')
        name=str(PurePosixPath(*path.parts[1:]))
        require(name not in files,'Duplicate normalized archive member')
        files[name]=tar.extractfile(item).read()
manifest_bytes=files['EVIDENCE_SHA256.json'];hashes=json.loads(manifest_bytes)
require(sha(manifest_bytes)==record['manifest_sha256'],'Manifest hash mismatch')
require(set(hashes)==set(files)-{'EVIDENCE_SHA256.json'} and len(hashes)==record['files'],'Manifest coverage mismatch')
require(all(sha(files[name])==digest for name,digest in hashes.items()),'Evidence file hash mismatch')
inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
result=json.loads(files['final_verification/RESULT.json'])
upload=json.loads((remote/'FINAL_UPLOAD.json').read_text())
require(json.loads(files['final_source/FINAL_TRANSFER_INPUTS.json'])==upload['files'],
        'Returned verification-input manifest differs from upload')
for name,digest in upload['files'].items():
    require(sha(files['final_source/'+name])==digest==sha((root/name).read_bytes()),
            'Verification input differs from uploaded or current local bytes: '+name)
require(result['runner_sha256']==upload['files']['verify_combined.py'],
        'Executed verifier differs from uploaded verifier')
launch=json.loads(files['FINAL_LAUNCH.json'])
require(launch['runner_sha256']==result['runner_sha256'] and
        launch['source_archive_sha256']==upload['sha256'] and
        launch['combined_sha256']==inputs['source_sha256'], 'Launch/input identity mismatch')
require(result['compiler_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
        'Independent compiler pin mismatch')
require(result.get('passed') is True and result.get('exit_code')==0 and result.get('reconstruction_verified'),'Incomplete independent result')
require(result['source_sha256_before']==result['source_sha256_after']==inputs['source_sha256']
        ==sha(files['final_source/lean/Exp008Combined.lean'])==sha((root/'lean/Exp008Combined.lean').read_bytes()),'Combined source identity mismatch')
require(result['source_hashes']==inputs['source_hashes'],'Checked source catalog mismatch')
for name,digest in inputs['source_hashes'].items():
    require(sha((root/name).read_bytes())==digest==sha(files['final_source/'+name]),'Source mismatch: '+name)
require(json.loads(files['final_source/evidence/FINAL_INPUTS.json'])==inputs,'Final input/audit catalog mismatch')
log=files['final_verification/combined.log']
require(sha(log)==result['log_sha256'],'Compiler log hash mismatch')
spec=importlib.util.spec_from_file_location('audit',root/'verification_tools/verify_exp005.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
rows=audit.validate_axiom_log(log.decode(),set(inputs['expected_audits']))
require({k:sorted(v) for k,v in rows.items()}==result['axiom_audits'],'Compiler/report axiom disagreement')
require(sha(files['final_verification/DEPENDENCY_ARTIFACTS.json'])==result['dependency_manifest_sha256'],'Dependency manifest hash mismatch')
out=remote/'downloaded_evidence/exp008_independent_evidence';out.mkdir(parents=True,exist_ok=False)
for name,data in files.items():
    path=out/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
report={'passed':True,'archive_sha256':record['archive_sha256'],'evidence_files_checked':len(hashes),
        'audits_checked':len(rows),'source_sha256':inputs['source_sha256'],'result_sha256':sha(files['final_verification/RESULT.json']),
        'evidence_root':str(out),'qualification':'Transfer hashes and all independent audits agree with current local source; this script does not rerun Lean.'}
(remote/'FINAL_TRANSFER_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
