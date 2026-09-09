"""Validate the independent evidence transfer, source identity, and all audits."""
import hashlib,importlib.util,json,shutil,tarfile
from pathlib import Path
r=Path(__file__).resolve().parent;root=r.parent
rec=json.loads((r/'EXPORT_RECEIPT.json').read_text())
archive=r/Path(rec['archive']).name
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(archive)==rec['archive_sha256']
out=r/'downloaded_evidence';out.mkdir(exist_ok=False)
with tarfile.open(archive) as tar:
 seen=set()
 for m in tar.getmembers():
  p=Path(m.name)
  assert m.isfile() and not p.is_absolute() and '..' not in p.parts and p.parts[0]=='exp007_independent_evidence'
  assert m.name not in seen
  seen.add(m.name)
  target=out/p
  assert target.resolve().is_relative_to(out.resolve())
  target.parent.mkdir(parents=True,exist_ok=True)
  with tar.extractfile(m) as incoming,target.open('xb') as outgoing:
   shutil.copyfileobj(incoming,outgoing)
evidence=out/'exp007_independent_evidence'
manifest=evidence/'EVIDENCE_SHA256.json'
assert sha(manifest)==rec['manifest_sha256']
hashes=json.loads(manifest.read_text())
assert len(hashes)==rec['files'] and all(sha(evidence/k)==v for k,v in hashes.items())
assert {str(p.relative_to(evidence)) for p in evidence.rglob('*') if p.is_file()}==set(hashes)|{'EVIDENCE_SHA256.json'}
inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
result=json.loads((evidence/'final_verification/RESULT.json').read_text())
assert result['passed'] and result['exit_code']==0 and result['reconstruction_verified']
assert result['source_sha256_before']==result['source_sha256_after']==inputs['source_sha256']
assert result['source_hashes']==inputs['source_hashes']
assert sha(evidence/'final_source/lean/Exp007Combined.lean')==inputs['source_sha256']
assert sha(evidence/'final_verification/combined.log')==result['log_sha256']
spec=importlib.util.spec_from_file_location('audit',root/'verification_tools/verify_exp005.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
rows=audit.validate_axiom_log((evidence/'final_verification/combined.log').read_text(),set(inputs['expected_audits']))
assert {k:sorted(v) for k,v in rows.items()}==result['axiom_audits']
report={'passed':True,'archive_sha256':sha(archive),'evidence_files_checked':len(hashes),'audits_checked':len(rows),'source_sha256':inputs['source_sha256'],'result_sha256':sha(evidence/'final_verification/RESULT.json'),'evidence_root':str(evidence),'qualification':'Archive/file hashes and all independent axioms agree with current local source.'}
(r/'FINAL_TRANSFER_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
