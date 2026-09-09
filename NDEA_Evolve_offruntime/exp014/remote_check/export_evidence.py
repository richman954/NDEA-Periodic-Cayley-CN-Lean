"""Export accepted independent source, inputs and logs; omit build caches."""
import datetime, hashlib, io, json, tarfile
from pathlib import Path

root=Path('/content/exp014_check')
result=json.loads((root/'final_verification/RESULT.json').read_text())
if result.get('passed') is not True or result.get('exit_code')!=0:
    raise RuntimeError('Independent combined check has not passed')
paths=[root/n for n in ['ENVIRONMENT.json','FINAL_UPLOAD.json','FINAL_LAUNCH.json',
    'BOOTSTRAP_LAUNCH.json','bootstrap_controller.log','bootstrap/RESULT.json',
    'final_controller.log','final_verification/RESULT.json',
    'final_verification/combined.log','final_verification/dependency_copy.log',
    'final_verification/DEPENDENCY_ARTIFACTS.json']]
paths+=sorted(p for p in (root/'final_source').rglob('*') if p.is_file())
paths+=sorted(p for p in (root/'inputs').iterdir() if p.is_file())
paths+=sorted((root/'bootstrap').glob('*.log'))
payload={str(p.relative_to(root)):p.read_bytes() for p in paths}
payload['bootstrap_tools/bootstrap.py']=Path('/content/exp014_bootstrap.py').read_bytes()
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
manifest={n:hashlib.sha256(data).hexdigest() for n,data in payload.items()}
payload['EVIDENCE_SHA256.json']=(json.dumps(manifest,indent=2)+'\n').encode()
archive=root/f'exp014_independent_evidence_{stamp}.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
    for name,data in sorted(payload.items()):
        item=tarfile.TarInfo(name);item.size=len(data);item.mode=0o644
        tar.addfile(item,io.BytesIO(data))
receipt={'archive':str(archive),'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
    'bytes':archive.stat().st_size,'payload_files':len(manifest),'passed':True}
(root/'EXPORT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
