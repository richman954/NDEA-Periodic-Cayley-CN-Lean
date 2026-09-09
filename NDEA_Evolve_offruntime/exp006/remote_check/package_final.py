import datetime
import hashlib
import io
import json
from pathlib import Path
import tarfile

root=Path('/content/exp006_check')
result=json.loads((root/'final_verification/RESULT.json').read_text())
if result.get('passed') is not True:
    raise RuntimeError('Combined check has not passed')
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
paths=set()
for folder in [root,root/'final_verification',root/'convergence']:
    for p in folder.iterdir():
        if p.is_file() and not p.is_symlink() and p.suffix in {'.lean','.py','.json','.log','.png','.pdf','.svg'}:
            paths.add(p)
payload={str(p.relative_to(root)):p.read_bytes() for p in sorted(paths)}
manifest={'utc':stamp,'files':{n:hashlib.sha256(v).hexdigest() for n,v in payload.items()},
          'scope':'Independent proof sources, receipts, logs, dependency manifest, and numerical figures; build caches excluded.'}
payload['EVIDENCE_SHA256.json']=(json.dumps(manifest,indent=2)+'\n').encode()
archive=root/f'exp006_independent_evidence_{stamp}.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
    for name,data in sorted(payload.items()):
        member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644
        tar.addfile(member,io.BytesIO(data))
receipt={'archive':str(archive),'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
         'bytes':archive.stat().st_size,'files':len(payload),'proof_passed':True}
print(json.dumps(receipt))
