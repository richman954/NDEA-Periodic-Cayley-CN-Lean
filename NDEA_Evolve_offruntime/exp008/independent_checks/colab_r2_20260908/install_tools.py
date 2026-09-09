"""Preserve the exact launch/check tools in the new runtime."""
from pathlib import Path,PurePosixPath
import hashlib,json,tarfile
root=Path('/content/exp008_check')
request=json.loads((root/'TOOLS_UPLOAD.json').read_text());archive=Path(request['archive'])
if hashlib.sha256(archive.read_bytes()).hexdigest()!=request['sha256']:raise RuntimeError('Tool archive mismatch')
files={}
with tarfile.open(archive) as tar:
    for item in tar.getmembers():
        p=PurePosixPath(item.name)
        if not item.isfile() or len(p.parts)!=1 or item.name in files or p.suffix!='.py':
            raise RuntimeError('Unsafe tool archive member')
        files[item.name]=tar.extractfile(item).read()
if {n:hashlib.sha256(v).hexdigest() for n,v in files.items()}!=request['files']:
    raise RuntimeError('Tool input hashes differ')
for name,data in files.items():
    p=root/name
    if p.exists():
        if p.read_bytes()!=data:raise RuntimeError('Existing tool differs: '+name)
    else:p.write_bytes(data)
(root/'TOOLS_INSTALL.json').write_text(json.dumps({'passed':True,**request},indent=2)+'\n')
print(json.dumps({'passed':True,'files':len(files)}))
