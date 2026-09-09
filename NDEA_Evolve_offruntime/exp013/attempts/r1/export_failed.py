from pathlib import Path
import hashlib,io,json,tarfile
root=Path('/content/exp013_check')
result=json.loads((root/'final_verification/RESULT.json').read_text())
assert result.get('passed') is False and result.get('exit_code')==1 and result.get('end_utc')
paths=[p for folder in ['final_verification','bootstrap','inputs','final_source'] for p in (root/folder).rglob('*') if p.is_file() and not any(x in p.parts for x in ['dependencies','cache_client'])]
paths += [p for p in root.iterdir() if p.is_file() and p.suffix in {'.json','.log'}]
payload={str(p.relative_to(root)):p.read_bytes() for p in sorted(set(paths))}
manifest={n:hashlib.sha256(b).hexdigest() for n,b in payload.items()}
payload['FAILED_MANIFEST.json']=(json.dumps(manifest,indent=2)+'\n').encode()
a=root/'exp013_failed_attempt1.tar.gz'
with tarfile.open(a,'x:gz') as tar:
 for n,b in payload.items():
  m=tarfile.TarInfo(n);m.size=len(b);tar.addfile(m,io.BytesIO(b))
print(json.dumps({'archive':str(a),'sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'payload_files':len(manifest),'bytes':a.stat().st_size,'proof_passed':False}))
