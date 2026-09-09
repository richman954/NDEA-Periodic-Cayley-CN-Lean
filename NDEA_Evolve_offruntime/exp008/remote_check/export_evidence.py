"""Export independent source, compiler logs, and receipts after a successful check."""
from pathlib import Path
import datetime,hashlib,io,json,os,tarfile

root=Path('/content/exp008_check')
result=json.loads((root/'final_verification/RESULT.json').read_text())
inputs=json.loads((root/'final_source/evidence/FINAL_INPUTS.json').read_text())
if not result.get('passed') or result.get('exit_code')!=0:
    raise RuntimeError('Final combined verification has not passed')
if result['source_sha256_before']!=result['source_sha256_after'] or result['source_sha256_after']!=inputs['source_sha256']:
    raise RuntimeError('Final checked source mismatch')
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
payload={};allowed={'.py','.lean','.json','.log','.png','.pdf','.svg'}
for area in ['bootstrap','inputs','development','diagnostics','final_verification','final_source']:
    for cur,dirs,files in os.walk(root/area):
        dirs[:]=[d for d in dirs if d not in {'.git','.lake','dependencies','lib','cache_client','__pycache__'}]
        for name in files:
            p=Path(cur)/name
            if p.is_file() and not p.is_symlink() and p.suffix in allowed:
                payload[str(p.relative_to(root))]=p.read_bytes()
for p in root.iterdir():
    if p.is_file() and not p.is_symlink() and p.suffix in {'.py','.json','.log'} and p.name!='EXPORT_RECEIPT.json':
        payload[p.name]=p.read_bytes()
hashes={name:hashlib.sha256(data).hexdigest() for name,data in sorted(payload.items())}
manifest=(json.dumps(hashes,indent=2)+'\n').encode();payload['EVIDENCE_SHA256.json']=manifest
archive=root/('exp008_independent_evidence_'+stamp+'.tar.gz')
with tarfile.open(archive,'w:gz') as tar:
    for name,data in sorted(payload.items()):
        item=tarfile.TarInfo('exp008_independent_evidence/'+name);item.size=len(data);item.mode=0o644
        tar.addfile(item,io.BytesIO(data))
receipt={'passed':True,'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
         'archive_bytes':archive.stat().st_size,'files':len(hashes),'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
         'combined_sha256':inputs['source_sha256'],'stamp':stamp}
(root/'EXPORT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
