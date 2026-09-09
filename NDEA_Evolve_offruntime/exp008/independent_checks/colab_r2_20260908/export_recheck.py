"""Export fresh-VM source, successful checks, and expected rejection evidence."""
from pathlib import Path
import datetime,hashlib,io,json,os,tarfile
root=Path('/content/exp008_check')
for name in ['bootstrap/RESULT.json','final_verification/RESULT.json','historical_verification/RESULT.json']:
    if json.loads((root/name).read_text()).get('passed') is not True:
        raise RuntimeError('Required check has not passed: '+name)
files={}
for area in ['bootstrap','inputs','final_source','final_verification','historical_source','historical_verification']:
    for current,dirs,names in os.walk(root/area):
        dirs[:]=[d for d in dirs if d not in {'dependencies','cache_client','.git','.lake','__pycache__','lib'}]
        for name in names:
            p=Path(current)/name
            if p.is_file() and not p.is_symlink():
                files[str(p.relative_to(root))]=p.read_bytes()
for p in root.iterdir():
    if p.is_file() and not p.is_symlink() and p.suffix in {'.py','.json','.log'} and p.name!='EXPORT_RECEIPT.json':
        files[p.name]=p.read_bytes()
# This was the independently executed bootstrap path, outside the check root.
files['bootstrap.py']=Path('/content/exp008_bootstrap.py').read_bytes()
manifest={n:hashlib.sha256(v).hexdigest() for n,v in sorted(files.items())}
manifest_bytes=(json.dumps(manifest,indent=2)+'\n').encode()
files['EVIDENCE_SHA256.json']=manifest_bytes
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
archive=root/('exp001_008_fresh_vm_recheck_'+stamp+'.tar.gz')
with tarfile.open(archive,'x:gz') as tar:
    for name,data in sorted(files.items()):
        item=tarfile.TarInfo('recheck_evidence/'+name);item.size=len(data);item.mode=0o644
        tar.addfile(item,io.BytesIO(data))
record={'passed':True,'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
        'archive_bytes':archive.stat().st_size,'files':len(manifest),
        'manifest_sha256':hashlib.sha256(manifest_bytes).hexdigest(),'stamp':stamp}
(root/'EXPORT_RECEIPT.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
