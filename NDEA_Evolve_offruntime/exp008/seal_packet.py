"""Create and read back a review packet after the final qualification passes."""
from pathlib import Path
import datetime,hashlib,json,os,zipfile

root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)

inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
final=json.loads((root/'evidence/FINAL_VERIFICATION.json').read_text())
require(final.get('passed') is True, 'Final qualification has not passed')
require(final['source_sha256']==inputs['source_sha256']==sha(root/'lean/Exp008Combined.lean'),
        'Final combined source changed')
require(all(sha(root/name)==digest for name,digest in inputs['source_hashes'].items()),
        'A checked source changed')
upload=json.loads((root/'remote_check/FINAL_UPLOAD.json').read_text())
require(all(sha(root/name)==digest for name,digest in upload['files'].items()),
        'A checked verification input changed')
require(final['total_audits']==len(inputs['expected_audits'])==90, 'Audit count mismatch')
for prefix in ['local','independent']:
    p=root/final[prefix+'_result']
    require(sha(p)==final[prefix+'_result_sha256'], 'Final result changed: '+prefix)
    result=json.loads(p.read_text())
    require(sha(p.parent/'combined.log')==result['log_sha256'],
            'Accepted compiler log changed: '+prefix)
    require(sha(p.parent/'DEPENDENCY_ARTIFACTS.json')==result['dependency_manifest_sha256'],
            'Accepted library manifest changed: '+prefix)
require((root/'COMPLETION_REPORT.md').is_file(), 'Completion report missing')
require((root/'SAVED_FILES.md').is_file(), 'Saved-file guide missing')
allowed_areas={'lean','verification_tools','evidence','remote_check'}
excluded_dirs={'build','dependencies','__pycache__','.git','.lake','lib','cache_client'}
excluded_names={'PACKET_MANIFEST.json','FINAL_PACKET_RECEIPT.json'}
selected=[]
for current,dirs,names in os.walk(root):
    dirs[:]=sorted(d for d in dirs if d not in excluded_dirs)
    for name in sorted(names):
        path=Path(current)/name;rel=path.relative_to(root)
        if not path.is_file() or path.is_symlink() or name in excluded_names:continue
        if len(rel.parts)==1:
            if path.suffix not in {'.md','.py'}:continue
        elif rel.parts[0] not in allowed_areas:continue
        require(path.suffix not in {'.olean','.ilean','.ir','.o','.so','.pyc'},
                'Unexpected build artifact: '+str(rel))
        selected.append(path)
hashes={str(p.relative_to(root)):sha(p) for p in sorted(selected)}
manifest=root/'PACKET_MANIFEST.json'
require(not manifest.exists(), 'Packet manifest already exists; preserve the sealed packet')
packet_name='Exp008_Verified_Review_Packet_20260908'
archive=root.parent.parent/(packet_name+'.zip')
require(not archive.exists() and not archive.with_suffix('.zip.sha256').exists() and
        not (root/'evidence/FINAL_PACKET_RECEIPT.json').exists(), 'Packet output already exists')
manifest_bytes=(json.dumps(hashes,indent=2)+'\n').encode()
manifest_digest=hashlib.sha256(manifest_bytes).hexdigest()
manifest.write_bytes(manifest_bytes)
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(selected)+[manifest]:z.write(p,packet_name+'/'+str(p.relative_to(root)))
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None,'Archive CRC check failed')
    require(set(z.namelist())=={packet_name+'/'+k for k in hashes}|{packet_name+'/PACKET_MANIFEST.json'},
            'Archive member coverage mismatch')
    require(z.read(packet_name+'/PACKET_MANIFEST.json')==manifest_bytes,'Packaged manifest bytes changed')
    for name,digest in hashes.items():
        require(hashlib.sha256(z.read(packet_name+'/'+name)).hexdigest()==digest,
                'Packaged file hash mismatch: '+name)
require(all(sha(root/name)==digest for name,digest in hashes.items()),'Input changed during packaging')
require(sha(manifest)==manifest_digest,'Manifest changed during packaging')
receipt={'passed':True,'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'archive':str(archive),'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,
         'manifest_entries':len(hashes),'manifest_sha256':manifest_digest,'verified_file_count':len(hashes)+1,
         'qualification':'Every packaged file hash and archive CRC checked after writing. The packet receipt and archive checksum are external to avoid a self-hash cycle.'}
(root/'evidence/FINAL_PACKET_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
archive.with_suffix('.zip.sha256').write_text(receipt['archive_sha256']+'  '+archive.name+'\n')
print(json.dumps(receipt,indent=2))
