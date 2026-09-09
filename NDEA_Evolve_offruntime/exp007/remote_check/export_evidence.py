import pathlib,json,hashlib,tarfile,datetime,shutil
r=pathlib.Path('/content/exp007_check')
result=json.loads((r/'final_verification/RESULT.json').read_text())
assert result['passed'] and result['source_sha256_before']=='cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out=r/('export_'+stamp);out.mkdir()
for area in ['bootstrap','development','diagnostics','final_verification','final_source']:
 for src in (r/area).rglob('*'):
  rel=src.relative_to(r)
  if not src.is_file() or 'dependencies' in rel.parts or 'cache_client' in rel.parts:continue
  if src.suffix not in ['.py','.lean','.json','.log','.png','.pdf','.svg']:continue
  dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
for name in ['FINAL_LAUNCH.json','final_controller.log','bootstrap_controller.log']:
 shutil.copyfile(r/name,out/name)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
hashes={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
(out/'EVIDENCE_SHA256.json').write_text(json.dumps(hashes,indent=2)+'\n')
archive=r/('exp007_independent_evidence_'+stamp+'.tar.gz')
with tarfile.open(archive,'w:gz') as tar:
 for p in sorted(out.rglob('*')):
  if p.is_file():tar.add(p,arcname='exp007_independent_evidence/'+str(p.relative_to(out)))
receipt={'archive':str(archive),'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,'files':len(hashes),'manifest_sha256':sha(out/'EVIDENCE_SHA256.json'),'passed':True,'stamp':stamp}
(r/'EXPORT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
