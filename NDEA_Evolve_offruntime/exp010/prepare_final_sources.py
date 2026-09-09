"""Package exact final-check inputs after the combined source is generated."""
from pathlib import Path
import hashlib,importlib.util,io,json,tarfile

root=Path(__file__).resolve().parent
inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('exp010_final_source_generator',root/'make_combined.py')
generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
rebuilt,reconstructed=generator.build(root)
if reconstructed!=inputs or rebuilt!=(root/'lean/Exp010Combined.lean').read_text():
    raise RuntimeError('Combined source/catalog reconstruction differs')
for name,digest in inputs['source_hashes'].items():
    if sha(root/name)!=digest:raise RuntimeError('Changed source: '+name)
paths=set(inputs['source_hashes'])|{'lean/Exp010Combined.lean','evidence/FINAL_INPUTS.json',
      'make_combined.py','verify_combined.py','remote_check/bootstrap_inputs/lake-manifest.json',
      'verification_tools/verify_exp005.py','verification_tools/lean_import_closure.py'}
payload={name:(root/name).read_bytes() for name in sorted(paths)}
manifest={name:hashlib.sha256(data).hexdigest() for name,data in payload.items()}
payload['FINAL_TRANSFER_INPUTS.json']=(json.dumps(manifest,indent=2)+'\n').encode()
destination=root/'remote_check'/('final_sources_'+inputs['source_sha256'][:16]+'.tar.gz')
if destination.exists():raise RuntimeError('Final source archive already exists; preserve it and use its receipt')
with tarfile.open(destination,'w:gz') as tar:
    for name,data in payload.items():
        item=tarfile.TarInfo(name);item.size=len(data);item.mode=0o644
        tar.addfile(item,io.BytesIO(data))
with tarfile.open(destination) as tar:
    members=tar.getmembers()
    if len(members)!=len(payload) or {m.name for m in members}!=set(payload):
        raise RuntimeError('Final source archive coverage differs')
    if any(not m.isfile() or tar.extractfile(m).read()!=payload[m.name] for m in members):
        raise RuntimeError('Final source archive readback differs')
request={'archive':'/content/exp010_check/'+destination.name,'sha256':sha(destination),
         'combined_sha256':inputs['source_sha256'],'files':manifest,'local_archive':str(destination)}
(root/'remote_check/FINAL_UPLOAD.json').write_text(json.dumps(request,indent=2)+'\n')
print(json.dumps({'archive':str(destination),'sha256':request['sha256'],'payload_files':len(payload)}))
