"""Start an independent combined check from the exact uploaded source archive."""
from pathlib import Path,PurePosixPath
import hashlib,io,json,subprocess,sys,tarfile
root=Path('/content/exp010_check');base=Path('/content/exp010_check');source=root/'final_source'
request=json.loads((root/'FINAL_UPLOAD.json').read_text())
bootstrap=json.loads((root/'bootstrap/RESULT.json').read_text())
if bootstrap.get('passed') is not True or bootstrap.get('input_hashes',{}).get('Combined.lean')!=request['combined_sha256']:
    raise RuntimeError('Exact final-source dependency bootstrap has not passed')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
archive=Path(request['archive'])
if sha(archive)!=request['sha256']:raise RuntimeError('Final source archive mismatch')
files={}
with tarfile.open(archive) as tar:
    for item in tar.getmembers():
        p=PurePosixPath(item.name)
        if not item.isfile() or p.is_absolute() or '..' in p.parts or str(p)!=item.name or item.name in files:
            raise RuntimeError('Unsafe or duplicate archive member')
        files[item.name]=tar.extractfile(item).read()
manifest=json.loads(files['FINAL_TRANSFER_INPUTS.json'])
if manifest!=request['files'] or set(manifest)!=set(files)-{'FINAL_TRANSFER_INPUTS.json'}:
    raise RuntimeError('Transfer manifest coverage mismatch')
if any(hashlib.sha256(files[k]).hexdigest()!=v for k,v in manifest.items()):
    raise RuntimeError('Transferred file mismatch')
source.mkdir(exist_ok=False)
for name,data in files.items():
    p=source/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
cmd=[sys.executable,'-u','-B',str(source/'verify_combined.py'),'--root',str(source),
     '--lean',str(base/'lean-4.31.0-linux/bin/lean'),'--mathlib',str(base/'mathlib'),
     '--other-packages',str(base/'mathlib/.lake/packages'),'--output',str(root/'final_verification')]
with (root/'final_controller.log').open('xb') as log:
    p=subprocess.Popen(cmd,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
receipt={'pid':p.pid,'command':cmd,'source_archive_sha256':sha(archive),
         'runner_sha256':sha(source/'verify_combined.py'),'combined_sha256':request['combined_sha256']}
(root/'FINAL_LAUNCH.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
