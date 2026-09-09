"""Verify bootstrap delivery and launch the independently downloaded environment."""
import hashlib,json,pathlib,subprocess,sys,tarfile
root=pathlib.Path('/content/exp009_check')
inp=root/'inputs'
archive=pathlib.Path('/content/exp009_bootstrap_inputs.tar.gz')
script=pathlib.Path('/content/exp009_bootstrap.py')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sha(archive)!='7907f0667815b639fc2e2bc8beec4512ee57e419c107e4ff7642531cd4362864' or sha(script)!='b381aea1cad921a426a8c62c8675aa11562d2c1f0c4dbf9c17544a0eb940694a':
    raise RuntimeError('Bootstrap delivery pin mismatch')
files={}
with tarfile.open(archive) as tar:
    for item in tar.getmembers():
        if not item.isfile() or '/' in item.name or item.name in {'.','..'} or item.name in files:
            raise RuntimeError('Unsafe or duplicate bootstrap member')
        files[item.name]=tar.extractfile(item).read()
manifest=json.loads(files['INPUT_HASHES.json'])
if set(files)!=(set(manifest)|{'INPUT_HASHES.json'}):raise RuntimeError('Input coverage mismatch')
if any(hashlib.sha256(files[k]).hexdigest()!=v for k,v in manifest.items()):
    raise RuntimeError('Bootstrap input hash mismatch')
inp.mkdir(exist_ok=False)
for name,data in files.items():(inp/name).write_bytes(data)
command=[sys.executable,'-u','-B',str(script)]
with (root/'bootstrap_controller.log').open('xb') as log:
    p=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,
        stdin=subprocess.DEVNULL,start_new_session=True)
receipt={'pid':p.pid,'root':str(root),'command':command,
    'archive_sha256':sha(archive),'bootstrap_sha256':sha(script),'input_hashes':manifest}
(root/'BOOTSTRAP_LAUNCH.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
