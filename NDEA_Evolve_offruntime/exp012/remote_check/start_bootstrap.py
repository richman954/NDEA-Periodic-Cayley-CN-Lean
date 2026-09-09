"""Verify bootstrap delivery and launch the independently downloaded environment."""
import hashlib,json,pathlib,subprocess,sys,tarfile
root=pathlib.Path('/content/exp012_check')
inp=root/'inputs'
archive=pathlib.Path('/content/exp012_bootstrap_inputs.tar.gz')
script=pathlib.Path('/content/exp012_bootstrap.py')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
EXPECTED_ARCHIVE_SHA256 = '9dbc649fb7199a3973d8ca9e7e0d1ca7a8200fdd8c68cdb16d8e1a751f4f9b60'
EXPECTED_BOOTSTRAP_SHA256 = '4b93106dd42b647a0f0c1f41328718072141cd1fd153dcb171b26bc866d87ec5'
if 'UNPREPARED' in {EXPECTED_ARCHIVE_SHA256,EXPECTED_BOOTSTRAP_SHA256}:
    raise RuntimeError('Run prepare_bootstrap_inputs.py before launching')
if sha(archive)!=EXPECTED_ARCHIVE_SHA256 or sha(script)!=EXPECTED_BOOTSTRAP_SHA256:
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
