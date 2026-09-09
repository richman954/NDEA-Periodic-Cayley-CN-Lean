"""Verify bootstrap delivery and launch the independently downloaded environment."""
import hashlib,json,pathlib,subprocess,sys,tarfile
root=pathlib.Path('/content/exp013_check')
inp=root/'inputs'
archive=pathlib.Path('/content/exp013_bootstrap_inputs.tar.gz')
script=pathlib.Path('/content/exp013_bootstrap.py')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
EXPECTED_ARCHIVE_SHA256 = 'e51b3f8795280c259fcdd91942b2dc0a65484f1c19e38b20b5b1388e7b67c861'
EXPECTED_BOOTSTRAP_SHA256 = '65ab4ca0479546340a83744aac4694e1b23e95bb2df9351cbe7709e338692b68'
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
