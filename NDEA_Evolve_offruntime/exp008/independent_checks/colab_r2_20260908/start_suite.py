"""Restore pinned suite sources and start their independent verification."""
from pathlib import Path,PurePosixPath
import hashlib,json,subprocess,sys,tarfile
root=Path('/content/exp008_check');source=root/'historical_source'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
request=json.loads((root/'SUITE_UPLOAD.json').read_text());archive=Path(request['archive'])
if sha(archive)!=request['sha256']:raise RuntimeError('Historical archive pin mismatch')
if sha(root/'verify_suite.py')!=request['runner_sha256']:raise RuntimeError('Historical runner pin mismatch')
files={}
with tarfile.open(archive) as tar:
    for member in tar.getmembers():
        p=PurePosixPath(member.name)
        if not member.isfile() or p.is_absolute() or '..' in p.parts or str(p)!=member.name or member.name in files:
            raise RuntimeError('Unsafe or duplicate suite archive member')
        files[member.name]=tar.extractfile(member).read()
if {n:hashlib.sha256(v).hexdigest() for n,v in files.items()}!=request['files']:
    raise RuntimeError('Historical payload identity mismatch')
source.mkdir(exist_ok=False)
for name,data in files.items():
    p=source/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
command=[sys.executable,'-u','-B',str(root/'verify_suite.py')]
with (root/'historical_controller.log').open('xb') as log:
    process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
record={'pid':process.pid,'command':command,'source_archive_sha256':sha(archive),
        'runner_sha256':sha(root/'verify_suite.py'),'inputs_sha256':sha(source/'SUITE_INPUTS.json')}
(root/'HISTORICAL_LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
