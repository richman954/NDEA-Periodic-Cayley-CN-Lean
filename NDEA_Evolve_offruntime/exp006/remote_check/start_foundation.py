import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path('/content/exp006_check')
root.mkdir(exist_ok=True)
source = root / 'Exp005Foundation.lean'
data = Path('/content/Exp005Foundation.lean').read_bytes()
if hashlib.sha256(data).hexdigest() != '40386d3848f338f4ea89869a39a920e127674f5a42a471dfbd969901599a8785':
    raise RuntimeError('Foundation snapshot mismatch')
source.write_bytes(data)
code = r'''
import datetime,hashlib,json,os,pathlib,subprocess,tarfile,time
root=pathlib.Path('/content/exp006_check')
base=pathlib.Path('/content/exp005_independent_check')
lean=base/'lean-4.31.0-linux/bin/lean'
lib=root/'build/lib/lean';lib.mkdir(parents=True,exist_ok=True)
packages=[base/'mathlib']+[p for p in (base/'mathlib/.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ,LEAN_NUM_THREADS='1')
env['LEAN_PATH']=os.pathsep.join(map(str,[lib]+[p/'.lake/build/lib/lean' for p in packages]+[lean.parent.parent/'lib/lean']))
source=root/'Exp005Foundation.lean';target=lib/'Exp005Foundation.olean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record={'source_sha256_before':sha(source),'compiler_sha256':sha(lean),'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
command=[str(lean),'-j','1','-R',str(root),'-o',str(target),str(source)]
record['command']=command
record['lean_path']=env['LEAN_PATH']
begin=time.monotonic()
try:
    with (root/'foundation.log').open('xb') as log:
        p=subprocess.run(command,env=env,cwd=root,stdout=log,stderr=subprocess.STDOUT,timeout=900)
    record['exit_code']=p.returncode
except subprocess.TimeoutExpired:
    record['exit_code']=124
record.update(source_sha256_after=sha(source),elapsed_seconds=time.monotonic()-begin,log_sha256=sha(root/'foundation.log'))
record['passed']=record['exit_code']==0 and record['source_sha256_before']==record['source_sha256_after']
record['artifacts']={str(p.relative_to(root)):sha(p) for p in lib.glob('Exp005Foundation.*')} if record['passed'] else {}
(root/'FOUNDATION_RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
archive=root/'foundation_artifacts.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
    for p in [source,root/'foundation.log',root/'FOUNDATION_RESULT.json']+list(lib.glob('Exp005Foundation.*')):
        tar.add(p,arcname=str(p.relative_to(root)),recursive=False)
receipt={'archive':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size,'passed':record['passed']}
(root/'FOUNDATION_DELIVERY.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
'''
job = root / 'compile_foundation.py'
job.write_text(code)
with (root / 'foundation_controller.log').open('xb') as log:
    p = subprocess.Popen([sys.executable, '-u', '-B', str(job)], stdout=log,
                         stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
print(json.dumps({'pid':p.pid,'root':str(root),'source_sha256':hashlib.sha256(data).hexdigest()}))
