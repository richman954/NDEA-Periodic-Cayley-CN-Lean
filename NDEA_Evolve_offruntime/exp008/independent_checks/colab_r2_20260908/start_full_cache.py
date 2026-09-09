"""Fetch the complete pinned Mathlib cache for exact historical imports."""
from pathlib import Path
import json,subprocess,sys
root=Path('/content/exp008_check')
code=r'''
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
root=Path('/content/exp008_check');mathlib=root/'mathlib';lean=root/'lean-4.31.0-linux/bin/lean'
packages=[mathlib]+[p for p in (mathlib/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ,LEAN_NUM_THREADS='1')
env['LEAN_PATH']=str(root/'bootstrap/cache_client/lib/lean')+':'+str(lean.parent.parent/'lib/lean')
env['LEAN_SRC_PATH']=':'.join(map(str,packages))
env['PATH']=str(lean.parent)+':'+env['PATH']
modules=['Mathlib']
command=[str(lean),'-j','1','--run',str(mathlib/'Cache/Main.lean'),'get',*modules]
begin=time.monotonic()
with (root/'extra_imports.log').open('xb') as log:
    result=subprocess.run(command,cwd=mathlib,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=900)
record={'exit_code':result.returncode,'modules':modules,'command':command,'elapsed_seconds':time.monotonic()-begin,
        'log_sha256':hashlib.sha256((root/'extra_imports.log').read_bytes()).hexdigest(),
        'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(root/'EXTRA_IMPORTS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''
job=root/'fetch_extra_imports.py';job.write_text(code)
with (root/'extra_imports_controller.log').open('xb') as log:
    p=subprocess.Popen([sys.executable,'-u','-B',str(job)],stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print(json.dumps({'pid':p.pid}))
