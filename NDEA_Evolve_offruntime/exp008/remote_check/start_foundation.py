"""Launch the source-only foundation compile in the independent environment."""
import json,subprocess,sys
from pathlib import Path
root=Path('/content/exp008_check')
code=r'''
import datetime,hashlib,json,os,subprocess,time
from pathlib import Path
root=Path('/content/exp008_check');base=Path('/content/exp008_check')
source=root/'development/lean/Exp007Foundation.lean'
lean=base/'lean-4.31.0-linux/bin/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected='cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c'
assert sha(source)==expected
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=':'.join([str(base/'mathlib/.lake/build/lib/lean')]+[str(p/'.lake/build/lib/lean') for p in (base/'mathlib/.lake/packages').iterdir() if p.is_dir()]+[str(lean.parent.parent/'lib/lean')]))
env.pop('LEAN_SRC_PATH',None)
command=[str(lean),'-j','1','-R',str(source.parent),'-o',str(root/'development/lib/Exp007Foundation.olean'),str(source)]
record={'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':command,'source_sha256_before':sha(source),'compiler_sha256':sha(lean),'lean_path':env['LEAN_PATH']}
begin=time.monotonic()
with (root/'development/evidence/foundation.log').open('xb') as log:
    r=subprocess.run(command,env=env,cwd=root,stdout=log,stderr=subprocess.STDOUT,timeout=900)
record.update(exit_code=r.returncode,elapsed_seconds=time.monotonic()-begin,source_sha256_after=sha(source),log_sha256=sha(root/'development/evidence/foundation.log'))
record['passed']=r.returncode==0 and record['source_sha256_before']==record['source_sha256_after']
(root/'development/evidence/FOUNDATION_RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''
job=root/'compile_foundation.py';job.write_text(code)
with (root/'foundation_controller.log').open('xb') as log:
    p=subprocess.Popen([sys.executable,'-u','-B',str(job)],stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print(json.dumps({'pid':p.pid,'root':str(root)}))
