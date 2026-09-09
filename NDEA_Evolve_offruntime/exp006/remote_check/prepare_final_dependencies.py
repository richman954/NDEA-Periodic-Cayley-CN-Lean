import json
from pathlib import Path
import subprocess
import sys

root=Path('/content/exp006_check')
code=r'''
import datetime,hashlib,json,os,pathlib,subprocess,time
root=pathlib.Path('/content/exp006_check')
base=pathlib.Path('/content/exp005_independent_check')
lean=base/'lean-4.31.0-linux/bin/lean'
mathlib=base/'mathlib'
packages=[mathlib]+[p for p in (mathlib/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ,LEAN_NUM_THREADS='1')
env['LEAN_PATH']=str(base/'evidence/20260908T044513/cache_client/lib/lean')+':'+str(lean.parent.parent/'lib/lean')
env['LEAN_SRC_PATH']=':'.join(map(str,packages))
env['PATH']=str(lean.parent)+':'+env['PATH']
modules=['Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds','Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv',
         'Mathlib.Analysis.InnerProductSpace.PiL2','Mathlib.LinearAlgebra.Matrix.Permutation',
         'Mathlib.Logic.Equiv.Fin.Rotate','Mathlib.Algebra.Ring.Periodic','Mathlib.Tactic.Abel']
command=[str(lean),'-j','1','--run',str(mathlib/'Cache/Main.lean'),'get',*modules]
begin=time.monotonic()
with (root/'additional_dependencies.log').open('xb') as log:
    p=subprocess.run(command,cwd=mathlib,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=900)
record={'modules':modules,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-begin,
        'command':command,'log_sha256':hashlib.sha256((root/'additional_dependencies.log').read_bytes()).hexdigest()}
(root/'ADDITIONAL_DEPENDENCIES.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''
job=root/'prepare_additional_dependencies.py'
job.write_text(code)
with (root/'dependencies_controller.log').open('xb') as log:
    p=subprocess.Popen([sys.executable,'-u','-B',str(job)],cwd=root,stdout=log,
                       stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
print(json.dumps({'pid':p.pid,'root':str(root)}))
