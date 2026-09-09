#!/usr/bin/env python3
import datetime, fcntl, hashlib, json, os, pathlib, subprocess, sys, time
root=pathlib.Path(__file__).resolve().parent
lean=pathlib.Path('/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean')
packages=pathlib.Path('/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages')
source=(root/sys.argv[1]).resolve()
name=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'_'+source.stem
log=root/'evidence'/f'{name}.log'
receipt=root/'evidence'/f'{name}.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
if sha(lean)!='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550':
    raise RuntimeError('Pinned Lean binary mismatch')
env=dict(os.environ)
env['LEAN_PATH']=':'.join([str(root/'build/lib/lean'),str(root.parent/'exp006/build/lib/lean')]+[str(p/'.lake/build/lib/lean') for p in packages.iterdir() if p.is_dir()]+[str(lean.parent.parent/'lib/lean')])
if source.stem=='Exp007Combined':
    env['LEAN_PATH']=str(root/'isolated_dependencies')+':'+str(lean.parent.parent/'lib/lean')
env['LEAN_NUM_THREADS']='1'
target=root/'build/lib/lean'/source.relative_to(root/'lean').with_suffix('.olean')
target.parent.mkdir(parents=True,exist_ok=True)
cmd=[str(lean),'-j','1','-R',str(root/'lean'),'-o',str(target),str(source)]
rec={'source':str(source),'source_sha256_before':sha(source),'lean_binary_sha256':sha(lean),'command':cmd,'lean_path':env['LEAN_PATH'],'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'runner_sha256':sha(pathlib.Path(__file__)),'mathlib_commit':subprocess.check_output(['git','-C',str(packages/'mathlib'),'rev-parse','HEAD'],text=True).strip()}
receipt.write_text(json.dumps(rec,indent=2)+'\n')
lock=open('/tmp/exp003_lean_one_job.lock','w')
fcntl.flock(lock,fcntl.LOCK_EX)
begin=time.monotonic()
try:
    with log.open('wb') as out: r=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
    rec['exit_code']=r.returncode
except subprocess.TimeoutExpired: rec['exit_code']=124
rec.update({'source_sha256_after':sha(source),'elapsed_seconds':time.monotonic()-begin,'log_sha256':sha(log),'log':str(log)})
rec['output_sha256']={str(target):sha(target)} if target.is_file() and rec['exit_code']==0 else {}
rec['sources_unchanged']=rec['source_sha256_before']==rec['source_sha256_after']
receipt.write_text(json.dumps(rec,indent=2)+'\n')
print(log.read_text()[-18000:])
print(json.dumps({'receipt':str(receipt),'exit_code':rec['exit_code'],'elapsed_seconds':rec['elapsed_seconds']}))
sys.exit(rec['exit_code'])
