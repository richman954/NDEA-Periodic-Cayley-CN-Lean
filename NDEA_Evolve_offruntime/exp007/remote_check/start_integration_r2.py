import pathlib,tarfile,subprocess,sys,json
root=pathlib.Path('/content/exp007_check');dev=root/'development'
with tarfile.open('/content/exp007_integration_r2_sources.tar.gz') as tar:
 for m in tar.getmembers():assert m.isfile() and '/' not in m.name and m.name.endswith('.lean')
 tar.extractall(dev,filter='data')
code="""import pathlib,subprocess,os,time,json,hashlib
r=pathlib.Path('/content/exp007_check');dev=r/'development';lean=r/'lean-4.31.0-linux/bin/lean'
libs=[dev,r/'mathlib/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (r/'mathlib/.lake/packages').iterdir() if p.is_dir()]+[lean.parent.parent/'lib/lean']
env=dict(os.environ,LEAN_PATH=':'.join(map(str,libs)),LEAN_NUM_THREADS='1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['FullClosure','StageBridge','Controls']:
 s=dev/(name+'.lean');begin=time.monotonic();before=sha(s)
 with (dev/('integration_r2_'+name+'.log')).open('wb') as log:
  p=subprocess.run([str(lean),'-j','1','-R',str(dev),'-o',str(dev/(name+'.olean')),str(s)],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
 rec={'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-begin,'source_sha256_before':before,'source_sha256_after':sha(s),'log_sha256':sha(dev/('integration_r2_'+name+'.log'))}
 (dev/('integration_r2_'+name+'_RESULT.json')).write_text(json.dumps(rec,indent=2))
 print(name,json.dumps(rec),flush=True)
 if p.returncode:break
"""
(dev/'check_integration.py').write_text(code)
with (dev/'integration_r2_controller.log').open('wb') as log:
 p=subprocess.Popen([sys.executable,'-u','-B',str(dev/'check_integration.py')],stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
print(json.dumps({'pid':p.pid}))
